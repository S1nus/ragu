//! Mid-stream witness cheating fuzz target.
//!
//! Runs the same instruction stream twice through the `Simulator`: an
//! honest path and a cheat path that, at a fuzzer-chosen point, replaces
//! one element on the stack with a fresh allocation whose value differs
//! from the honest one. After both runs complete, the final element and
//! boolean values are compared.
//!
//! The op grammar, byte decoding, and gadget dispatch live in
//! [`ragu_testing_fuzz::substrate`]; the cheat is injected through the
//! substrate's pre-op synthesis hook. This harness owns the cheat
//! machinery, the dead-cheat triage, and the fingerprint comparison.
//!
//! # Current effective behavior
//!
//! As implemented, this target functions primarily as a Simulator
//! robustness fuzzer rather than a soundness oracle. The cheated slot is
//! included in the comparison fingerprint, and the cheat value is filtered
//! to differ from the original, so `honest != cheat` is tautologically
//! true regardless of whether downstream constraints actually catch the
//! cheat. The signals the target reliably surfaces today are panics, OOB
//! indexing, and arithmetic faults in the gadget API when fed adversarial
//! inputs — not under-constrained gadgets.
//!
//! # The constraint-side oracles live elsewhere
//!
//! The originally planned "patcher" pass cannot turn this target into an
//! under-constrained-gadget oracle: every downstream gadget recomputes
//! honestly from the cheated value, so gates self-satisfy by construction
//! and the constraint matrix is never consulted — Simulator-side
//! perturbation, with or without a patcher, observes only witness
//! generation. The true oracles are `fuzz_witness_pinning` (single-wire
//! trace-coefficient mutation against the revdot identity),
//! `fuzz_circuit_cheat` (input mutation against the assembled constraint
//! identity), and `fuzz_advice_patcher` (advice mutation repaired through
//! the captured constraint graph). This target remains in the rotation for
//! what it demonstrably catches: panics, OOB indexing, and arithmetic
//! faults in the gadget API under adversarial mid-stream value
//! substitution.

#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_core::{Error, drivers::Driver, maybe::Maybe};
use ragu_primitives::{Element, Simulator, allocator::Standard};
use ragu_testing_fuzz::substrate::{
    Capabilities, Limits, Op, OpKind, OpSet, Preamble, Program, special_value, synthesize_with_hook,
};

/// How the cheat replaces an element.
#[derive(Arbitrary, Debug, Clone, Copy)]
enum CheatFlavor {
    /// Fresh witness allocation with an arbitrary value. Severs all
    /// constraint history of the previous occupant of this slot.
    Alloc(u64),
    /// Replace with a constant. Severs constraint history and locks the
    /// new value into a constant path.
    Constant(u64),
    /// Fresh witness allocation with a special field value (0, 1, p-1,
    /// roots of unity, generators, …).
    Special(u8),
}

#[derive(Arbitrary, Debug)]
struct Input {
    /// Index into the decoded ops at which to apply the cheat. The cheat
    /// replaces `elems[target_idx]` *before* `ops[cheat_at]` is executed.
    cheat_at: u16,
    /// Index (mod current stack length) of the slot to replace.
    target_idx: u8,
    cheat: CheatFlavor,
    /// Raw program bytes, decoded via [`Program::decode`]. Last field, so
    /// `arbitrary_take_rest` hands it the remainder of the input.
    program: Vec<u8>,
}

/// The historical 19-op robustness vocabulary: everything except `Anchor`.
fn opset() -> OpSet {
    OpSet::ALL.without(Capabilities::ANCHORS)
}

/// Final-state fingerprint: every element's value followed by every
/// boolean's value, in stack order.
type Fingerprint = (Vec<Fp>, Vec<bool>);

/// Execute the program (with or without the cheat) and return the final
/// fingerprint if the Simulator accepted.
///
/// Returns `None` if the simulator rejected, or if `apply_cheat` was true
/// but the chosen cheat value coincided with the slot's existing value
/// (a degenerate input that would produce a false-positive fingerprint
/// match) — the hook aborts that run with an error.
fn run_path(program: &Program, input: &Input, apply_cheat: bool) -> Option<Fingerprint> {
    let mut snapshot: Option<Fingerprint> = None;

    let sim = Simulator::<Fp>::simulate((), |dr, _| {
        let stacks = synthesize_with_hook(
            dr,
            &mut Standard::new(),
            program,
            &[],
            |dr, idx, elems, _bools| {
                // Apply the cheat *before* executing ops[cheat_at]. We
                // require a non-empty elems stack, otherwise there is
                // nothing to cheat on and the test is degenerate.
                //
                // Clamp the target to indices < 64 so the cheated element
                // survives any future truncation to ELEM_TRUNCATE_TO.
                // Otherwise the cheat can be dropped from the stack
                // mid-run, removing it from the final fingerprint and
                // producing a false-positive match.
                if apply_cheat && idx == input.cheat_at as usize && !elems.is_empty() {
                    let target = (input.target_idx as usize) % elems.len().min(64);
                    let original_val: Fp = *elems[target].value().take();
                    let cheat_val = match input.cheat {
                        CheatFlavor::Alloc(v) => Fp::from(v),
                        CheatFlavor::Constant(v) => Fp::from(v),
                        CheatFlavor::Special(idx) => special_value(idx),
                    };
                    if original_val == cheat_val {
                        // No actual cheat — the chosen replacement value
                        // happens to equal what was already there.
                        // Fingerprints would trivially match; abort so the
                        // outer harness discards this run.
                        return Err(Error::InvalidWitness("degenerate no-op cheat".into()));
                    }
                    let cheated = match input.cheat {
                        CheatFlavor::Alloc(_) | CheatFlavor::Special(_) => {
                            Element::alloc(dr, &mut (), Simulator::<Fp>::just(move || cheat_val))?
                        }
                        CheatFlavor::Constant(_) => Element::constant(dr, cheat_val),
                    };
                    elems[target] = cheated;
                }
                Ok(())
            },
        )?;

        // Capture the final stack state. Element::value and Boolean::value
        // are infallible under the Simulator driver because its MaybeKind
        // is Always.
        let elem_vals: Vec<Fp> = stacks.elems.iter().map(|e| *e.value().take()).collect();
        let bool_vals: Vec<bool> = stacks.bools.iter().map(|b| b.value().take()).collect();
        snapshot = Some((elem_vals, bool_vals));

        Ok(())
    });

    if sim.is_err() {
        return None;
    }
    snapshot
}

/// How many elements an Op pushes onto the `elems` stack.
///
/// Used by the TRIAGE_CHEAT path to walk the op stream without actually
/// running the Simulator. Assumes Result-returning ops succeed (worst
/// case for "did the cheat propagate" — gives an upper bound).
fn op_pushes(op: &Op) -> usize {
    match op.kind() {
        OpKind::AllocSquare => 2,
        OpKind::IsZero | OpKind::BoolAlloc | OpKind::BoolNot | OpKind::BoolAnd | OpKind::Anchor => {
            0
        }
        _ => 1,
    }
}

/// Whether an Op's element-push is conditional on a runtime `Result`
/// (`if let Ok(_)` in the substrate dispatch). `op_pushes` is an upper
/// bound for these — actual execution may push zero. Used by
/// `is_dead_cheat` to refuse predicting through unpredictable stack
/// growth.
///
/// Note: ops that use `?` to propagate errors (e.g., `Op::AllocSpecial`,
/// `Op::BoolAlloc`, the `Element::alloc` inside `Op::Fold`) are
/// intentionally excluded here. They fail *symmetrically* in the honest
/// and cheat paths because pre-cheat ops execute identically through
/// both invocations of `run_path`, so a `?`-propagated failure causes
/// both paths to return `None` and the harness exits before the
/// soundness assertion — there is no false-positive surface to guard
/// against. Only `if let Ok(_)`-style fallible pushes can shift the
/// effective stack length between paths and need conservative bail-out.
fn op_can_fail_push(op: &Op) -> bool {
    matches!(
        op.kind(),
        OpKind::Mul
            | OpKind::Square
            | OpKind::Invert
            | OpKind::Divide
            | OpKind::Fold
            | OpKind::AllocRaw
            | OpKind::AllocSquare
            | OpKind::ConditionalSelect
    )
}

/// Whether an Op reads `elems[target]` (given the current elem stack length).
fn op_reads_target(op: &Op, target: usize, elens: usize) -> bool {
    if elens == 0 {
        return false;
    }
    let resolves = |a: u8| (a as usize) % elens == target;
    match *op {
        Op::Add(a, b) | Op::Sub(a, b) | Op::Mul(a, b) | Op::Divide(a, b) | Op::Fold(a, b, _) => {
            resolves(a) || resolves(b)
        }
        Op::ConditionalSelect(_, a, b) => resolves(a) || resolves(b),
        Op::Scale(a, _)
        | Op::Square(a)
        | Op::Double(a)
        | Op::Negate(a)
        | Op::Invert(a)
        | Op::IsZero(a)
        | Op::Anchor(a) => resolves(a),
        _ => false,
    }
}

/// Triage helper: simulate stack growth through the op stream without
/// invoking the Simulator. Returns `(target_at_cheat, downstream_reads,
/// downstream_ops)` describing how many downstream ops actually reference
/// the cheated slot. A `downstream_reads = 0` result indicates a "dead
/// cheat" — the soundness assertion cannot fire (the cheat value remains
/// observable at position `target_at_cheat` in the cheat-path fingerprint
/// while honest-path holds the original value, so honest != cheated is
/// trivially satisfied).
fn triage_cheat(input: &Input, ops: &[Op]) -> (usize, usize, usize) {
    let mut elens: usize = Preamble::LEN;
    let cheat_at_idx = (input.cheat_at as usize).min(ops.len());

    // Walk pre-cheat ops to compute elens at cheat time.
    for op in &ops[..cheat_at_idx] {
        if elens == 0 {
            return (0, 0, 0);
        }
        elens += op_pushes(op);
        if elens > 128 {
            elens = 64;
        }
    }

    if elens == 0 {
        return (0, 0, 0);
    }

    let target_at_cheat = (input.target_idx as usize) % elens.min(64);

    let mut downstream_reads = 0usize;
    let mut downstream_ops = 0usize;
    for op in &ops[cheat_at_idx..] {
        if elens == 0 {
            break;
        }
        downstream_ops += 1;
        if op_reads_target(op, target_at_cheat, elens) {
            downstream_reads += 1;
        }
        elens += op_pushes(op);
        if elens > 128 {
            elens = 64;
        }
    }

    (target_at_cheat, downstream_reads, downstream_ops)
}

/// Pre-flight check: returns `true` if the static op walk can prove the
/// cheated slot is never read by any downstream op. Inputs classified as
/// dead are skipped — running the two simulator paths on them is pure
/// waste, and they dominate the input distribution under random `Op`
/// sampling (most variants either don't read elements at all or pick
/// indices that miss the cheated slot).
///
/// **Soundness bound.** `op_pushes` is an upper-bound estimator (it
/// assumes Result-returning ops succeed). To match `run_path`'s
/// `target_at_cheat` computation exactly, we refuse to predict when any
/// pre-cheat op has a fallible push: in those cases the predicted `elens`
/// at the cheat point would exceed the real `elens`, drifting
/// `target_at_cheat = target_idx % elens.min(64)` to a different slot than
/// `run_path` actually cheats on. We conservatively return `false` (not
/// dead) and run the full path.
///
/// Residual suffix drift: when a *suffix* op fails to push, the prediction
/// can still miss a real read (`(a % elens_real) == target` while
/// `(a % elens_pred) != target`). This is a coverage shave, not a
/// soundness break — it requires both a suffix failure and a specific
/// modular near-miss on the read index. Inputs with multiple real reads
/// almost always trip the live-cheat check on a non-drifting read first.
///
/// Bails out on the first read, so the walk costs O(prefix + 1) for live
/// cheats vs. O(prefix + suffix) for dead cheats — the asymmetry favors
/// the cheap path.
fn is_dead_cheat(input: &Input, ops: &[Op]) -> bool {
    let mut elens: usize = Preamble::LEN;
    let cheat_at_idx = (input.cheat_at as usize).min(ops.len());

    for op in &ops[..cheat_at_idx] {
        // Pre-cheat fallible push → `elens` prediction may exceed reality,
        // breaking `target_at_cheat` agreement with `run_path`. Bail.
        if op_can_fail_push(op) {
            return false;
        }
        elens += op_pushes(op);
        if elens > 128 {
            elens = 64;
        }
    }

    if elens == 0 {
        return true;
    }

    // Mirror `run_path`: `target_idx % elems.len().min(64)`. The clamp lower
    // bound guards `% 0` if `elens` is ever zero here (currently unreachable
    // given the preamble shape, but defends against future schema changes).
    let target_at_cheat = (input.target_idx as usize) % elens.clamp(1, 64);

    for op in &ops[cheat_at_idx..] {
        if elens == 0 {
            break;
        }
        if op_reads_target(op, target_at_cheat, elens) {
            return false;
        }
        elens += op_pushes(op);
        if elens > 128 {
            elens = 64;
        }
    }

    true
}

fuzz_target!(|input: Input| {
    let program = Program::decode(&input.program, opset(), Limits::default());

    // DEBUG_INPUT=1 prints the parsed input and decoded program, then
    // exits — useful for triaging crash artifacts. See README.md.
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!(
            "cheat_at = {}, target_idx = {}, cheat = {:?}\n{program:#?}",
            input.cheat_at, input.target_idx, input.cheat,
        );
        return;
    }
    // TRIAGE_CHEAT=1 walks the op stream tracking the cheated slot and
    // reports how many downstream ops reference it. A 0 count means
    // "dead cheat" — the soundness signal is a false positive.
    if std::env::var("TRIAGE_CHEAT").is_ok() {
        let (target_at_cheat, downstream_reads, downstream_ops) =
            triage_cheat(&input, &program.ops);
        eprintln!(
            "cheat_at = {}\n\
             target_idx = {} → target_at_cheat = {}\n\
             cheat flavor = {:?}\n\
             downstream ops = {}\n\
             downstream reads of cheated slot = {}",
            input.cheat_at,
            input.target_idx,
            target_at_cheat,
            input.cheat,
            downstream_ops,
            downstream_reads,
        );
        if downstream_reads == 0 {
            eprintln!(
                "\nVERDICT: DEAD CHEAT — cheated slot was never read after the \
                 cheat fired. The fingerprint match is structurally trivial; \
                 this is almost certainly a false-positive soundness signal."
            );
        } else {
            eprintln!(
                "\nVERDICT: LIVE CHEAT — cheated slot was read {} times \
                 downstream. If `cargo +nightly fuzz run fuzz_witness_cheat \
                 <file>` confirms the panic, the gadget on that read path \
                 is plausibly under-constrained.",
                downstream_reads,
            );
        }
        return;
    }
    if program.ops.is_empty() {
        return;
    }

    // Cheat must land inside the executable op range, otherwise the cheat
    // is a no-op and fingerprints trivially match.
    if (input.cheat_at as usize) >= program.ops.len() {
        return;
    }

    // Skip dead cheats — inputs where the cheated slot is never read
    // downstream. The soundness assertion cannot fire on these (the cheat
    // value remains visible at position `target_at_cheat` in the cheat-path
    // fingerprint, differing from honest-path's original value by
    // construction), so running the simulator twice would be pure waste.
    // This walk reads bytes only; no field arithmetic, no constraint checks.
    if is_dead_cheat(&input, &program.ops) {
        return;
    }

    let honest = match run_path(&program, &input, false) {
        Some(f) => f,
        None => return,
    };
    let cheated = match run_path(&program, &input, true) {
        Some(f) => f,
        None => return,
    };

    // Soundness signal: cheat path accepted by Simulator AND its final
    // state is observationally identical to the honest run.
    assert!(
        honest != cheated,
        "soundness signal: cheat at op[{}] target {} flavor {:?} \
         did not perturb the final state; \
         every downstream constraint and observation was insensitive to \
         the swap. Suspect an under-constrained gadget. \
         Program: {program:?}",
        input.cheat_at,
        input.target_idx,
        input.cheat,
    );
});
