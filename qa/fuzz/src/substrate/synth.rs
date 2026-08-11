//! Layer 3: driver-generic synthesis of generated programs.
//!
//! One interpreter turns a [`Program`] into real gadget calls against any
//! [`Driver`]. The per-op error semantics are copied exactly from the
//! historical `fuzz_element_ops` dispatch so migrated targets keep their
//! behavior: value-fallible gadget calls *skip* the push on failure (the
//! stack simply doesn't grow), while allocation failures propagate.
//!
//! Consumers that need value-independent stack progression (the patcher
//! family aligns stack slots between an honest and a mutated run) get it by
//! generating programs whose fallible ops are steered to succeed (layer 5),
//! not by changing the interpreter.

use ff::PrimeField;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    maybe::Maybe,
};
use ragu_primitives::{Boolean, Element, allocator::Allocator};

use super::{Op, Program, special_value};

/// Element-stack cap: when the stack exceeds this, it is truncated to
/// [`ELEM_TRUNCATE_TO`]. Mirrors the historical robustness-target bound;
/// the shadow evaluator applies the identical rule so slots stay aligned.
pub const ELEM_STACK_CAP: usize = 128;
/// See [`ELEM_STACK_CAP`].
pub const ELEM_TRUNCATE_TO: usize = 64;
/// Boolean-stack cap, truncating to [`BOOL_TRUNCATE_TO`].
pub const BOOL_STACK_CAP: usize = 64;
/// See [`BOOL_STACK_CAP`].
pub const BOOL_TRUNCATE_TO: usize = 32;

/// The synthesized stacks, returned so consumers can extract wires, values,
/// or outputs.
pub struct Stacks<'dr, D: Driver<'dr>> {
    /// The element stack after the final op.
    pub elems: Vec<Element<'dr, D>>,
    /// The boolean stack after the final op.
    pub bools: Vec<Boolean<'dr, D>>,
    /// Number of [`Op::Anchor`]s that emitted a pinning constraint (anchors
    /// beyond the supplied constants are skipped).
    pub anchors_emitted: usize,
    /// Every *free-advice* wire allocated during synthesis, in creation
    /// order: non-constant preamble slots, `AllocSpecial`/`AllocRaw`/
    /// `AllocSquare`-root elements, `Fold` scales, and `BoolAlloc`
    /// booleans. These are the prover's genuine degrees of freedom — the
    /// wires a constraint-graph solver must hold fixed (everything else is
    /// derived). Gadget-internal hints that *are* pinned (a multiplication
    /// gate's output, an `invert` inverse, a `divide` quotient) are
    /// excluded, because constraints determine them.
    pub advice_wires: Vec<D::Wire>,
    /// The wire of each [`Op::BoolAlloc`]-allocated boolean, in creation
    /// order — a subset of [`advice_wires`](Self::advice_wires). A boolean
    /// wire is pinned to `{0, 1}` only by its booleanity constraints
    /// (`a·b = 0`, `a + b = 1`); the patcher cheats these wires to a
    /// non-boolean field value to check that booleanity actually rejects.
    pub bool_advice_wires: Vec<D::Wire>,
    /// Each [`Op::Fold`] scale, as `(op index, wire)` — a subset of
    /// [`advice_wires`](Self::advice_wires). The op index keys the native
    /// shadow's [`Overrides::fold_scales`](super::Overrides::fold_scales), so
    /// the patcher can cheat a fold scale and have both sides judge the same
    /// commitment.
    pub fold_advice: Vec<(usize, D::Wire)>,
}

/// Synthesizes `program` through `dr`.
///
/// The preamble elements are created first — constants where
/// [`Preamble::is_constant`](super::Preamble::is_constant) says so,
/// allocated witness wires otherwise — then ops execute in order with
/// operand indices reduced modulo the live stack length.
///
/// `anchors` supplies the pinned constant for each [`Op::Anchor`] in
/// encounter order, typically captured from an honest shadow evaluation;
/// anchors beyond the supplied slice emit nothing. Robustness consumers
/// that exclude `Anchor` from their mask pass `&[]`.
pub fn synthesize<'dr, D: Driver<'dr>>(
    dr: &mut D,
    allocator: &mut impl Allocator<'dr, D>,
    program: &Program,
    anchors: &[D::F],
) -> Result<Stacks<'dr, D>>
where
    D::F: PrimeField<Repr = [u8; 32]>,
{
    synthesize_with_hook(dr, allocator, program, anchors, |_, _, _, _| Ok(()))
}

/// [`synthesize`] with the witness-slot preamble values supplied through
/// the driver's witness mechanism instead of derived from the program.
///
/// This is what lets a generated program act as a real
/// [`Circuit`](ragu_circuits::Circuit): the program (including its constant
/// preamble slots and anchor constants) is circuit *structure*, while the
/// witness-allocated preamble values are the circuit *witness* — so the
/// same registered circuit can be re-traced with mutated witnesses, which
/// is the patcher family's whole game. The honest witness is
/// [`Preamble::values`](super::Preamble::values).
pub fn synthesize_with_witness<'dr, D: Driver<'dr>>(
    dr: &mut D,
    allocator: &mut impl Allocator<'dr, D>,
    program: &Program,
    witness: DriverValue<D, [D::F; super::Preamble::LEN]>,
    anchors: &[D::F],
) -> Result<Stacks<'dr, D>>
where
    D::F: PrimeField<Repr = [u8; 32]>,
{
    let structure: [D::F; super::Preamble::LEN] = program.preamble.values();
    let mut elems: Vec<Element<'dr, D>> = Vec::with_capacity(structure.len());
    let mut advice_wires: Vec<D::Wire> = Vec::new();
    for (i, v) in structure.into_iter().enumerate() {
        if program.preamble.is_constant(i) {
            elems.push(Element::constant(dr, v));
        } else {
            let e = Element::alloc(dr, allocator, witness.as_ref().map(move |w| w[i]))?;
            advice_wires.push(e.wire().clone());
            elems.push(e);
        }
    }
    synthesize_ops(
        dr,
        allocator,
        program,
        elems,
        advice_wires,
        anchors,
        |_, _, _, _| Ok(()),
    )
}

/// [`synthesize`] with a hook invoked before every op.
///
/// The hook receives the index of the op about to execute and mutable
/// access to both stacks; `fuzz_witness_cheat`-style harnesses use it to
/// swap a stack element mid-stream ("replace `elems[target]` *before*
/// `ops[cheat_at]` runs"). Returning an error aborts synthesis, which
/// harnesses use to discard degenerate runs.
pub fn synthesize_with_hook<'dr, D: Driver<'dr>>(
    dr: &mut D,
    allocator: &mut impl Allocator<'dr, D>,
    program: &Program,
    anchors: &[D::F],
    hook: impl FnMut(&mut D, usize, &mut Vec<Element<'dr, D>>, &mut Vec<Boolean<'dr, D>>) -> Result<()>,
) -> Result<Stacks<'dr, D>>
where
    D::F: PrimeField<Repr = [u8; 32]>,
{
    let values: [D::F; super::Preamble::LEN] = program.preamble.values();
    let mut elems: Vec<Element<'dr, D>> = Vec::with_capacity(values.len());
    let mut advice_wires: Vec<D::Wire> = Vec::new();
    for (i, v) in values.into_iter().enumerate() {
        if program.preamble.is_constant(i) {
            elems.push(Element::constant(dr, v));
        } else {
            let e = Element::alloc(dr, allocator, D::just(move || v))?;
            advice_wires.push(e.wire().clone());
            elems.push(e);
        }
    }
    synthesize_ops(dr, allocator, program, elems, advice_wires, anchors, hook)
}

/// Executes `program.ops` over an already-built initial element stack.
/// Shared tail of [`synthesize_with_hook`] and [`synthesize_with_witness`].
fn synthesize_ops<'dr, D: Driver<'dr>>(
    dr: &mut D,
    allocator: &mut impl Allocator<'dr, D>,
    program: &Program,
    mut elems: Vec<Element<'dr, D>>,
    mut advice_wires: Vec<D::Wire>,
    anchors: &[D::F],
    mut hook: impl FnMut(
        &mut D,
        usize,
        &mut Vec<Element<'dr, D>>,
        &mut Vec<Boolean<'dr, D>>,
    ) -> Result<()>,
) -> Result<Stacks<'dr, D>>
where
    D::F: PrimeField<Repr = [u8; 32]>,
{
    let mut bools: Vec<Boolean<'dr, D>> = Vec::new();
    let mut bool_advice_wires: Vec<D::Wire> = Vec::new();
    let mut fold_advice: Vec<(usize, D::Wire)> = Vec::new();
    let mut anchor_idx = 0usize;

    for (idx, op) in program.ops.iter().enumerate() {
        hook(dr, idx, &mut elems, &mut bools)?;

        let elen = elems.len();
        let blen = bools.len();
        if elen == 0 {
            break;
        }

        match *op {
            Op::Add(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                let r = elems[a].add(dr, &elems[b]);
                elems.push(r);
            }
            Op::Sub(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                let r = elems[a].sub(dr, &elems[b]);
                elems.push(r);
            }
            Op::Mul(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                if let Ok(r) = elems[a].mul(dr, &elems[b]) {
                    elems.push(r);
                }
            }
            Op::Square(a) => {
                let a = a as usize % elen;
                if let Ok(r) = elems[a].square(dr) {
                    elems.push(r);
                }
            }
            Op::Double(a) => {
                let a = a as usize % elen;
                let r = elems[a].double(dr);
                elems.push(r);
            }
            Op::Negate(a) => {
                let a = a as usize % elen;
                let r = elems[a].negate(dr);
                elems.push(r);
            }
            Op::Invert(a) => {
                let a = a as usize % elen;
                if let Ok(r) = elems[a].invert(dr) {
                    elems.push(r);
                }
            }
            Op::IsZero(a) => {
                let a = a as usize % elen;
                if let Ok(b) = elems[a].is_zero(dr, allocator) {
                    bools.push(b);
                }
            }
            Op::Divide(a, b) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                if let Ok(b_nz) = elems[b].clone().enforce_nonzero(dr)
                    && let Ok(r) = elems[a].divide(dr, &b_nz)
                {
                    elems.push(r);
                }
            }
            Op::Scale(a, c) => {
                let a = a as usize % elen;
                let r = elems[a].scale(dr, Coeff::Arbitrary(D::F::from(c)));
                elems.push(r);
            }
            Op::Fold(a, b, s) => {
                let (a, b) = (a as usize % elen, b as usize % elen);
                let scale = Element::alloc(dr, allocator, D::just(move || D::F::from(s)))?;
                advice_wires.push(scale.wire().clone());
                fold_advice.push((idx, scale.wire().clone()));
                if let Ok(r) = Element::fold(dr, [&elems[a], &elems[b]], &scale) {
                    elems.push(r);
                }
            }
            Op::AllocConst(v) => {
                let r = Element::constant(dr, D::F::from(v));
                elems.push(r);
            }
            Op::AllocSpecial(idx) => {
                let v = special_value::<D::F>(idx);
                let r = Element::alloc(dr, allocator, D::just(move || v))?;
                advice_wires.push(r.wire().clone());
                elems.push(r);
            }
            Op::AllocRaw(bytes) => {
                let v: Option<D::F> = D::F::from_repr(bytes).into();
                if let Some(fp) = v
                    && let Ok(r) = Element::alloc(dr, allocator, D::just(move || fp))
                {
                    advice_wires.push(r.wire().clone());
                    elems.push(r);
                }
            }
            Op::AllocSquare(v) => {
                if let Ok((root, sq)) = Element::alloc_square(dr, D::just(move || D::F::from(v))) {
                    // The root is free advice; the square is derived (pinned
                    // by the alloc_square gate to root²).
                    advice_wires.push(root.wire().clone());
                    elems.push(root);
                    elems.push(sq);
                }
            }
            Op::BoolAlloc(v) => {
                if let Ok(b) = Boolean::alloc(dr, allocator, D::just(move || v)) {
                    advice_wires.push(b.wire().clone());
                    bool_advice_wires.push(b.wire().clone());
                    bools.push(b);
                }
            }
            Op::BoolNot(a) => {
                if blen > 0 {
                    let a = a as usize % blen;
                    let r = bools[a].not(dr);
                    bools.push(r);
                }
            }
            Op::BoolAnd(a, b) => {
                if blen > 0 {
                    let (a, b) = (a as usize % blen, b as usize % blen);
                    if let Ok(r) = bools[a].and(dr, &bools[b]) {
                        bools.push(r);
                    }
                }
            }
            Op::ConditionalSelect(cond, a, b) => {
                if blen > 0 {
                    let cond = cond as usize % blen;
                    let (a, b) = (a as usize % elen, b as usize % elen);
                    if let Ok(r) = bools[cond].conditional_select(dr, &elems[a], &elems[b]) {
                        elems.push(r);
                    }
                }
            }
            Op::Anchor(a) => {
                if anchor_idx < anchors.len() {
                    let slot = a as usize % elen;
                    let pin = Element::constant(dr, anchors[anchor_idx]);
                    elems[slot].sub(dr, &pin).enforce_zero(dr)?;
                }
                anchor_idx += 1;
            }
        }

        if elems.len() > ELEM_STACK_CAP {
            elems.truncate(ELEM_TRUNCATE_TO);
        }
        if bools.len() > BOOL_STACK_CAP {
            bools.truncate(BOOL_TRUNCATE_TO);
        }
    }

    Ok(Stacks {
        elems,
        bools,
        anchors_emitted: anchor_idx.min(anchors.len()),
        advice_wires,
        bool_advice_wires,
        fold_advice,
    })
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use ragu_pasta::Fp;
    use ragu_primitives::{Simulator, allocator::Standard};

    use super::*;
    use crate::substrate::{Limits, OpSet, Preamble, program_strategy};

    fn empty_preamble() -> Preamble {
        Preamble {
            seeds: [3, 5, 7, 11],
            large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
            special_seeds: [1, 11],
            constant_mask: 0b0000_0101,
        }
    }

    /// A handcrafted program touching both stacks synthesizes and the
    /// Simulator accepts it.
    #[test]
    fn smoke_simulator_accepts() {
        let program = Program {
            preamble: empty_preamble(),
            ops: vec![
                Op::Add(0, 1),
                Op::Mul(8, 2),
                Op::AllocSquare(9),
                Op::IsZero(3),
                Op::BoolAlloc(true),
                Op::BoolNot(0),
                Op::BoolAnd(0, 1),
                Op::ConditionalSelect(2, 4, 5),
                Op::Divide(9, 1),
                Op::Fold(0, 1, 17),
                Op::Invert(1),
            ],
        };
        let sim = Simulator::<Fp>::simulate((), |dr, _| {
            let stacks = synthesize(dr, &mut Standard::new(), &program, &[])?;
            assert!(stacks.elems.len() > Preamble::LEN);
            assert!(!stacks.bools.is_empty());
            Ok(())
        });
        assert!(sim.is_ok(), "Simulator rejected an honest program");
    }

    /// Anchors pinned to the elements' honest values are satisfiable; an
    /// anchor pinned to a wrong constant makes the Simulator reject.
    #[test]
    fn anchors_pin_honest_values() {
        let program = Program {
            preamble: empty_preamble(),
            ops: vec![Op::Add(0, 1), Op::Anchor(8)],
        };
        // Honest: slot 8 is seeds[0] + seeds[1] = 8.
        let honest = Simulator::<Fp>::simulate((), |dr, _| {
            let stacks = synthesize(dr, &mut Standard::new(), &program, &[Fp::from(8)])?;
            assert_eq!(stacks.anchors_emitted, 1);
            Ok(())
        });
        assert!(honest.is_ok(), "honest anchor rejected");

        let cheat = Simulator::<Fp>::simulate((), |dr, _| {
            synthesize(dr, &mut Standard::new(), &program, &[Fp::from(9)])?;
            Ok(())
        });
        assert!(cheat.is_err(), "wrong anchor constant must be rejected");
    }

    /// The pre-op hook observes the stack state before each op executes.
    #[test]
    fn hook_runs_per_op() {
        let program = Program {
            preamble: empty_preamble(),
            ops: vec![Op::Add(0, 1), Op::Double(2)],
        };
        let mut seen = Vec::new();
        let sim = Simulator::<Fp>::simulate((), |dr, _| {
            synthesize_with_hook(
                dr,
                &mut Standard::new(),
                &program,
                &[],
                |_, idx, elems, _| {
                    seen.push((idx, elems.len()));
                    Ok(())
                },
            )?;
            Ok(())
        });
        assert!(sim.is_ok());
        assert_eq!(seen, vec![(0, Preamble::LEN), (1, Preamble::LEN + 1)]);
    }

    proptest! {
        /// Every generated program synthesizes without panicking, and the
        /// Simulator never rejects when no anchors are emitted (all other
        /// constraints are satisfied by construction by the gadgets' own
        /// witnesses).
        #[test]
        fn proptest_simulator_accepts_anchorless(
            program in program_strategy(
                OpSet::ALL.without(crate::substrate::Capabilities::ANCHORS),
                Limits::default().max_ops,
            ),
        ) {
            let sim = Simulator::<Fp>::simulate((), |dr, _| {
                synthesize(dr, &mut Standard::new(), &program, &[])?;
                Ok(())
            });
            prop_assert!(sim.is_ok(), "Simulator rejected an honest anchorless program");
        }
    }
}
