//! Driver-vs-driver metamorphic fuzz target.
//!
//! Runs the same decoded program through two `Driver` implementations —
//! `Simulator` and `Emulator<Wired<Fp>>` — and compares the resulting
//! final element-value sequences. Tests the load-bearing invariant that
//! the model driver (which asserts `a*b = c` and `enforce_zero(lc) = 0`
//! inline) and the witness-extraction driver that the synthesis pipeline
//! builds on top of (`Emulator`, used internally by `trace::eval`) process
//! the same gadget code observationally identically.
//!
//! The op grammar, byte decoding, and gadget dispatch live in
//! [`ragu_testing_fuzz::substrate`] — one driver-generic interpreter runs both
//! sides, so this target is also the proof that the substrate itself does
//! not branch on driver type.
//!
//! # Oracle
//!
//! After running the same program through both drivers:
//!
//! - `(Simulator: Ok, Emulator: Ok)` → both succeeded; compare final
//!   element values. Any divergence → **bug** (the two drivers disagree on
//!   what the witness's internal wire values are).
//! - `(Simulator: Err, Emulator: Ok)` → expected: a witness invalid by
//!   `Simulator`'s constraint check would be silently accepted by
//!   `Emulator`, which does not enforce gate equations. Discard.
//! - `(Simulator: Ok, Emulator: Err)` → **bug**: `Simulator` accepted but
//!   `Emulator` couldn't even produce a wire. Would mean a gadget-internal
//!   error path triggered only in `Emulator`, which should be impossible
//!   under the shared gadget code.
//! - `(Simulator: Err, Emulator: Err)` → consistent rejection (e.g. both
//!   hit `Element::invert(0)` or similar gadget-level error). Discard.
//!
//! # What this catches
//!
//! - Subtle differences in how `Simulator::gate` and `Emulator::gate`
//!   handle the same witness closure.
//! - Divergent behavior in `Driver::routine` between the two drivers
//!   (`Simulator::routine` calls `Emulator::predict` internally, then
//!   `routine.execute(self, ...)` — the predict-then-execute split could
//!   diverge if either side has a bug).
//! - Any gadget code that branches on driver type (which it shouldn't, but
//!   this is the load-bearing invariant the test enforces).
//!
//! # What this doesn't catch
//!
//! - Bugs in `trace::eval`'s segment-grouping logic (positional metadata,
//!   not wire values).
//! - Bugs in the trace-polynomial assembly, constraint polynomial emission
//!   (`WiringObject`), or downstream prover/verifier components.
//! - Soundness gaps in the constraint system itself (the
//!   `fuzz_witness_pinning` / `fuzz_circuit_cheat` / `fuzz_advice_patcher`
//!   lane).

#![no_main]

use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_core::{
    drivers::{
        Driver,
        emulator::{Emulator, Wired},
    },
    maybe::{Always, Maybe},
};
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing_fuzz::substrate::{Capabilities, Limits, OpSet, Program, synthesize};

/// Final-state fingerprint: every element's value followed by every
/// boolean's value, in stack order.
type Fingerprint = (Vec<Fp>, Vec<bool>);

/// Run the program against a driver and capture the final fingerprint.
fn run_path<'dr, D>(dr: &mut D, program: &Program) -> ragu_core::Result<Fingerprint>
where
    D: Driver<'dr, F = Fp, MaybeKind = Always<()>>,
{
    let stacks = synthesize(dr, &mut Standard::new(), program, &[])?;
    let elem_vals: Vec<Fp> = stacks.elems.iter().map(|e| *e.value().take()).collect();
    let bool_vals: Vec<bool> = stacks.bools.iter().map(|b| b.value().take()).collect();
    Ok((elem_vals, bool_vals))
}

/// Run the program through `Simulator`, capturing the final fingerprint
/// on success.
fn run_simulator(program: &Program) -> Option<Fingerprint> {
    let mut snapshot: Option<Fingerprint> = None;
    let sim = Simulator::<Fp>::simulate((), |dr, _| {
        snapshot = Some(run_path(dr, program)?);
        Ok(())
    });
    if sim.is_err() {
        return None;
    }
    snapshot
}

/// Run the program through `Emulator<Wired<Fp>>`, capturing the final
/// fingerprint on success.
fn run_emulator(program: &Program) -> Option<Fingerprint> {
    let mut snapshot: Option<Fingerprint> = None;
    let result = Emulator::<Wired<Fp>>::emulate_wired((), |dr, _| {
        snapshot = Some(run_path(dr, program)?);
        Ok(())
    });
    if result.is_err() {
        return None;
    }
    snapshot
}

fuzz_target!(|data: &[u8]| {
    let program = Program::decode(
        data,
        OpSet::ALL.without(Capabilities::ANCHORS),
        Limits::default(),
    );

    // DEBUG_INPUT=1 prints the decoded program and exits — useful for
    // triaging crash artifacts. See README.md "DEBUG_INPUT env var" section.
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{program:#?}");
        return;
    }
    if program.ops.is_empty() {
        return;
    }

    let sim = run_simulator(&program);
    let emu = run_emulator(&program);

    match (&sim, &emu) {
        (None, _) => {
            // Simulator rejected. Discard regardless of what Emulator did:
            // (None, None) is consistent rejection, (None, Some(_)) is the
            // expected case where Simulator's stricter constraint enforcement
            // catches something Emulator silently accepts.
        }
        (Some(_), None) => {
            // Simulator accepted but Emulator failed. Both drivers run the
            // same gadget code with the same witness; the Emulator does
            // *less* enforcement than Simulator, so any gadget-internal Err
            // it hits should also have triggered for Simulator. This is a
            // bug.
            panic!(
                "driver divergence: Simulator accepted, Emulator rejected. Program: {program:?}",
            );
        }
        (Some(s), Some(e)) => {
            // Both drivers ran successfully. The same gadget code with the
            // same witness must produce the same wire values; any
            // disagreement is a model-vs-real driver divergence.
            assert!(
                s == e,
                "driver divergence: Simulator and Emulator produced different \
                 final fingerprints from the same program and witness. \
                 sim={s:?}, emu={e:?}, program={program:?}",
            );
        }
    }
});
