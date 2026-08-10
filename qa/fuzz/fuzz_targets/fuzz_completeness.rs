//! Completeness (over-constraint) fuzzing: a correct circuit accepts every
//! valid witness, not just the honest one (issues #728, #793).
//!
//! The rest of the patcher family chases *soundness* — a witness ragu
//! wrongly accepts. This is the dual: an *over-constrained* gadget wrongly
//! rejects a witness it should accept (a completeness bug).
//!
//! For an anchorless program over the infallible vocabulary, every
//! assignment of the preamble witness is valid by construction: the gadgets
//! compute derived values that satisfy their own constraints, no anchor pins
//! anything, and no value-dependent failure (divide-by-zero, invert-zero)
//! can occur. So ragu's real [`Simulator`] — its actual constraint checker —
//! must accept every witness. A rejection is a completeness bug.

#![no_main]

use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_core::maybe::{Always, MaybeKind};
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing_fuzz::substrate::{
    Capabilities, Limits, OpSet, Preamble, Program, synthesize_with_witness,
};

#[derive(arbitrary::Arbitrary, Debug)]
struct Input {
    /// Seeds for the preamble witness values, one per slot.
    witness: [u64; Preamble::LEN],
    /// Raw program bytes, decoded via [`Program::decode`]. Last field, so
    /// `arbitrary_take_rest` hands it the remainder of the input.
    program: Vec<u8>,
}

/// The infallible, anchorless vocabulary: no value-fallible ops (so no
/// witness can trigger a rejection) and no anchors (so no witness is pinned).
fn opset() -> OpSet {
    OpSet::ALL
        .without(Capabilities::VALUE_FALLIBLE)
        .without(Capabilities::ANCHORS)
}

fuzz_target!(|input: Input| {
    let program = Program::decode(&input.program, opset(), Limits::default());

    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("witness={:?}\n{program:#?}", input.witness);
        return;
    }
    if program.ops.is_empty() {
        return;
    }

    let witness: [Fp; Preamble::LEN] = core::array::from_fn(|i| Fp::from(input.witness[i]));

    let sim = Simulator::<Fp>::simulate((), |dr, _| {
        synthesize_with_witness(
            dr,
            &mut Standard::new(),
            &program,
            Always::maybe_just(move || witness),
            &[],
        )?;
        Ok(())
    });

    assert!(
        sim.is_ok(),
        "COMPLETENESS SIGNAL: ragu's Simulator REJECTED a valid witness \
         {witness:?} for an anchorless, infallible circuit — an \
         over-constrained gadget. Program: {program:?}",
    );
});
