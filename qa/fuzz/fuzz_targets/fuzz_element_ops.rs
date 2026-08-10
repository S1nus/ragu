//! Fuzz arbitrary `Element` and `Boolean` operation sequences through the `Simulator`.
//!
//! Invariants:
//! - The `Simulator` never panics for valid witness values.
//! - Expected failures (invert zero, div by zero) return `Err`, not panic.
//!
//! The op grammar, byte decoding, and gadget dispatch live in
//! [`ragu_testing_fuzz::substrate`], shared with the other op-stream targets;
//! this harness owns only the vocabulary mask (the historical 19-op
//! robustness set — everything except `Anchor`) and the
//! swallow-errors-but-never-panic policy.

#![no_main]

use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing_fuzz::substrate::{Capabilities, Limits, OpSet, Program, synthesize};

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

    let _ = Simulator::<Fp>::simulate((), |dr, _| {
        synthesize(dr, &mut Standard::new(), &program, &[])?;
        Ok(())
    });
});
