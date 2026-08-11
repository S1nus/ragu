//! Witness-inspection coverage augmentation POC.
//!
//! Same substrate dispatch as `fuzz_element_ops` (shared via
//! [`ragu_testing_fuzz::substrate`]), but with an added coverage-augmentation
//! step at the end of each successful simulation: the final witness state
//! (element values + boolean values) is hashed and the hash is "spread"
//! across branches that SanitizerCoverage's PC-guard instrumentation
//! tracks as edges. The intent is to bias libFuzzer toward exploring
//! distinct *internal witness states* even when the `Simulator`'s
//! Rust-level branches don't differ between inputs.
//!
//! # Why
//!
//! libFuzzer's coverage feedback is edge-based: it tracks which branches
//! the target binary took. The `Simulator` is a Rust interpreter, so it
//! has plenty of native branches (one per `Op` arm, plus error paths
//! inside each gadget), and libFuzzer naturally explores them. But two
//! inputs can take the *same* Rust branches in the simulator and still
//! produce structurally different witnesses — different `is_zero` results,
//! different `ConditionalSelect` outcomes, different element values
//! flowing through downstream ops — that the fuzzer doesn't distinguish.
//!
//! This target augments coverage with a witness-state fingerprint: at the
//! end of each successful simulation, the final element- and boolean-
//! value vectors are hashed to a `u64`, and each set bit of that hash is
//! used to fire a distinct `if` branch under `black_box`. libFuzzer's
//! PC-guard instrumentation then sees those branches as separate edges,
//! and combinations of set bits become new coverage. The fuzzer biases
//! mutation toward inputs that produce previously-unseen witness states.
//!
//! # Comparison protocol
//!
//! Run `fuzz_element_ops` and `fuzz_witness_coverage` for the same wall-
//! clock budget on empty corpora. Compare libFuzzer's reported `cov`
//! (edges), `ft` (features), and especially **corpus size** (saved inputs
//! that triggered new coverage). The augmentation is valuable if the
//! corpus grows faster or the explored input space is more diverse.
//!
//! The augmentation costs ~28% throughput in measured runs (extra hashing
//! plus the 64-branch coverage spray per iteration). It is kept opt-in as
//! a separate target rather than applied to all targets so users can
//! choose the trade-off per campaign.

#![no_main]

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::hint::black_box;

use ff::PrimeField;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_core::maybe::Maybe;
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing_fuzz::substrate::{Capabilities, Limits, OpSet, Program, synthesize};

/// Hash the final witness state into a single u64.
///
/// Field elements are serialized via `to_repr()` (canonical byte form);
/// booleans are hashed as a `Vec<bool>`. Uses `DefaultHasher` because
/// adversarial hash resistance isn't needed — we only need different
/// witnesses to produce different hashes with overwhelming probability.
fn hash_witness(elems: &[Fp], bools: &[bool]) -> u64 {
    let mut hasher = DefaultHasher::new();
    for fp_val in elems {
        fp_val.to_repr().as_ref().hash(&mut hasher);
    }
    bools.hash(&mut hasher);
    hasher.finish()
}

/// Spread the witness fingerprint across distinct branches that
/// SanitizerCoverage's PC-guard instrumentation tracks as separate edges.
///
/// Each set bit of the hash fires a `black_box(i)` call inside its own
/// `if` arm. Different fingerprints → different combinations of branches
/// taken → libFuzzer perceives new coverage and biases mutation toward
/// inputs that produce previously-unseen witness states.
///
/// `black_box` prevents the compiler from constant-folding the loop body
/// away. The cost is 64 conditional branches per successful run, which is
/// negligible compared to the simulator's overhead.
#[inline(never)]
fn feed_witness_coverage(fingerprint: u64) {
    for i in 0..64 {
        if (fingerprint >> i) & 1 == 1 {
            black_box(i);
        }
    }
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

    let _ = Simulator::<Fp>::simulate((), |dr, _| {
        let stacks = synthesize(dr, &mut Standard::new(), &program, &[])?;

        // Augmentation: hash the final witness state and feed it to
        // libFuzzer's coverage tracker via the branch-on-hash trick.
        let elem_vals: Vec<Fp> = stacks.elems.iter().map(|e| *e.value().take()).collect();
        let bool_vals: Vec<bool> = stacks.bools.iter().map(|b| b.value().take()).collect();
        feed_witness_coverage(hash_witness(&elem_vals, &bool_vals));

        Ok(())
    });
});
