//! Fuzz three-way agreement of the registry polynomial at a single circuit.
//!
//! For circuit $i$ at omega point $w$, three independent evaluators compute
//! the same registry polynomial:
//! - `wxy(w, x, y)` (scalar)
//! - `wx(w, x)` (polynomial in $Y$, evaluated at $y$)
//! - `wy(w, y)` (polynomial in $X$, evaluated at $x$)
//!
//! Invariant: `wxy(w, x, y) == wx(w, x).eval(y) == wy(w, y).eval(x)`
//!
//! The identity is a property of the *registry polynomial* — it never
//! inspects the witness — so any registered circuit is a valid vehicle.
//! The circuit is an arbitrary generated [`ragu_testing_fuzz::substrate`]
//! program (registered as a [`ProgramCircuit`]), generalizing the original
//! target's single hand-written `SquareCircuit` to the full space of
//! circuit shapes the grammar produces.

#![no_main]

use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_circuits::{
    polynomials::TestRank,
    registry::{CircuitIndex, RegistryBuilder},
};
use ragu_testing_fuzz::substrate::{Limits, OpSet, Overrides, Program, ProgramCircuit, shadow_eval};

#[derive(arbitrary::Arbitrary, Debug)]
struct Input {
    /// Raw program bytes, decoded via [`Program::decode`].
    program: Vec<u8>,
    x_seed: u64,
    y_seed: u64,
}

fuzz_target!(|input: Input| {
    // The full grammar. Registration is witness-independent (it runs the
    // wiring synthesis, which never evaluates values), so no steering is
    // needed — value-fallible ops emit their gates structurally.
    let program = Program::decode(&input.program, OpSet::ALL, Limits::default());

    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!(
            "x_seed={}, y_seed={}\n{program:#?}",
            input.x_seed, input.y_seed
        );
        return;
    }
    if program.ops.is_empty() {
        return;
    }

    // Anchor constants are circuit structure; the honest shadow supplies
    // one per `Anchor` op. (Their values do not affect the three-way
    // identity, but a well-formed circuit needs them to register.)
    let honest = shadow_eval::<Fp>(&program, Overrides::none());
    let circuit = ProgramCircuit {
        program: &program,
        anchors: &honest.anchors,
    };
    let registry = match RegistryBuilder::<Fp, TestRank>::new()
        .register_circuit(circuit)
        .and_then(|b| b.finalize())
    {
        Ok(r) => r,
        Err(_) => return, // Circuit too large for rank — skip.
    };

    let w = CircuitIndex::new(0).omega_j::<Fp>();
    let x = Fp::from(input.x_seed);
    let y = Fp::from(input.y_seed);

    let sxy = registry.wxy(w, x, y);
    let sx_at_y = registry.wx(w, x).eval(y);
    let sy_at_x = registry.wy(w, y).eval(x);

    assert_eq!(sxy, sx_at_y, "wxy != wx(w, x).eval(y): {program:?}");
    assert_eq!(sxy, sy_at_x, "wxy != wy(w, y).eval(x): {program:?}");
});
