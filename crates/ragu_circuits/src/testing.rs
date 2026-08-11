//! Test-only circuit analysis utilities.

use ragu_core::Result;

use crate::{Circuit, FromUniformBytes};

/// Raw counts collected by a circuit synthesis analysis pass.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SynthesisCounts {
    /// The total number of gates, including the reserved SYSTEM gate.
    pub num_gates: usize,
    /// The total number of constraints, including public-output constraints
    /// and the final ONE constraint.
    pub num_constraints: usize,
}

/// Runs the production synthesis analysis pass and returns its raw counts.
pub fn synthesis_counts<F, C>(circuit: &C) -> Result<SynthesisCounts>
where
    F: FromUniformBytes<64>,
    C: Circuit<F>,
{
    let metrics = crate::metrics::eval(circuit)?;
    Ok(SynthesisCounts {
        num_gates: metrics.num_gates,
        num_constraints: metrics.num_constraints,
    })
}
