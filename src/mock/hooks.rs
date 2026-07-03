//! Framework-side state surfaced to
//! [`Step::witness`](crate::step::Step::witness) impls — mirrors
//! `ragu_pcd::framework_hooks::FrameworkHooks`.
//!
//! Carries the polynomial-commitment opening-claim sink reached from a step
//! body through [`StepCtx`](crate::ctx::StepCtx).

use alloc::vec::Vec;

use ragu_arithmetic::group::Group as _;
use ragu_core::{Error, Result};
use ragu_pasta::{Eq, Fp};

pub type PolyQueryClaim = (Eq, Fp, Fp);

/// Container for framework-side state threaded through a
/// [`Step::witness`](crate::step::Step::witness) invocation.
#[derive(Clone, Debug, Default)]
pub struct FrameworkHooks {
    poly_query_claims: Vec<PolyQueryClaim>,
}

impl FrameworkHooks {
    #[must_use]
    pub fn new() -> Self {
        Self {
            poly_query_claims: Vec::new(),
        }
    }

    /// Records a polynomial-query opening claim. Errors if `com` is the
    /// identity, which real ragu cannot witness as a commitment `Point`.
    pub fn enforce_polynomial_query(&mut self, com: Eq, x: Fp, y: Fp) -> Result<()> {
        if bool::from(com.is_identity()) {
            return Err(Error::InvalidWitness(
                "point at infinity cannot be witnessed".into(),
            ));
        }
        self.poly_query_claims.push((com, x, y));
        Ok(())
    }

    #[must_use]
    pub fn into_outputs(self) -> Vec<PolyQueryClaim> {
        self.poly_query_claims
    }
}
