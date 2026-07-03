//! Context object threaded through
//! [`Step::witness`](crate::step::Step::witness)
//! — mirrors `ragu_pcd::step::StepCtx`.
//!
//! Real ragu's `StepCtx` bundles the circuit driver with the framework hooks.
//! The mock has no driver, so it carries only the [`FrameworkHooks`] claim sink
//! and exposes the two hooks a step body reaches for: recording
//! polynomial-query opening claims and deriving Fiat-Shamir challenges.

use blake2b_simd::Params;
use ragu_arithmetic::{
    ff::FromUniformBytes as _,
    group::{Group as _, GroupEncoding as _},
};
use ragu_core::{Error, Result};
use ragu_pasta::{Eq, Fp};

use crate::hooks::FrameworkHooks;

const CHALLENGE_LEN: usize = 64;

/// Framework-side state threaded through
/// [`Step::witness`](crate::step::Step::witness).
pub struct StepCtx<'a> {
    hooks: &'a mut FrameworkHooks,
}

impl<'a> StepCtx<'a> {
    pub(crate) fn new(hooks: &'a mut FrameworkHooks) -> Self {
        Self { hooks }
    }

    /// Records a polynomial-query opening claim. Errors if `com` is the
    /// identity, which real ragu cannot witness as a commitment `Point`.
    pub fn enforce_poly_query(&mut self, com: Eq, x: Fp, y: Fp) -> Result<()> {
        self.hooks.enforce_polynomial_query(com, x, y)
    }

    /// Derives a Fiat-Shamir challenge from `commitments`. Errors on an
    /// identity commitment, which real ragu could not have absorbed as a
    /// `Point`.
    pub fn derive_challenge(&mut self, commitments: &[Eq]) -> Result<Fp> {
        for com in commitments {
            if bool::from(com.is_identity()) {
                return Err(Error::InvalidWitness(
                    "point at infinity cannot be witnessed".into(),
                ));
            }
        }
        let mut state = Params::new()
            .hash_length(CHALLENGE_LEN)
            .personal(b"MkRagu_Challng_\0")
            .to_state();
        for com in commitments {
            state.update(com.to_bytes().as_ref());
        }
        let mut wide = [0u8; CHALLENGE_LEN];
        wide.copy_from_slice(state.finalize().as_bytes());
        Ok(Fp::from_uniform_bytes(&wide))
    }
}
