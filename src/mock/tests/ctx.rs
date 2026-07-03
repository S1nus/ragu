use alloc::string::ToString as _;

use ragu_arithmetic::{ff::Field as _, group::Group as _};
use ragu_core::Error;
use ragu_pasta::{Eq, Fp};

use crate::{ctx::StepCtx, hooks::FrameworkHooks, polynomial::Polynomial};

#[test]
fn enforce_poly_query_rejects_identity() {
    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);

    assert!(
        ctx.enforce_poly_query(Eq::generator(), Fp::ONE, Fp::ONE)
            .is_ok()
    );

    let err = ctx
        .enforce_poly_query(Eq::identity(), Fp::ONE, Fp::ONE)
        .expect_err("identity commitment must be rejected");
    assert!(matches!(err, Error::InvalidWitness(_)));
    assert!(err.to_string().contains("point at infinity"));
}

#[test]
fn derive_challenge_rejects_identity() {
    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);

    assert!(ctx.derive_challenge(&[Eq::generator()]).is_ok());

    let err = ctx
        .derive_challenge(&[Eq::generator(), Eq::identity()])
        .expect_err("identity commitment must be rejected");
    assert!(matches!(err, Error::InvalidWitness(_)));
}

#[test]
fn zero_polynomial_commits_to_identity_but_cannot_be_witnessed() {
    // Commit is permissive, exactly like real ragu's unblinded MSM…
    let com = Polynomial::from_coeffs(&[Fp::ZERO]).commit();
    assert!(bool::from(com.is_identity()));

    // …the failure happens where the commitment enters the proof system,
    // mirroring `Point::alloc` at the real pcd boundary.
    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(ctx.enforce_poly_query(com, Fp::ONE, Fp::ZERO).is_err());
}
