use alloc::string::ToString as _;

use ragu_arithmetic::{ff::Field as _, group::Group as _};
use ragu_core::Error;
use ragu_pasta::{Eq, Fp};

use crate::constraint::*;

#[test]
fn enforce_zero_rejects_nonzero() {
    assert!(enforce_zero(Fp::ZERO, "must be zero").is_ok());
    assert!(enforce_zero(Fp::ONE, "must be zero").is_err());
}

#[test]
fn enforce_nonzero_rejects_zero() {
    assert_eq!(
        enforce_nonzero(Fp::from(4u64), "must be nonzero").unwrap(),
        Fp::from(4u64)
    );
    assert!(enforce_nonzero(Fp::ZERO, "must be nonzero").is_err());
}

#[test]
fn invert_and_divide() {
    let a = Fp::from(4578u64);
    let b = Fp::from(372u64);

    assert_eq!(invert(a, "not invertible").unwrap(), a.invert().unwrap());
    assert!(invert(Fp::ZERO, "not invertible").is_err());

    assert_eq!(
        divide(a, b, "divide by zero").unwrap(),
        a * b.invert().unwrap()
    );
    assert!(divide(a, Fp::ZERO, "divide by zero").is_err());
}

#[test]
fn root_of_unity() {
    let err = "not a root of unity";
    // 1 is a 2^k-th root of unity for any k.
    assert!(enforce_root_of_unity(Fp::ONE, 5, err).is_ok());
    // -1 is a 2^k root of unity for k >= 1 but not k = 0.
    assert!(enforce_root_of_unity(-Fp::ONE, 1, err).is_ok());
    assert!(enforce_root_of_unity(-Fp::ONE, 0, err).is_err());
    // 0 is never a root of unity.
    assert!(enforce_root_of_unity(Fp::ZERO, 3, err).is_err());
}

#[test]
fn conditional_enforce_equal_only_binds_when_true() {
    let a = Fp::from(3u64);
    let b = Fp::from(4u64);

    // Condition false: no constraint, even for unequal operands.
    assert!(conditional_enforce_equal(false, a, b, "a == b").is_ok());

    // Condition true: equal passes, unequal fails.
    assert!(conditional_enforce_equal(true, a, a, "a == b").is_ok());
    assert!(conditional_enforce_equal(true, a, b, "a == b").is_err());
}

#[test]
fn enforce_equal_point_rejects_distinct_points() {
    let g = Eq::generator();
    assert!(enforce_equal_point(g, g, "points must match").is_ok());
    assert!(enforce_equal_point(g, g.double(), "points must match").is_err());
}

#[test]
fn enforce_equal_point_rejects_identity() {
    let err = enforce_equal_point(Eq::generator(), Eq::identity(), "points must match")
        .expect_err("identity must be rejected");
    assert!(matches!(err, Error::InvalidWitness(_)));
    assert!(err.to_string().contains("point at infinity"));

    // Not even `identity == identity`: the real gadget cannot witness it.
    assert!(enforce_equal_point(Eq::identity(), Eq::identity(), "points must match").is_err());
}
