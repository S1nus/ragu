//! Mock equivalents of ragu's enforce-only field-element gadget utilities.
//!
//! Generic over the field `F`, mirroring real ragu's field-generic gadgets.

use ragu_arithmetic::{ff::Field, group::Group};
use ragu_core::{Error, Result};

/// Enforces `a == 0`. Mirrors `Element::enforce_zero`; returns
/// `Err(Error::InvalidWitness(err))` where the real constraint would be
/// unsatisfiable (`a` nonzero).
pub fn enforce_zero<F: Field>(a: F, err: &'static str) -> Result<()> {
    if bool::from(a.is_zero()) {
        Ok(())
    } else {
        Err(Error::InvalidWitness(err.into()))
    }
}

/// Enforces `a != 0`, returning `a`. Mirrors `Element::enforce_nonzero`, which
/// fails to synthesize for a zero value.
pub fn enforce_nonzero<F: Field>(a: F, err: &'static str) -> Result<F> {
    if bool::from(a.is_zero()) {
        Err(Error::InvalidWitness(err.into()))
    } else {
        Ok(a)
    }
}

/// Multiplicative inverse $a^{-1}$. Mirrors `Element::invert`, which is
/// unsatisfiable for a zero value.
pub fn invert<F: Field>(a: F, err: &'static str) -> Result<F> {
    Option::from(a.invert()).ok_or_else(|| Error::InvalidWitness(err.into()))
}

/// `a / divisor`. Mirrors `Element::divide`; errors on a zero divisor (real
/// ragu takes a `Nonzero`, pushing this precondition to the type).
pub fn divide<F: Field>(a: F, divisor: F, err: &'static str) -> Result<F> {
    invert(divisor, err).map(|inv| a * inv)
}

/// Enforces $a^{2^k} = 1$. Mirrors `Element::enforce_root_of_unity`.
pub fn enforce_root_of_unity<F: Field>(a: F, k: u32, err: &'static str) -> Result<()> {
    let mut value = a;
    for _ in 0..k {
        value = value.square();
    }
    if value == F::ONE {
        Ok(())
    } else {
        Err(Error::InvalidWitness(err.into()))
    }
}

/// Conditionally enforces `a == b`: when `cond` is true, requires `a == b`; when
/// false, imposes nothing. Mirrors `Boolean::conditional_enforce_equal`;
/// returns `Err(Error::InvalidWitness(err))` where the real constraint would be
/// unsatisfiable (`cond` true and `a != b`).
pub fn conditional_enforce_equal<F: Field>(
    cond: bool,
    a: F,
    b: F,
    err: &'static str,
) -> Result<()> {
    if cond && a != b {
        Err(Error::InvalidWitness(err.into()))
    } else {
        Ok(())
    }
}

/// Enforces `a == b` for two curve points. Mirrors `Point::enforce_equal` (real
/// ragu's derived `GadgetEquals` for `Point`, which constrains the coordinates
/// equal); returns `Err(Error::InvalidWitness(err))` where those constraints
/// would be unsatisfiable (`a != b`).
///
/// An identity input errors instead, since real ragu cannot witness it as a
/// `Point`.
pub fn enforce_equal_point<C: Group>(a: C, b: C, err: &'static str) -> Result<()> {
    if bool::from(a.is_identity()) || bool::from(b.is_identity()) {
        return Err(Error::InvalidWitness(
            "point at infinity cannot be witnessed".into(),
        ));
    }
    if a == b {
        Ok(())
    } else {
        Err(Error::InvalidWitness(err.into()))
    }
}
