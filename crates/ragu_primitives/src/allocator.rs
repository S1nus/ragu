//! Wire allocation.
//!
//! The core [`Driver`] trait has no notion of allocating a single wire — its
//! primitive is [`gate`](ragu_core::drivers::DriverTypes::gate), which
//! produces four wires at a time. Circuit code frequently needs standalone
//! wires, so this module introduces allocation as a separate concern.
//!
//! A gate's four wires $(A, B, C, D)$ are constrained by $A \cdot B = C$ and
//! $C \cdot D = 0$. When $B$ and $C$ are both zero the remaining wires $A$
//! and $D$ are unconstrained, so up to two independent values can be packed
//! into one gate. An [`Allocator`] manages this: it decides whether to
//! allocate a fresh gate or repurpose a leftover wire from a previous one.
//!
//! Allocation is a trait because different contexts call for different
//! strategies:
//!
//! - [`Allocator`] for `()` — stateless; allocates a full gate per wire.
//!   Simple but wasteful.
//!
//! - [`Standard`] — the standard allocator. Pairs consecutive
//!   allocations into one gate (halving gate cost) and also pools spare
//!   `Extra` tokens [`donate`](Allocator::donate)d by external gadgets
//!   (e.g. [`Boolean::alloc`](crate::Boolean::alloc)) whose $D$ wire is
//!   unconstrained. Subsequent allocations redeem pooled tokens before
//!   falling back to new gates, and self-produced spares enter the pool
//!   too.

use alloc::vec::Vec;

use ragu_arithmetic::Coeff;
use ragu_core::{Result, drivers::Driver};

/// Allocates wires on behalf of a gadget.
///
/// Implementations decide how to turn a witness-producing closure into a
/// driver wire. The simplest implementation (see the impl for `()`)
/// allocates a full multiplication gate with zeroed $b$ and $c$ wires.
/// [`Standard`] pairs consecutive allocations into a single gate by
/// stashing the [`Extra`](ragu_core::drivers::DriverTypes::Extra) token
/// that the `()` allocator discards, and also accepts donated tokens.
pub trait Allocator<'dr, D: Driver<'dr>> {
    /// Allocates a new wire whose assignment is computed by `value`.
    ///
    /// The closure follows the same purity contract as [`Driver::mul`]:
    /// it may be called zero or more times, it must be side-effect-free,
    /// and errors returned from it propagate to the caller.
    ///
    /// # Errors
    ///
    /// Returns any error produced by `value`, or any error from the driver
    /// while allocating the wire.
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire>;

    /// Accepts a spare [`Extra`](ragu_core::drivers::DriverTypes::Extra)
    /// token from an external gate whose $D$ wire is unconstrained.
    ///
    /// Allocators that can pool tokens (like [`Standard`]) store them
    /// for future [`alloc`](Self::alloc) calls. The default implementation
    /// drops the token, keeping the driver's default $D = 0$.
    fn donate(&mut self, _extra: D::Extra) {}
}

/// Stateless allocator that uses one gate per allocation.
///
/// Each call produces a multiplication gate $a \cdot 0 = 0$ and returns
/// the $a$ wire, wasting the $b$ and $c$ wires.
impl<'dr, D: Driver<'dr>> Allocator<'dr, D> for () {
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire> {
        let (a, _, _) = dr.mul(|| Ok((value()?, Coeff::Zero, Coeff::Zero)))?;
        Ok(a)
    }
}

/// Allocator that pools spare
/// [`Extra`](ragu_core::drivers::DriverTypes::Extra) tokens donated by
/// other gadgets.
///
/// Some gadgets allocate a gate whose $D$ wire is unconstrained (because
/// $C = 0$). Rather than waste that wire, they can
/// [`donate`](Self::donate) the `Extra` token to this allocator.
/// Subsequent [`alloc`](Allocator::alloc) calls redeem pooled tokens via
/// [`assign_extra`](ragu_core::drivers::DriverTypes::assign_extra) before
/// falling back to new gate allocation.
///
/// This also pairs its own gate allocations:
/// when the pool is empty and a fresh gate is needed, the spare `Extra`
/// from that gate enters the pool for the next call.
///
/// Dropping a `Standard` with tokens still in the pool is safe:
/// the driver already assigned $D = 0$ for those gates.
pub struct Standard<E> {
    pool: Vec<E>,
}

impl<E> Default for Standard<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E> Standard<E> {
    /// Creates a new `Standard` with an empty pool.
    pub const fn new() -> Self {
        Self { pool: Vec::new() }
    }
}

impl<'dr, D: Driver<'dr>> Allocator<'dr, D> for Standard<D::Extra> {
    fn alloc(&mut self, dr: &mut D, value: impl Fn() -> Result<Coeff<D::F>>) -> Result<D::Wire> {
        if let Some(extra) = self.pool.pop() {
            dr.assign_extra(extra, value)
        } else {
            let (a, _, _, extra) = dr.gate(|| Ok((value()?, Coeff::Zero, Coeff::Zero)))?;
            self.pool.push(extra);
            Ok(a)
        }
    }

    fn donate(&mut self, extra: D::Extra) {
        self.pool.push(extra);
    }
}
