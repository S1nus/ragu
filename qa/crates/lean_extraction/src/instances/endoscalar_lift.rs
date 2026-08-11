use ff::{Field, WithSmallOrderMulGroup};
use ragu_arithmetic::Coeff;
use ragu_core::drivers::Driver;
use ragu_pasta::Fp;

use crate::{driver::ExtractionDriver, expr::Expr, instance::CircuitInstance};

pub struct EndoscalarLiftInstance;

impl CircuitInstance for EndoscalarLiftInstance {
    type Field = Fp;

    /// Mirrors `Endoscalar::lift` on the constraint side without going through
    /// `Endoscalar` (whose fields are private). For each of the 64 bit pairs
    /// `(n, e)`, we inline the `Boolean::and(n, e)` body — one `mul` gate plus
    /// two `enforce_equal`s — and build the output `Expression` tree to match
    /// the Lean reimpl's `stepCircuit` shape verbatim. Without this manual tree
    /// shaping, the actual `Endoscalar::lift` (which uses `acc.double() + .add`
    /// chains) would produce a left-associated tree that the formal-instance
    /// proof couldn't byte-equate against the Lean's right-grouped form.
    ///
    /// `boolean_and.rs` follows the same inlining pattern for the same reason
    /// (no public `Boolean` constructor from a bare wire).
    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // Allocate 128 input wires: bits[0..128].
        let bit_wires: Vec<Expr<Fp>> = (0..128usize)
            .map(|_| dr.alloc_input_wires(1).into_iter().next().unwrap())
            .collect();

        let zeta = Fp::ZETA;
        let one = Fp::ONE;
        let coeff_n = -Fp::from(2);
        let coeff_e = zeta - one;
        let coeff_ne = (one - zeta).double();

        // Compute `ctFinal ζ 64 = 2^65 * (ζ+1) + 2^64 - 1`, iteratively the
        // same way `Endoscalar::lift` does it.
        let mut ct = (zeta + one).double(); // 2 * (ζ + 1)
        for _ in 0..64 {
            ct = ct.double();
            ct += one;
        }
        let ct_final = ct;

        // Build acc as an Expr tree. Start at `Expression.const 0` to mirror
        // the Lean reimpl's `Fin.foldl 64 ... (Expression.const 0)`.
        let mut acc: Expr<Fp> = Expr::Const(Coeff::Zero);

        for i in 0..64usize {
            let n_wire = &bit_wires[2 * i];
            let e_wire = &bit_wires[2 * i + 1];

            // Inline `Boolean::and(n, e)`: one mul gate (`a * b = c`) plus two
            // `enforce_equal`s binding the gate's `a`/`b` wires to `n` and `e`.
            // The output `ne` is the gate's `c` wire.
            let (mul_a, mul_b, mul_c) = dr.mul(|| Ok((Coeff::Zero, Coeff::Zero, Coeff::Zero)))?;
            dr.enforce_equal(&mul_a, n_wire)?;
            dr.enforce_equal(&mul_b, e_wire)?;
            let ne_wire = mul_c;

            // Build the Lean-shaped `stepCircuit` update:
            //   acc' = (Const 2 * acc) + ((Const coeff_n * n + Const coeff_e * e) + Const coeff_ne * ne)
            let term_acc = Expr::Mul(Box::new(Expr::Const(Coeff::Two)), Box::new(acc));
            let term_n = Expr::Mul(
                Box::new(Expr::Const(Coeff::Arbitrary(coeff_n))),
                Box::new(n_wire.clone()),
            );
            let term_e = Expr::Mul(
                Box::new(Expr::Const(Coeff::Arbitrary(coeff_e))),
                Box::new(e_wire.clone()),
            );
            let term_ne = Expr::Mul(
                Box::new(Expr::Const(Coeff::Arbitrary(coeff_ne))),
                Box::new(ne_wire),
            );
            let inner = Expr::Add(
                Box::new(Expr::Add(Box::new(term_n), Box::new(term_e))),
                Box::new(term_ne),
            );
            acc = Expr::Add(Box::new(term_acc), Box::new(inner));
        }

        // Final output: `acc + Const ct_final` (mirrors the trailing
        // `return acc + Expression.const (ctFinal ζ 64)` in the Lean reimpl).
        let result = Expr::Add(
            Box::new(acc),
            Box::new(Expr::Const(Coeff::Arbitrary(ct_final))),
        );

        Ok(vec![result])
    }
}
