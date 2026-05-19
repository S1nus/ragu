//! Polynomial-query claim collection for [`Step`](crate::step::Step) impls.
//!
//! A `Step::witness` impl receives a `pq: &mut PolyQueryClaims<...>`
//! parameter alongside its driver. Steps that need to verify a
//! polynomial-commitment opening — i.e. that the polynomial committed to by
//! `com` evaluates to `y` at point `x` — call
//! `pq.enforce_polynomial_query(dr, com, x, y)`. The framework collects the
//! resulting claims through the adapter's `Aux` for later fuse-time
//! processing. Steps that don't need polynomial-query verification simply
//! ignore the parameter.
//!
//! Steps can also call [`PolyQueryClaims::derive_challenge`] to fold an
//! arbitrary gadget's wires into a Pedersen commitment on the nested curve
//! plus a Poseidon challenge — the basic Fiat-Shamir building block.

use alloc::vec::Vec;

use ff::PrimeField;
use ragu_arithmetic::{CurveAffine, FixedGenerators, PoseidonPermutation};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::Gadget,
    maybe::Maybe,
};
use ragu_primitives::{Element, GadgetExt, Point, io::Write, poseidon::Sponge};

/// Sink for polynomial-commitment opening claims raised by a
/// [`Step::witness`](crate::step::Step::witness) invocation.
///
/// Wires aren't carried out of `witness()`, so each recorded claim's
/// `(com, x, y)` values are extracted up-front and accumulated into a single
/// `DriverValue`. The framework's adapter constructs this sink, passes it to
/// the step, then surfaces [`into_inner`](Self::into_inner) through its
/// `Aux` for later fuse-time processing.
pub struct PolyQueryClaims<'dr, D: Driver<'dr>, C: CurveAffine<Base = D::F>> {
    claims: DriverValue<D, Vec<(C, D::F, D::F)>>,
}

impl<'dr, D: Driver<'dr>, C: CurveAffine<Base = D::F>> PolyQueryClaims<'dr, D, C> {
    /// Creates a new, empty claim collector.
    pub fn new() -> Self {
        Self {
            claims: D::just(Vec::new),
        }
    }

    /// Records a claim that the polynomial committed to by `com` evaluates to
    /// `y` at the point `x`.
    pub fn enforce_polynomial_query(
        &mut self,
        _dr: &mut D,
        com: Point<'dr, D, C>,
        x: Element<'dr, D>,
        y: Element<'dr, D>,
    ) -> Result<()> {
        let triple =
            D::try_just(|| Ok((com.value().take(), *x.value().take(), *y.value().take())))?;
        let current = core::mem::replace(&mut self.claims, D::just(Vec::new));
        self.claims = current.and_then(|mut v| {
            triple.map(|t| {
                v.push(t);
                v
            })
        });
        Ok(())
    }

    /// Folds a gadget's wires into a Pedersen commitment on the nested curve
    /// and a Poseidon challenge.
    ///
    /// Returns `(com, challenge)` where `com` is a Pedersen commitment to the
    /// gadget's wires (against `pedersen_generators`, no blinding) and
    /// `challenge` is a Poseidon hash of those same wires (one squeeze from a
    /// fresh sponge keyed by `poseidon_params`).
    ///
    /// ## Contract
    ///
    /// The wire values are interpreted as `C::ScalarExt` scalars, mirroring
    /// the typed contract of
    /// [`sparse::Polynomial::commit`](ragu_circuits::polynomials::sparse::Polynomial::commit)
    /// (`fn commit<C: CurveAffine<ScalarExt = F>>`). Each wire's `D::F`
    /// witness is reinterpreted into `C::ScalarExt` via a uniform-bytes
    /// reduction; callers are responsible for ensuring wire values are valid
    /// scalars.
    ///
    /// The returned `com` is allocated from witness (same trust model as the
    /// `com` argument to [`enforce_polynomial_query`](Self::enforce_polynomial_query));
    /// binding `com` to a particular opening is the caller's responsibility.
    ///
    /// ## Panics
    ///
    /// Panics if `pedersen_generators.g().len()` is shorter than the gadget's
    /// wire count.
    pub fn derive_challenge<Gad, P, G>(
        &mut self,
        dr: &mut D,
        poseidon_params: &'dr P,
        pedersen_generators: &G,
        gadget: &Gad,
    ) -> Result<(Point<'dr, D, C>, Element<'dr, D>)>
    where
        Gad: Gadget<'dr, D>,
        Gad::Kind: Write<D::F>,
        P: PoseidonPermutation<D::F>,
        G: FixedGenerators<C>,
        D::F: PrimeField,
        C::ScalarExt: ff::FromUniformBytes<64>,
    {
        let mut wires: Vec<Element<'dr, D>> = Vec::new();
        gadget.write(dr, &mut wires)?;
        let n = wires.len();
        assert!(
            pedersen_generators.g().len() >= n,
            "derive_challenge: pedersen generators ({}) shorter than gadget wires ({})",
            pedersen_generators.g().len(),
            n,
        );

        let com_native: DriverValue<D, C> = D::try_just(|| {
            let scalars: Vec<C::ScalarExt> = wires
                .iter()
                .map(|e| {
                    let repr = e.value().as_ref().take().to_repr();
                    let mut buf = [0u8; 64];
                    let bytes = repr.as_ref();
                    let len = bytes.len().min(64);
                    buf[..len].copy_from_slice(&bytes[..len]);
                    <C::ScalarExt as ff::FromUniformBytes<64>>::from_uniform_bytes(&buf)
                })
                .collect();
            Ok(ragu_arithmetic::mul::<C, _, _>(&scalars, &pedersen_generators.g()[..n]).into())
        })?;
        let com = Point::alloc(dr, com_native)?;

        let mut sponge = Sponge::new(dr, poseidon_params);
        for w in &wires {
            sponge.absorb(dr, w)?;
        }
        let challenge = sponge.squeeze(dr)?;

        Ok((com, challenge))
    }

    /// Consumes the sink and returns the accumulated claim values.
    pub fn into_inner(self) -> DriverValue<D, Vec<(C, D::F, D::F)>> {
        self.claims
    }
}

impl<'dr, D: Driver<'dr>, C: CurveAffine<Base = D::F>> Default for PolyQueryClaims<'dr, D, C> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use ff::PrimeField;
    use ragu_arithmetic::Cycle;
    use ragu_pasta::{Fp, Pasta};
    use ragu_primitives::{Simulator, allocator::Standard};

    use super::*;

    type Sim = Simulator<Fp>;
    type NCurve = <Pasta as Cycle>::NestedCurve;
    type Scalar = <Pasta as Cycle>::ScalarField;

    fn fp_to_scalar(f: Fp) -> Scalar {
        let r = f.to_repr();
        let mut buf = [0u8; 64];
        let bytes = r.as_ref();
        buf[..bytes.len()].copy_from_slice(bytes);
        <Scalar as ff::FromUniformBytes<64>>::from_uniform_bytes(&buf)
    }

    /// `derive_challenge` on a two-`Element` tuple returns a Pedersen
    /// commitment that matches a native MSM, and a Poseidon hash that matches
    /// a fresh sponge fed the same wires in the same order.
    #[test]
    fn derive_challenge_matches_native_msm_and_poseidon() -> Result<()> {
        let params = Pasta::baked();
        let v0 = Fp::from(7u64);
        let v1 = Fp::from(11u64);

        Sim::simulate((v0, v1), |dr, witness| {
            let allocator = &mut Standard::new();
            let (a_val, b_val) = witness.cast();
            let a = Element::alloc(dr, allocator, a_val)?;
            let b = Element::alloc(dr, allocator, b_val)?;

            // Reference Poseidon: absorb the same wires into a fresh sponge.
            let mut reference_sponge = Sponge::<'_, _, <Pasta as Cycle>::CircuitPoseidon>::new(
                dr,
                Pasta::circuit_poseidon(params),
            );
            reference_sponge.absorb(dr, &a)?;
            reference_sponge.absorb(dr, &b)?;
            let expected_challenge = *reference_sponge.squeeze(dr)?.value().take();

            // Reference MSM on the nested curve, scalars reduced from D::F.
            let expected_point: NCurve = ragu_arithmetic::mul::<NCurve, _, _>(
                &[fp_to_scalar(v0), fp_to_scalar(v1)],
                &Pasta::nested_generators(params).g()[..2],
            )
            .into();

            let mut pq = PolyQueryClaims::<'_, _, NCurve>::new();
            let (com, challenge) = pq.derive_challenge(
                dr,
                Pasta::circuit_poseidon(params),
                Pasta::nested_generators(params),
                &(a, b),
            )?;

            assert_eq!(com.value().take(), expected_point);
            assert_eq!(*challenge.value().take(), expected_challenge);

            Ok(())
        })?;

        Ok(())
    }
}
