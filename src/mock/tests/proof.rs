use alloc::vec::Vec;

use ragu_arithmetic::rand::{SeedableRng as _, rngs::StdRng};
use ragu_core::Result;
use ragu_pasta::{Ep, Eq, Fp, Fq};

use crate::{
    application::{Application, ApplicationBuilder},
    ctx::StepCtx,
    header::{Header, Suffix},
    proof::{PROOF_SIZE_COMPRESSED, Pcd, Proof},
    step::{Index, Step},
};

/// Header carrying one field element, as an application header would.
struct ValueHeader;

impl Header for ValueHeader {
    type Data = u64;

    const SUFFIX: Suffix = Suffix::new(0);

    fn encode(data: &Self::Data) -> (Vec<Fp>, Vec<Fq>, Vec<Ep>, Vec<Eq>) {
        (
            alloc::vec![Fp::from(*data)],
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
    }
}

/// Seed step producing a [`ValueHeader`].
struct ValueSeedStep;

impl Step for ValueSeedStep {
    type Aux<'source> = ();
    type Left = ();
    type Output = ValueHeader;
    type Right = ();
    type Witness<'source> = u64;

    const INDEX: Index = Index::new(0);

    fn witness<'source>(
        &self,
        _ctx: &mut StepCtx<'_>,
        witness: Self::Witness<'source>,
        _left: <Self::Left as Header>::Data,
        _right: <Self::Right as Header>::Data,
    ) -> Result<(<Self::Output as Header>::Data, Self::Aux<'source>)> {
        Ok((witness, ()))
    }
}

/// Application with [`ValueSeedStep`] registered.
fn value_app() -> Application {
    ApplicationBuilder::new()
        .register(ValueSeedStep)
        .expect("register")
        .finalize()
        .expect("finalize")
}

#[test]
fn round_trip() {
    let mut rng = StdRng::seed_from_u64(0);
    let app = value_app();
    let (pcd, ()) = app.seed(&mut rng, ValueSeedStep, 7u64).expect("seed");

    let bytes: [u8; PROOF_SIZE_COMPRESSED] = pcd.proof().clone().into();
    let recovered = Proof::try_from(&bytes).expect("round trip should succeed");
    assert_eq!(pcd.proof().serialize(), recovered.serialize());
}

#[test]
fn tampered_fails() {
    let mut rng = StdRng::seed_from_u64(0);
    let app = value_app();
    let (pcd, ()) = app.seed(&mut rng, ValueSeedStep, 7u64).expect("seed");

    let mut bytes: [u8; PROOF_SIZE_COMPRESSED] = pcd.proof().clone().into();
    bytes[0] ^= 0xFFu8;
    assert!(
        Proof::try_from(&bytes).is_err(),
        "tampered proof should fail"
    );
}

#[test]
fn carry_creates_pcd() {
    let mut rng = StdRng::seed_from_u64(0);
    let app = value_app();
    let (pcd, ()) = app.seed(&mut rng, ValueSeedStep, 7u64).expect("seed");

    let (proof, _data) = pcd.into_parts();
    let expected = proof.clone();
    let carried: Pcd<()> = proof.carry(());
    assert_eq!(carried.proof().serialize(), expected.serialize());
}

#[test]
fn rerandomize() {
    let mut rng = StdRng::seed_from_u64(0);
    let app = value_app();
    let (pcd, ()) = app.seed(&mut rng, ValueSeedStep, 7u64).expect("seed");

    let original = pcd.proof().clone();
    assert_eq!(original.rerand_tag, [0u8; 32]);

    let once_pcd = app.rerandomize(pcd, &mut rng).expect("rerandomize once");
    let once = once_pcd.proof().clone();

    assert_eq!(original.header_hash, once.header_hash);
    assert_eq!(original.witness_hash, once.witness_hash);
    assert_eq!(original.binding, once.binding);
    assert_ne!(original.serialize(), once.serialize());

    let twice_pcd = app
        .rerandomize(once_pcd, &mut rng)
        .expect("rerandomize twice");
    let twice = twice_pcd.proof().clone();

    assert_eq!(original.header_hash, twice.header_hash);
    assert_eq!(original.witness_hash, twice.witness_hash);
    assert_eq!(original.binding, twice.binding);
    assert_ne!(once.serialize(), twice.serialize());

    assert_ne!(original.rerand_tag, once.rerand_tag);
    assert_ne!(original.rerand_tag, twice.rerand_tag);
    assert_ne!(once.rerand_tag, twice.rerand_tag);
}
