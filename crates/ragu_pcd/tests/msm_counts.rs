//! Counts MSM invocations and element counts during a single fuse() call.
//! Run with: cargo test -p ragu_pcd --features count-msm --test msm_counts -- --nocapture

#[cfg(feature = "count-msm")]
#[test]
fn count_msm_in_fuse() -> ragu_core::Result<()> {
    use ragu_arithmetic::Cycle;
    use ragu_circuits::polynomials::ProductionRank;
    use ragu_pasta::{Fp, Pasta};
    use ragu_pcd::ApplicationBuilder;
    use ragu_testing::pcd::nontrivial::{Hash2, WitnessLeaf};
    use rand::SeedableRng;
    use rand::rngs::StdRng;

    let pasta = Pasta::baked();
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        })?
        .register(Hash2 {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        })?
        .finalize(pasta)?;

    let mut rng = StdRng::seed_from_u64(1234);

    let (leaf1, _) = app.seed(
        &mut rng,
        WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        Fp::from(42u64),
    )?;

    let (leaf2, _) = app.seed(
        &mut rng,
        WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        Fp::from(43u64),
    )?;

    // Reset counters before fuse.
    ragu_arithmetic::msm_histogram::reset();
    ragu_arithmetic::MSM_CALL_COUNT.store(0, core::sync::atomic::Ordering::Relaxed);
    ragu_arithmetic::MSM_TOTAL_ELEMENTS.store(0, core::sync::atomic::Ordering::Relaxed);

    let (node, _) = app.fuse(
        &mut rng,
        Hash2 {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        (),
        leaf1,
        leaf2,
    )?;
    assert!(app.verify(&node, &mut rng)?);

    let calls = ragu_arithmetic::MSM_CALL_COUNT.load(core::sync::atomic::Ordering::Relaxed);
    let total = ragu_arithmetic::MSM_TOTAL_ELEMENTS.load(core::sync::atomic::Ordering::Relaxed);
    let sizes = ragu_arithmetic::msm_histogram::drain();

    eprintln!("\n=== MSM calls during fuse() ===");
    eprintln!("Total calls: {calls}");
    eprintln!("Total elements across all calls: {total}");
    eprintln!("Average elements per call: {}", total / calls.max(1));
    eprintln!("\nPer-call sizes:");
    for (i, n) in sizes.iter().enumerate() {
        eprintln!("  call {i:>3}: n={n}");
    }

    Ok(())
}
