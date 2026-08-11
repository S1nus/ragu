use ragu_core::drivers::Driver;
use ragu_pasta::Fp;
use ragu_primitives::Endoscalar;

use crate::{
    driver::ExtractionDriver,
    expr::Expr,
    instance::{CircuitInstance, WireCollector},
};

pub struct EndoscalarAllocInstance;

impl CircuitInstance for EndoscalarAllocInstance {
    type Field = Fp;

    fn circuit(dr: &mut ExtractionDriver<Fp>) -> ragu_core::Result<Vec<Expr<Fp>>> {
        // MaybeKind = Empty: the u128-value closure threaded into the
        // per-bit `Boolean::alloc` calls is never executed under extraction.
        let value = ExtractionDriver::<Fp>::just(|| 0u128);
        let endo = Endoscalar::alloc(dr, value)?;
        WireCollector::collect_from(&endo)
    }
}
