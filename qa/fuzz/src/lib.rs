//! Shared library for the `ragu_testing-fuzz` targets.
//!
//! Holds the machinery the fuzz targets are built on — the generated-program
//! [`substrate`] (op grammar, byte decoder, driver-generic synthesis, native
//! shadow, circuit wrapper) and the patcher [`recorder`] engine (recording
//! driver, repair solver, rank oracle, playback cross-check). Both live here
//! rather than in `ragu_testing` because the fuzz targets are their only
//! consumers; the `#[bin]` targets under `fuzz_targets/` depend on this lib.

pub mod recorder;
pub mod substrate;
