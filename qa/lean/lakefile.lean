import Lake
open Lake DSL

package Ragu where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxHeartbeats, (4000000 : Nat)⟩,
    ⟨`maxRecDepth, (2000 : Nat)⟩]

@[default_target]
lean_lib Ragu where
  -- Build every module under `Ragu/`, not just `Ragu.lean`'s import closure, so
  -- a `.lean` that no aggregator imports cannot silently escape CI.
  globs := #[`Ragu.*]

-- Prints the canonical digest of every formal instance's reimplementation;
-- CI compares the output against `cargo run -p lean_extraction -- fingerprint`.
lean_exe fingerprints where
  root := `Ragu.Fingerprint.Main

require clean from git "https://github.com/Verified-zkEVM/clean" @ "main"
