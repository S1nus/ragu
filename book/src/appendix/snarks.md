# SNARKs

A **succinct non-interactive argument of knowledge (SNARK)** is a
cryptographic proof system that allows a prover to convince a verifier
that a statement is true, without revealing any information beyond the
validity of the statement itself. The key properties are:

- **Succinct**: the proof is small (much smaller than the computation
  it attests to) and fast to verify.
- **Non-interactive**: the prover sends a single message to the
  verifier; no back-and-forth is needed.
- **Argument of knowledge**: the prover not only demonstrates that a
  valid witness _exists_, but that they actually _know_ one.

SNARKs are the building blocks of
[proof-carrying data](../concepts/pcd.md): each step in a PCD computation
produces a SNARK that attests to the correctness of that step, and
recursive composition allows these proofs to reference each other.

## NARKs

A **NARK** (non-interactive argument of knowledge) relaxes the
succinctness requirement on the full proof. In Ragu's split form, the
proof has two parts: a succinct _instance_ that the verifier checks, and
a potentially linear-size _witness_ that only the prover and decider
need. The instance is small and fast to verify; the witness is not.

This relaxation matters for recursive proof composition. A full SNARK
requires the prover to produce a succinct proof at every recursive step,
which is expensive. A NARK defers that cost: the prover carries the
proof witness forward in uncompressed form and only compresses at the
boundary where the proof leaves the recursive pipeline. The
[split-accumulation](../protocol/core/accumulation/index.md) technique
makes this practical — the recursive verifier only processes the
succinct instance, and the witness is accumulated without compression.

Ragu's internal proof system is a NARK. Its instance contains
commitments, evaluation claims, and the IPA accumulator state. Its
witness contains the full polynomial vectors and auxiliary data needed
by the decider. When proofs leave the recursive pipeline, they can be
[compressed](../concepts/pcd.md) to a succinct form for transmission.

## Trusted setup

Some SNARKs require a _trusted setup_, a one-time ceremony that
produces structured reference parameters from secret randomness. If
that randomness leaks, an adversary can forge proofs.

|                  | Pairing-based (Groth16, PLONK+KZG)  | IPA-based (Bulletproofs, Halo, Ragu)        |
|------------------|--------------------------------------|---------------------------------------------|
| **Setup**        | Trusted ceremony                     | Transparent (no trust)                      |
| **Opening proof** | Constant size                       | Logarithmic size                             |
| **Verification** | Constant time                        | Linear time (deferred via accumulation)     |

Ragu targets deployment in Zcash as part of
[Project Tachyon](https://tachyon.z.cash/), where avoiding a
trusted setup is a strong design goal. The Pasta curves are not
pairing-friendly, which rules out pairing-based commitments,
so Ragu uses IPA-based commitments throughout. Ragu's internal split
form still carries a linear-size witness until compression.
