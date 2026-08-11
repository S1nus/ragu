import Clean.Circuit
import Clean.Circuit.Loops
import Ragu.Circuits.Boolean.Alloc

namespace Ragu.Circuits.Endoscalar.Alloc
variable {p : ℕ} [Fact p.Prime]

/-- `Endoscalar::alloc(value)` allocates 128 boolean wires, each carrying
the corresponding bit of the 128-bit prover hint `value`. Mirrors the
Rust loop `for i in 0..Uendo::BITS { Boolean::alloc((value >> i) & 1) }`
in `crates/ragu_primitives/src/endoscalar.rs::Endoscalar::alloc`.

`Uendo` is `pub use u128 as Uendo` in `crates/ragu_arithmetic/src/lib.rs:102`,
so `Uendo::BITS = u128::BITS = 128`. This Lean reimpl is monomorphic at 128 —
no polymorphism needed.

Extraction instance: `qa/crates/lean_extraction/src/instances/endoscalar_alloc.rs`
(which drives the real `Endoscalar::alloc` directly). Tied to this reimpl by the
fingerprint equivalence check via the formal instance in
`qa/lean/Ragu/Instances/Endoscalar/Alloc.lean`. -/
def main (value : ProverEnvironment (F p) → BitVec 128)
    : Circuit (F p) (Vector (Expression (F p)) 128) :=
  Circuit.mapFinRange 128 fun (i : Fin 128) =>
    Boolean.Alloc.circuit (fun env => (value env)[i.val])

def Assumptions (_input : Unit) (_data : ProverData (F p)) := True

def ProverAssumptions (_input : BitVec 128) (_data : ProverData (F p))
    (_hint : ProverHint (F p)) := True

/-- The verifier learns that all 128 output wires are boolean. -/
def Spec (_input : Unit) (out : Vector (F p) 128) (_data : ProverData (F p)) :=
  ∀ i : Fin 128, IsBool out[i]

/-- The honest prover's wire `i` holds bit `i` of the 128-bit hint
(LSB-first, matching the Rust `(value >> i) & 1`). Callers use this to chain
the allocated endoscalar's value through composed completeness proofs. -/
def ProverSpec (input : BitVec 128) (out : Vector (F p) 128) (_hint : ProverHint (F p)) :=
  ∀ i : Fin 128, out[i] = if input[i.val] then 1 else 0

instance elaborated
    : ElaboratedCircuit (F p) (Unconstrained (BitVec 128)) (fields 128) where
  main
  localLength _ := 128 * 3
  localLength_eq _ _ := by
    simp [main, circuit_norm, Boolean.Alloc.circuit]
  subcircuitsConsistent _ _ := by
    simp [main, circuit_norm, Boolean.Alloc.circuit]

theorem soundness
    : GeneralFormalCircuit.WithHint.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Boolean.Alloc.circuit, Boolean.Alloc.Assumptions, Boolean.Alloc.Spec]
  exact h_holds

theorem completeness
    : GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
        ProverAssumptions ProverSpec := by
  circuit_proof_start [Boolean.Alloc.circuit, Boolean.Alloc.Assumptions, Boolean.Alloc.Spec,
    Boolean.Alloc.ProverAssumptions, Boolean.Alloc.ProverSpec]
  intro i
  exact (h_env i).2

def circuit : GeneralFormalCircuit.WithHint (F p) (Unconstrained (BitVec 128)) (fields 128) :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    ProverAssumptions := ProverAssumptions,
    ProverSpec := ProverSpec,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Endoscalar.Alloc
