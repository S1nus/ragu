import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.Divide
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.AddIncompleteUnchecked
variable {p : ℕ} [Fact p.Prime]

/-- Two input points. Unlike `Point.AddIncomplete`, there is no inverse hint:
this variant models `Point::add_incomplete` against an *unchecked*
`NonzeroBank` (`NonzeroBank::new_unchecked()`), where the bank fold and the
scope-end discharge emit no constraints. -/
structure Inputs (F : Type) where
  P1 : Spec.Point F
  P2 : Spec.Point F
deriving ProvableStruct

/-- `Point::add_incomplete` called with an unchecked bank, as
`Endoscalar::group_scale` does: just the affine-addition gates.

  - delta = (y₂ - y₁) / (x₂ - x₁) — the bank fold on `(x₂ - x₁)` is a no-op.
  - x₃ = delta² - x₁ - x₂
  - y₃ = delta · (x₁ - x₃) - y₁

Nothing in the constraint system forces `x₁ ≠ x₂`; that non-degeneracy is a
caller obligation (`Assumptions`), justified externally (for `group_scale`,
by the Appendix C no-collision argument of BGH19). -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ := input

  -- delta = (y2 - y1) / (x2 - x1)
  let delta ← Element.Divide.circuit ⟨y2 - y1, x2 - x1⟩

  -- x3 = delta² - x1 - x2
  let delta_sq ← Element.Square.circuit delta
  let x3 := delta_sq - x1 - x2

  -- y3 = delta · (x1 - x3) - y1
  let y_term ← Element.Mul.circuit ⟨delta, x1 - x3⟩
  let y3 := y_term - y1

  return ⟨x3, y3⟩

/-- Caller obligations: both points on curve, and the distinct-x condition the
circuit does *not* enforce. -/
def Assumptions (curveParams : Spec.CurveParams p) (input : Inputs (F p)) :=
  input.P1.isOnCurve curveParams ∧
  input.P2.isOnCurve curveParams ∧
  input.P1.x ≠ input.P2.x

def Spec (curveParams : Spec.CurveParams p)
    (input : Inputs (F p)) (output : Spec.Point (F p)) :=
  input.P1.add_incomplete input.P2 = some output ∧
  output.isOnCurve curveParams

instance elaborated : ElaboratedCircuit (F p) Inputs Spec.Point where
  main
  -- divide (3) + square (3) + mul_for_y (3) = 9 wires
  localLength _ := 9

theorem soundness (curveParams : Spec.CurveParams p) :
    Soundness (F p) elaborated (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start [Element.Divide.circuit, Element.Divide.Assumptions, Element.Divide.Spec,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨h_curve1, h_curve2, h_x_ne⟩ := h_assumptions
  obtain ⟨h_div, h_sq, h_y_term⟩ := h_holds
  have h_sub_ne : input_P2_x + -input_P1_x ≠ 0 := by
    rw [← sub_eq_add_neg]
    exact sub_ne_zero.mpr (Ne.symm h_x_ne)
  have h_delta : env.get i₀ = (input_P2_y + -input_P1_y) / (input_P2_x + -input_P1_x) :=
    h_div (Or.inl h_sub_ne)
  have h_add_eq :
      Spec.Point.add_incomplete { x := input_P1_x, y := input_P1_y }
          { x := input_P2_x, y := input_P2_y } =
        some { x := env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x,
               y := env.get (i₀ + 3 + 3 + 2) + -input_P1_y } := by
    simp only [Spec.Point.add_incomplete, if_neg h_x_ne, Option.some.injEq,
      Spec.Point.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [h_sq, h_delta]; ring
    · rw [h_y_term, h_sq, h_delta]; ring
  refine ⟨h_add_eq, ?_⟩
  simpa [h_add_eq] using
    Lemmas.add_incomplete_preserves_membership
      ⟨input_P1_x, input_P1_y⟩ ⟨input_P2_x, input_P2_y⟩ curveParams h_x_ne h_curve1 h_curve2

theorem completeness (curveParams : Spec.CurveParams p) :
    Completeness (F p) elaborated (Assumptions curveParams) := by
  circuit_proof_start [Element.Divide.circuit, Element.Divide.ProverAssumptions,
    Element.Square.circuit, Element.Square.Assumptions,
    Element.Mul.circuit, Element.Mul.Assumptions]
  obtain ⟨_, _, h_x_ne⟩ := h_assumptions
  rw [← sub_eq_add_neg]
  exact sub_ne_zero.mpr (Ne.symm h_x_ne)

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Inputs Spec.Point :=
  { elaborated with
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Point.AddIncompleteUnchecked
