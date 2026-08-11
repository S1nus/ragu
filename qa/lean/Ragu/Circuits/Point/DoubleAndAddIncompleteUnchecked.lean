import Clean.Circuit
import Clean.Utils.Primes
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Element.Divide
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.DoubleAndAddIncompleteUnchecked
variable {p : ℕ} [Fact p.Prime]

/-- Two input points. Unlike `Point.DoubleAndAddIncomplete`, there is no
inverse hint: this variant models `Point::double_and_add_incomplete` against
an *unchecked* `NonzeroBank` (`NonzeroBank::new_unchecked()`), where the two
bank folds and the scope-end discharge emit no constraints. -/
structure Inputs (F : Type) where
  P1 : Spec.Point F  -- the point to be doubled (Rust's `self`)
  P2 : Spec.Point F  -- the point to be added once (Rust's `other`)
deriving ProvableStruct

/-- `Point::double_and_add_incomplete` called with an unchecked bank, as
`Endoscalar::group_scale` does. Computes `2·P1 + P2` via the zcash trick:

  - λ₁ = (y₂ - y₁) / (x₂ - x₁) — slope through P1 and P2 (divide #1).
  - x_r = λ₁² - x₁ - x₂ — x-coord of P1 + P2.
  - λ₂ = 2y₁ / (x₁ - x_r) - λ₁ — slope through (P1 + P2) and P1 (divide #2).
  - x_s = λ₂² - x_r - x₁; y_s = λ₂ (x₁ - x_s) - y₁.

Nothing in the constraint system forces the two distinct-x conditions; they
are caller obligations (`Assumptions`), justified externally (for
`group_scale`, by the Appendix C no-collision argument of BGH19). -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var Spec.Point (F p)) := do
  let ⟨⟨x_p, y_p⟩, ⟨x_q, y_q⟩⟩ := input

  -- λ₁ = (y_q - y_p) / (x_q - x_p)
  let lambda_1 ← Element.Divide.circuit ⟨y_q - y_p, x_q - x_p⟩

  -- x_r = λ₁² - x_p - x_q
  let lambda_1_sq ← Element.Square.circuit lambda_1
  let x_r := lambda_1_sq - x_p - x_q

  -- λ₂_half = 2 y_p / (x_p - x_r)
  let lambda_2_half ← Element.Divide.circuit ⟨y_p + y_p, x_p - x_r⟩
  let lambda_2 := lambda_2_half - lambda_1

  -- x_s = λ₂² - x_r - x_p
  let lambda_2_sq ← Element.Square.circuit lambda_2
  let x_s := lambda_2_sq - x_r - x_p

  -- y_s = λ₂ (x_p - x_s) - y_p
  let y_term ← Element.Mul.circuit ⟨lambda_2, x_p - x_s⟩
  let y_s := y_term - y_p

  return ⟨x_s, y_s⟩

/-- Caller obligations: both points on curve, and the full non-degeneracy of
the `(P1 + P2) + P1` chain — both incomplete additions succeed. The circuit
does *not* enforce either distinct-x condition. -/
def Assumptions (curveParams : Spec.CurveParams p) (input : Inputs (F p)) :=
  input.P1.isOnCurve curveParams ∧
  input.P2.isOnCurve curveParams ∧
  ∃ r out, input.P1.add_incomplete input.P2 = some r ∧
    r.add_incomplete input.P1 = some out

/-- Same contract as the discharging variant: the output is `2·P1 + P2`,
stated via the two affine additions. -/
def Spec (curveParams : Spec.CurveParams p)
    (input : Inputs (F p)) (output : Spec.Point (F p)) :=
  ∃ r, input.P1.add_incomplete input.P2 = some r ∧
    r.add_incomplete input.P1 = some output ∧
    output.isOnCurve curveParams

instance elaborated : ElaboratedCircuit (F p) Inputs Spec.Point where
  main
  -- divide1 (3) + square1 (3) + divide2 (3) + square2 (3) + mul_for_y (3) = 15
  localLength _ := 15

theorem soundness (curveParams : Spec.CurveParams p) :
    Soundness (F p) elaborated (Assumptions curveParams) (Spec curveParams) := by
  circuit_proof_start [Element.Divide.circuit, Element.Divide.Assumptions, Element.Divide.Spec,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec]
  obtain ⟨h_curve1, h_curve2, r0, out0, h_add1, h_add2⟩ := h_assumptions
  obtain ⟨h_div1, h_sq1, h_div2, h_sq2, h_yterm⟩ := h_holds
  -- First distinct-x condition, from the assumption chain's first `some`.
  have h_x_ne : input_P1_x ≠ input_P2_x := by
    intro h
    rw [Spec.Point.add_incomplete, if_pos h] at h_add1
    exact Option.some_ne_none _ h_add1.symm
  have h_sub_ne : input_P2_x + -input_P1_x ≠ 0 := by
    rw [← sub_eq_add_neg]
    exact sub_ne_zero.mpr (Ne.symm h_x_ne)
  have h_delta : env.get i₀ = (input_P2_y + -input_P1_y) / (input_P2_x + -input_P1_x) :=
    h_div1 (Or.inl h_sub_ne)
  -- Pin the assumption's intermediate point to extract the second condition.
  have h_r0 : r0 = ⟨((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
        input_P1_x - input_P2_x,
      ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) *
        (input_P1_x - (((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
          input_P1_x - input_P2_x)) - input_P1_y⟩ := by
    simp only [Spec.Point.add_incomplete, if_neg h_x_ne, Option.some.injEq] at h_add1
    exact h_add1.symm
  have h_rx_ne : ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
      input_P1_x - input_P2_x ≠ input_P1_x := by
    intro h
    rw [h_r0] at h_add2
    rw [Spec.Point.add_incomplete, if_pos h] at h_add2
    exact Option.some_ne_none _ h_add2.symm
  -- Second distinct-x condition, in circuit-wire form.
  have h_xpr_ne : input_P1_x + -(env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x) ≠ 0 := by
    rw [h_sq1, h_delta]
    intro h
    apply h_rx_ne
    linear_combination -h
  have h_r_ne_xp : (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x) ≠ input_P1_x :=
    fun h => h_xpr_ne (by rw [h]; ring)
  have h_diff_ne : input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x) ≠ 0 := by
    rw [sub_eq_add_neg]; exact h_xpr_ne
  have h_lam2half : env.get (i₀ + 3 + 3) =
      (input_P1_y + input_P1_y) /
        (input_P1_x + -(env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) :=
    h_div2 (Or.inl h_xpr_ne)
  have h_lam2_mul : env.get (i₀ + 3 + 3) *
      (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) =
      input_P1_y + input_P1_y := by
    rw [sub_eq_add_neg, h_lam2half, div_mul_cancel₀ _ h_xpr_ne]
  have h_slope :
      (input_P1_y - (env.get i₀ *
            (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) - input_P1_y)) /
          (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) =
        env.get (i₀ + 3 + 3) - env.get i₀ := by
    rw [show input_P1_y - (env.get i₀ *
                (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) - input_P1_y) =
            input_P1_y + input_P1_y - env.get i₀ *
                (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) by ring]
    rw [← h_lam2_mul,
        show env.get (i₀ + 3 + 3) *
              (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) -
            env.get i₀ * (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) =
          (env.get (i₀ + 3 + 3) - env.get i₀) *
            (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) by ring]
    exact mul_div_cancel_right₀ _ h_diff_ne
  -- The intermediate point r = P1 + P2, on the circuit's wires.
  have h_add_eq1 :
      ({ x := input_P1_x, y := input_P1_y } : Spec.Point (F p)).add_incomplete
          { x := input_P2_x, y := input_P2_y } =
        some { x := env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x,
               y := env.get i₀ *
                      (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) -
                    input_P1_y } := by
    simp only [Spec.Point.add_incomplete, if_neg h_x_ne, Option.some.injEq,
      Spec.Point.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [h_sq1, h_delta]; ring
    · rw [h_sq1, h_delta]; ring
  have h_add_eq2 :
      ({ x := env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x,
         y := env.get i₀ *
                (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) -
              input_P1_y } :
            Spec.Point (F p)).add_incomplete { x := input_P1_x, y := input_P1_y } =
        some { x := env.get (i₀ + 3 + 3 + 3 + 2) +
                      -(env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x) + -input_P1_x,
               y := env.get (i₀ + 3 + 3 + 3 + 3 + 2) + -input_P1_y } := by
    simp only [Spec.Point.add_incomplete, if_neg h_r_ne_xp, Option.some.injEq,
      Spec.Point.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [h_slope, h_sq2]; ring
    · rw [h_slope, h_yterm, h_sq2]
      linear_combination (-h_lam2_mul)
  refine ⟨_, h_add_eq1, h_add_eq2, ?_⟩
  have h_r_curve := by
    simpa [h_add_eq1] using Lemmas.add_incomplete_preserves_membership
      { x := input_P1_x, y := input_P1_y } { x := input_P2_x, y := input_P2_y }
      curveParams h_x_ne h_curve1 h_curve2
  simpa [h_add_eq2] using Lemmas.add_incomplete_preserves_membership
    { x := env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x,
      y := env.get i₀ *
            (input_P1_x - (env.get (i₀ + 3 + 2) + -input_P1_x + -input_P2_x)) - input_P1_y }
    { x := input_P1_x, y := input_P1_y } curveParams h_r_ne_xp h_r_curve h_curve1

theorem completeness (curveParams : Spec.CurveParams p) :
    Completeness (F p) elaborated (Assumptions curveParams) := by
  circuit_proof_start [Element.Divide.circuit, Element.Divide.ProverAssumptions,
    Element.Divide.Assumptions, Element.Divide.Spec,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions]
  obtain ⟨_, _, r0, out0, h_add1, h_add2⟩ := h_assumptions
  obtain ⟨h_div1_env, h_sq1_env, _⟩ := h_env
  have h_x_ne : input_P1_x ≠ input_P2_x := by
    intro h
    rw [Spec.Point.add_incomplete, if_pos h] at h_add1
    exact Option.some_ne_none _ h_add1.symm
  have h_sub_ne : input_P2_x + -input_P1_x ≠ 0 := by
    rw [← sub_eq_add_neg]
    exact sub_ne_zero.mpr (Ne.symm h_x_ne)
  have h_delta : env.get i₀ = (input_P2_y + -input_P1_y) / (input_P2_x + -input_P1_x) :=
    h_div1_env h_sub_ne (Or.inl h_sub_ne)
  have h_r0 : r0 = ⟨((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
        input_P1_x - input_P2_x,
      ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) *
        (input_P1_x - (((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
          input_P1_x - input_P2_x)) - input_P1_y⟩ := by
    simp only [Spec.Point.add_incomplete, if_neg h_x_ne, Option.some.injEq] at h_add1
    exact h_add1.symm
  have h_rx_ne : ((input_P2_y - input_P1_y) / (input_P2_x - input_P1_x)) ^ 2 -
      input_P1_x - input_P2_x ≠ input_P1_x := by
    intro h
    rw [h_r0] at h_add2
    rw [Spec.Point.add_incomplete, if_pos h] at h_add2
    exact Option.some_ne_none _ h_add2.symm
  refine ⟨h_sub_ne, ?_⟩
  rw [h_sq1_env, h_delta]
  intro h
  apply h_rx_ne
  linear_combination -h

def circuit (curveParams : Spec.CurveParams p) : FormalCircuit (F p) Inputs Spec.Point :=
  { elaborated with
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Point.DoubleAndAddIncompleteUnchecked
