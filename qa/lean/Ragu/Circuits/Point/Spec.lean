import Clean.Circuit
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Ragu.Core

namespace Ragu.Circuits.Point.Spec
open Core.Primes
variable {p : ℕ} [Fact p.Prime]

structure Point (F : Type) where
  x : F
  y : F
deriving ProvableStruct

/--
  Short Weierstrass curves with a = 0.

  `h_small_order` is a proof that the element ζ has order 3 in the base field
-/
structure CurveParams (base_p : ℕ) where
  b : F base_p
  ζ : F base_p
  h_small_order : ζ^3 = 1

def Point.isOnCurve (point : Point (F p)) (curveParams : CurveParams p) : Prop :=
  point.y^2 = point.x^3 + curveParams.b

def CurveParams.noOrderTwoPoints (curveParams : CurveParams p) : Prop :=
  (∀ point : Spec.Point (F p), (point.isOnCurve curveParams) → point.y ≠ 0)

def Point.negate (point : Point (F p)) : Point (F p) :=
  {
    x := point.x,
    y := -point.y
  }

def Point.endo (point : Point (F p)) (curveParams : CurveParams p) : Point (F p) :=
  {
    x := curveParams.ζ * point.x,
    y := point.y
  }

/--
  Add two affine point

  Returns some point only if the result is affine as well, otherwise return none
-/
def Point.add_incomplete (point_1 : Point (F p)) (point_2 : Point (F p)) : Option (Point (F p)) :=
  -- a / 0 is defined to be 0 for fields, therefore to make the spec precise
  -- we return None if the x coordinates of the points are equal
  if point_1.x = point_2.x then none else
  let lambda := (point_2.y - point_1.y) / (point_2.x - point_1.x)
  let x3 := lambda^2 - point_1.x - point_2.x
  some {
    x := x3,
    y := lambda * (point_1.x - x3) - point_1.y
  }

def Point.double (point : Point (F p)) : Option (Point (F p)) :=
  -- a / 0 is defined to be 0 for fields, therefore to make the spec precise
  -- we return None if point.y is zero
  if point.y = 0 then none else
  let lambda := (3 * point.x^2) / (2 * point.y)
  let x2 := lambda^2 - 2*point.x
  some {
    x := x2,
    y := lambda * (point.x - x2) - point.y
  }

-- concrete pasta curves parameters
def EpAffineParams: Circuits.Point.Spec.CurveParams Core.Primes.p :=
{
  b := 5,
  ζ := 0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab9,
  h_small_order := by native_decide
}

def EqAffineParams: Circuits.Point.Spec.CurveParams Core.Primes.q :=
{
  b := 5,
  ζ := 0x6819a58283e528e511db4d81cf70f5a0fed467d47c033af2aa9d2e050aa0e4f,
  h_small_order := by native_decide
}

/-! ### `noOrderTwoPoints` for the concrete Pasta parameters

A point of order two is an affine point with `y = 0`, i.e. a root of
`x³ + b`. For both Pasta curves `b = 5` and `−5` is not a cube (checked by
Euler's cube criterion `(-5)^((p-1)/3) ≠ 1`), so no such point exists. -/

/-- Binary (square-and-multiply) exponentiation. `Monoid.npow` is linear in
the exponent, so `native_decide` cannot evaluate `a ^ k` at
cryptographic-size `k`; this computes the same value in `O(log k)`
multiplications. -/
def fastPow {M : Type*} [Monoid M] (a : M) (k : ℕ) : M :=
  if _h : k = 0 then 1
  else
    let half := fastPow (a * a) (k / 2)
    if k % 2 = 0 then half else half * a
termination_by k
decreasing_by omega

theorem fastPow_eq {M : Type*} [Monoid M] (a : M) (k : ℕ) :
    fastPow a k = a ^ k := by
  induction a, k using fastPow.induct with
  | case1 a =>
    simp [fastPow]
  | case2 a k h h_even ih =>
    rw [fastPow]
    simp only [dif_neg h, if_pos h_even, ih]
    rw [← sq, ← pow_mul]
    congr 1
    omega
  | case3 a k h h_odd ih =>
    rw [fastPow]
    simp only [dif_neg h, if_neg h_odd, ih]
    rw [← sq, ← pow_mul, ← pow_succ]
    congr 1
    omega

/-- Euler-style cube criterion: if `−b` fails the cube test
`(−b)^((q−1)/3) = 1` then `x³ + b` has no root, so the curve has no points
of order two. -/
theorem noOrderTwoPoints_of_neg_b_not_cube {q : ℕ} [Fact q.Prime]
    (cp : CurveParams q)
    (h3 : 3 * ((q - 1) / 3) = q - 1)
    (hb0 : cp.b ≠ 0)
    (hcube : (-cp.b) ^ ((q - 1) / 3) ≠ 1) :
    cp.noOrderTwoPoints := by
  intro pt h_curve hy0
  rw [Point.isOnCurve, hy0] at h_curve
  have h_x3 : pt.x ^ 3 = -cp.b := by linear_combination -h_curve
  have hx0 : pt.x ≠ 0 := by
    intro h
    rw [h] at h_x3
    exact hb0 (by linear_combination h_x3)
  apply hcube
  calc (-cp.b) ^ ((q - 1) / 3)
      = (pt.x ^ 3) ^ ((q - 1) / 3) := by rw [h_x3]
    _ = pt.x ^ (3 * ((q - 1) / 3)) := by rw [← pow_mul]
    _ = pt.x ^ (q - 1) := by rw [h3]
    _ = 1 := ZMod.pow_card_sub_one_eq_one hx0

/-- The Pallas parameters have no points of order two: `−5` is not a cube
in `F_p`. Discharges the `noOrderTwoPoints` caller obligation of
`Point.Double` / `Endoscalar.GroupScale` at the concrete instantiation. -/
theorem epAffineParams_noOrderTwoPoints : EpAffineParams.noOrderTwoPoints := by
  apply noOrderTwoPoints_of_neg_b_not_cube
  · native_decide
  · native_decide
  · rw [← fastPow_eq]
    native_decide

/-- The Vesta parameters have no points of order two: `−5` is not a cube
in `F_q`. -/
theorem eqAffineParams_noOrderTwoPoints : EqAffineParams.noOrderTwoPoints := by
  apply noOrderTwoPoints_of_neg_b_not_cube
  · native_decide
  · native_decide
  · rw [← fastPow_eq]
    native_decide

end Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Lemmas
variable {p : ℕ} [Fact p.Prime]
open Spec

lemma double_preserves_membership [NeZero (2 : F p)] (point : Point (F p)) (curveParams: CurveParams p)
    (h_membership: point.isOnCurve curveParams) (h_order : curveParams.noOrderTwoPoints) :
    match point.double with
    | none =>
      -- this is impossible: since we assume that the curve does not have points of order two,
      -- every affine point has an affine double
      False
    | some double => double.isOnCurve curveParams := by
  simp only [CurveParams.noOrderTwoPoints] at h_order
  specialize h_order point h_membership
  simp only [Point.double, if_neg h_order, Point.isOnCurve]
  simp only [Point.isOnCurve] at h_membership
  have h2 : (2 : F p) ≠ 0 := NeZero.ne 2
  have h2y : (2 : F p) * point.y ≠ 0 := mul_ne_zero h2 h_order
  field_simp [h_order, h2y, h2]
  have hb : curveParams.b = point.y ^ 2 - point.x ^ 3 := by rw [h_membership]; ring
  rw [hb]
  ring


lemma add_incomplete_preserves_membership (p1 p2 : Point (F p)) (cp : CurveParams p) (h : p1.x ≠ p2.x)
    (hm1 : p1.isOnCurve cp) (hm2 : p2.isOnCurve cp) :
    match p1.add_incomplete p2 with
    | none => False
    | some r => r.isOnCurve cp := by
  simp only [Point.add_incomplete, if_neg h, Point.isOnCurve]
  simp only [Point.isOnCurve] at hm1 hm2
  have hdiff : p2.x - p1.x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  set lambda := (p2.y - p1.y) / (p2.x - p1.x) with hlambda
  have h_lam_mul : lambda * (p2.x - p1.x) = p2.y - p1.y := by
    simp only [hlambda]; field_simp [hdiff]
  have h_sum : lambda * (p2.y + p1.y) = p2.x ^ 2 + p1.x * p2.x + p1.x ^ 2 := by
    have key : (p2.y - p1.y) * (p2.y + p1.y) = (p2.x - p1.x) * (p2.x ^ 2 + p1.x * p2.x + p1.x ^ 2) := by
      have : p2.y ^ 2 - p1.y ^ 2 = p2.x ^ 3 - p1.x ^ 3 := by rw [hm1, hm2]; ring
      calc (p2.y - p1.y) * (p2.y + p1.y) = p2.y ^ 2 - p1.y ^ 2 := by ring
        _ = p2.x ^ 3 - p1.x ^ 3 := this
        _ = (p2.x - p1.x) * (p2.x ^ 2 + p1.x * p2.x + p1.x ^ 2) := by ring
    have hmul : (p2.x - p1.x) * (lambda * (p2.y + p1.y)) = (p2.x - p1.x) * (p2.x ^ 2 + p1.x * p2.x + p1.x ^ 2) := by
      calc (p2.x - p1.x) * (lambda * (p2.y + p1.y))
          = lambda * (p2.x - p1.x) * (p2.y + p1.y) := by ring
        _ = (p2.y - p1.y) * (p2.y + p1.y) := by rw [h_lam_mul]
        _ = (p2.x - p1.x) * (p2.x ^ 2 + p1.x * p2.x + p1.x ^ 2) := key
    exact mul_left_cancel₀ hdiff hmul
  have h_bracket : lambda ^ 2 * (p1.x - p2.x) + p1.x ^ 2 + p1.x * p2.x + p2.x ^ 2 - 2 * lambda * p1.y = 0 := by
    have eq3 : lambda * (p2.y - p1.y) = lambda ^ 2 * (p2.x - p1.x) := by
      calc lambda * (p2.y - p1.y)
          = lambda * (lambda * (p2.x - p1.x)) := by rw [h_lam_mul]
        _ = lambda ^ 2 * (p2.x - p1.x) := by ring
    have eq4 : 2 * lambda * p1.y = lambda * (p2.y + p1.y) - lambda * (p2.y - p1.y) := by ring
    rw [eq4, h_sum, eq3]; ring
  rw [← sub_eq_zero]
  have factored : (lambda * (p1.x - (lambda ^ 2 - p1.x - p2.x)) - p1.y) ^ 2 - ((lambda ^ 2 - p1.x - p2.x) ^ 3 + cp.b)
      = (2 * p1.x + p2.x - lambda ^ 2) * (lambda ^ 2 * (p1.x - p2.x) + p1.x ^ 2 + p1.x * p2.x + p2.x ^ 2 - 2 * lambda * p1.y)
        + (p1.y ^ 2 - p1.x ^ 3 - cp.b) := by ring
  rw [factored, h_bracket, mul_zero, zero_add]
  have : p1.y ^ 2 - p1.x ^ 3 - cp.b = p1.y ^ 2 - (p1.x ^ 3 + cp.b) := by ring
  rw [this, hm1, sub_self]

end Ragu.Circuits.Point.Lemmas
