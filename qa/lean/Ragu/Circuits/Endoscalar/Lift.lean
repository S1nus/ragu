import Clean.Circuit
import Clean.Circuit.Loops
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Boolean.And
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Endoscalar.Lift
variable {p : ℕ} [Fact p.Prime]

/-- `Endoscalar::lift` lifts a 128-bit endoscalar to its effective field-element
scalar. Implements Algorithm 2 from BGH19 (the Halo paper). Mirrors the Rust
loop in `crates/ragu_primitives/src/endoscalar.rs::lift`.

For each pair of bits `(n, e)`:
  - `tmp = (n ? -1 : 1) · (e ? ζ : 1)`
  - `acc' = 2·acc + tmp`

Starting from `acc₀ = 2·(ζ+1)` and looping 64 times, output is `acc₆₄`.

The circuit-side `main` separates the two phases of the loop:
* **Constraint emission** (in-circuit, via `Circuit.mapFinRange 64`): one
  `Boolean.And.circuit` call per iteration computing `bits[2i] ∧ bits[2i+1]`
  as a fresh wire. The body's output is the AND wire, which is `ConstantOutput`,
  so `circuit_norm` collapses the loop machinery automatically.
* **Symbolic accumulation** (pure value-level `Fin.foldl 64`): the running
  Horner-style accumulator is built from the bits and the AND-wire expressions
  with no constraint emission. The final answer adds a closed-form constant
  capturing the initial `2·(ζ+1)` and the 64 implicit `+1` shifts.

Extraction instance: `qa/crates/lean_extraction/src/instances/endoscalar_lift.rs`,
tied to this reimpl by the fingerprint equivalence check via the formal instance
in `qa/lean/Ragu/Instances/Endoscalar/Lift.lean`. The Rust instance uses an
inlined `Boolean::and` (gate + 2 `enforce_equal`s, same pattern as
`boolean_and.rs`) and shapes its output Expression tree to match this reimpl's
`stepCircuit` form verbatim, so the structural output encoding in the
fingerprint digests agrees. -/
structure Input (F : Type) where
  bits : Vector F 128
deriving ProvableStruct

/-- One native Horner step. Given current accumulator and one 2-bit pair `(n, e)`
(interpreted as field 0 or 1), returns the next accumulator value. -/
def stepNative (ζ acc n e : F p) : F p :=
  let sign : F p := if n = 1 then -1 else 1
  let mult : F p := if e = 1 then ζ else 1
  2 * acc + sign * mult

/-- Native lift: 64-step Horner reduction starting from `2·(ζ+1)`. Iterates
`stepNative` over the 64 bit-pairs of `bits`. -/
def liftNative (ζ : F p) (bits : Vector (F p) 128) : F p :=
  Fin.foldl 64 (fun acc (i : Fin 64) =>
      stepNative ζ acc (bits[2 * i.val]'(by have := i.isLt; omega))
        (bits[2 * i.val + 1]'(by have := i.isLt; omega)))
    (2 * (ζ + 1))

/-- Per-iteration symbolic accumulator update (pure expression, no constraints).
Encodes the native step `2·acc + (n?-1:1)·(e?ζ:1)` as an affine expression in
`n`, `e`, and `ne = n·e`. The constant `1` from the algebraic identity is *not*
included here — it's accumulated separately via the closed-form `ctFinal`. -/
def stepCircuit (ζ : F p) (n e ne acc : Expression (F p)) : Expression (F p) :=
  Expression.const 2 * acc +
    (Expression.const (-2) * n +
     Expression.const (ζ - 1) * e +
     Expression.const (2 * (1 - ζ)) * ne)

/-- The constant component of the running accumulator after `k` iterations,
starting from `2·(ζ+1)`. Each iteration applies `ct → 2·ct + 1`, so the closed
form is `2^(k+1)·(ζ+1) + 2^k - 1`. -/
def ctFinal (ζ : F p) (k : ℕ) : F p :=
  2 ^ (k + 1) * (ζ + 1) + 2 ^ k - 1

def main (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Expression (F p)) := do
  let ne_wires ← Circuit.mapFinRange 64 fun (i : Fin 64) =>
    Boolean.And.circuit
      ⟨input.bits[2 * i.val]'(by have := i.isLt; omega),
       input.bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩
  let acc : Expression (F p) := Fin.foldl 64
    (fun (acc : Expression (F p)) (i : Fin 64) =>
      stepCircuit curveParams.ζ
        (input.bits[2 * i.val]'(by have := i.isLt; omega))
        (input.bits[2 * i.val + 1]'(by have := i.isLt; omega))
        ne_wires[i]
        acc)
    (Expression.const 0)
  return acc + Expression.const (ctFinal curveParams.ζ 64)

def Assumptions (_curveParams : Point.Spec.CurveParams p) (input : Input (F p)) :=
  ∀ i : Fin 128, IsBool input.bits[i]

def Spec (curveParams : Point.Spec.CurveParams p) (input : Input (F p)) (out : F p) :=
  out = liftNative curveParams.ζ input.bits

instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input field where
  main := main curveParams
  localLength _ := 64 * 3
  localLength_eq input offset := by
    simp [main, circuit_norm, Boolean.And.circuit]
  subcircuitsConsistent input offset := by
    simp [main, circuit_norm, Boolean.And.circuit]

/-- For `n, e ∈ {0, 1}` (encoded as field elements), the symbolic step's
algebraic core matches the native step's `sign · mult` factor:
`1 + (-2·n + (ζ-1)·e + 2·(1-ζ)·n·e) = (if n=1 then -1 else 1) · (if e=1 then ζ else 1)`.
The constant `1` on the LHS is what gets accumulated into `ctFinal`. -/
private lemma step_identity (ζ n e : F p) (hn : IsBool n) (he : IsBool e) :
    1 + (-2 * n + (ζ - 1) * e + 2 * (1 - ζ) * (n * e)) =
    (if n = 1 then -1 else 1) * (if e = 1 then ζ else 1) := by
  rcases hn with hn | hn <;> rcases he with he | he <;>
    simp [hn, he] <;> ring

/-- For `a, b, out ∈ {0, 1}` (as field elements), `out.val = a.val &&& b.val`
forces `out = a * b`. Bridges `Boolean.And.Spec`'s `Nat`/`&&&` form to a field
product. -/
private lemma and_eq_mul_of_isBool (a b out : F p) (ha : IsBool a) (hb : IsBool b)
    (h_out : IsBool out) (h : ZMod.val out = ZMod.val a &&& ZMod.val b) :
    out = a * b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases h_out with h_out | h_out <;>
    simp_all [ZMod.val_zero, ZMod.val_one]

/-- `Fin.foldl` is congruent in its body up to pointwise equality. -/
private lemma fin_foldl_congr {α : Type*} (n : ℕ)
    (f g : α → Fin n → α) (init : α)
    (h : ∀ acc i, f acc i = g acc i) :
    Fin.foldl n f init = Fin.foldl n g init := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    have h_castSucc : ∀ acc i, (fun acc (i : Fin n) => f acc i.castSucc) acc i =
        (fun acc (i : Fin n) => g acc i.castSucc) acc i := by
      intro acc i; exact h acc i.castSucc
    rw [ih (fun acc i => f acc i.castSucc) (fun acc i => g acc i.castSucc) init h_castSucc]
    rw [h _ (Fin.last n)]

/-- A `Fin.foldl_succ_last` variant that lets us bridge the `castSucc`-shifted
inner body to a natural `Fin n`-indexed body when they agree pointwise. -/
private lemma fin_foldl_succ_last_eq {α : Type*} (n : ℕ) (f : α → Fin (n + 1) → α)
    (g : α → Fin n → α) (init : α)
    (hfg : ∀ acc (i : Fin n), f acc i.castSucc = g acc i) :
    Fin.foldl (n + 1) f init = f (Fin.foldl n g init) (Fin.last n) := by
  rw [Fin.foldl_succ_last]
  congr 1
  exact fin_foldl_congr n (fun acc i => f acc i.castSucc) g init hfg

theorem soundness (curveParams : Point.Spec.CurveParams p)
    : Soundness (F p) (elaborated curveParams) (Assumptions curveParams)
        (Spec curveParams) := by
  circuit_proof_start [Boolean.And.circuit, Boolean.And.Assumptions, Boolean.And.Spec]
  -- h_input gives the field-level relationship; lift to per-bit equality.
  -- Use Nat-indexed form (matches how the foldl-body indexes via `2 * i.val`).
  have h_bits_eq : ∀ (j : ℕ) (h : j < 128),
      Expression.eval env (input_var_bits[j]'h) = (input_bits[j]'h) := by
    intro j h
    have := congrArg (fun v => v[j]'h) h_input
    simpa [Vector.getElem_map] using this
  have h_bits_bool : ∀ (j : ℕ) (h : j < 128),
      IsBool (input_bits[j]'h) := fun j h => h_assumptions ⟨j, h⟩
  -- For each AND-iter, h_holds (under the boolean premises) gives us the
  -- `&&&` spec + IsBool for the wire; promote to wire = bits[2i] * bits[2i+1].
  have h_ne : ∀ i : Fin 64,
      Expression.eval env
        (Boolean.And.main
            ⟨input_var_bits[2 * i.val]'(by have := i.isLt; omega),
             input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩
            (i₀ + i.val * 3)).1 =
        (input_bits[2 * i.val]'(by have := i.isLt; omega)) *
        (input_bits[2 * i.val + 1]'(by have := i.isLt; omega)) := by
    intro i
    have hi : 2 * i.val < 128 := by have := i.isLt; omega
    have hi1 : 2 * i.val + 1 < 128 := by have := i.isLt; omega
    have ha : IsBool (Expression.eval env (input_var_bits[2 * i.val]'hi)) := by
      rw [h_bits_eq _ hi]; exact h_bits_bool _ hi
    have hb : IsBool (Expression.eval env (input_var_bits[2 * i.val + 1]'hi1)) := by
      rw [h_bits_eq _ hi1]; exact h_bits_bool _ hi1
    obtain ⟨h_val, h_isbool⟩ := h_holds i ⟨ha, hb⟩
    rw [h_bits_eq _ hi, h_bits_eq _ hi1] at h_val
    exact and_eq_mul_of_isBool
      (input_bits[2 * i.val]'hi) (input_bits[2 * i.val + 1]'hi1)
      _
      (h_bits_bool _ hi) (h_bits_bool _ hi1) h_isbool h_val
  -- With h_ne in hand, the symbolic Fin.foldl 64 evaluates pointwise to a
  -- value-level Horner reduction over `input_bits` and `ne` wire values.
  -- Inductive bridge to `liftNative` via `step_identity`.
  -- First: prove a generalized invariant for all m ≤ 64. Then specialize.
  -- The invariant: at step m, eval(sym_acc) + ctFinal ζ m = native_acc.
  suffices h : ∀ (m : ℕ) (hm : m ≤ 64),
      Expression.eval env
        (Fin.foldl m (fun (acc : Expression (F p)) (i : Fin m) =>
            stepCircuit curveParams.ζ
              (input_var_bits[2 * i.val]'(by have := i.isLt; omega))
              (input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega))
              (Boolean.And.main
                ⟨input_var_bits[2 * i.val]'(by have := i.isLt; omega),
                 input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩
                (i₀ + i.val * 3)).1
              acc)
          (Expression.const 0)) +
      ctFinal curveParams.ζ m =
      Fin.foldl m (fun (acc : F p) (i : Fin m) =>
          stepNative curveParams.ζ acc
            (input_bits[2 * i.val]'(by have := i.isLt; omega))
            (input_bits[2 * i.val + 1]'(by have := i.isLt; omega)))
        (2 * (curveParams.ζ + 1)) by
    simp only [liftNative]
    exact h 64 (Nat.le_refl 64)
  intro m hm
  induction m with
  | zero =>
    simp only [Fin.foldl_zero, Expression.eval, ctFinal, pow_zero]
    ring
  | succ m ih =>
    have hm' : m ≤ 64 := Nat.le_of_succ_le hm
    have hi_m : 2 * m < 128 := by omega
    have hi_m1 : 2 * m + 1 < 128 := by omega
    have ih' := ih hm'
    have h_ne_m : Expression.eval env
        (Boolean.And.main
            ⟨input_var_bits[2 * m]'hi_m,
             input_var_bits[2 * m + 1]'hi_m1⟩
            (i₀ + m * 3)).1 =
        (input_bits[2 * m]'hi_m) * (input_bits[2 * m + 1]'hi_m1) := by
      have := h_ne ⟨m, by omega⟩
      simpa using this
    have h_bm_eq : Expression.eval env (input_var_bits[2 * m]'hi_m) = input_bits[2 * m]'hi_m :=
      h_bits_eq _ hi_m
    have h_bm1_eq : Expression.eval env (input_var_bits[2 * m + 1]'hi_m1) =
        input_bits[2 * m + 1]'hi_m1 :=
      h_bits_eq _ hi_m1
    have h_bm_bool : IsBool (input_bits[2 * m]'hi_m) := h_bits_bool _ hi_m
    have h_bm1_bool : IsBool (input_bits[2 * m + 1]'hi_m1) := h_bits_bool _ hi_m1
    have hsi := step_identity curveParams.ζ
      (input_bits[2 * m]'hi_m) (input_bits[2 * m + 1]'hi_m1) h_bm_bool h_bm1_bool
    -- Peel the last iteration on both sides using `fin_foldl_succ_last_eq` so
    -- the inner foldls match `ih'` directly (without castSucc baggage).
    rw [fin_foldl_succ_last_eq m _ (fun (acc : Expression (F p)) (i : Fin m) =>
        stepCircuit curveParams.ζ
          (input_var_bits[2 * i.val]'(by have := i.isLt; omega))
          (input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega))
          (Boolean.And.main
            ⟨input_var_bits[2 * i.val]'(by have := i.isLt; omega),
             input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩
            (i₀ + i.val * 3)).1
          acc) _ (fun _ _ => by simp [Fin.val_castSucc])]
    rw [fin_foldl_succ_last_eq m _ (fun (acc : F p) (i : Fin m) =>
        stepNative curveParams.ζ acc
          (input_bits[2 * i.val]'(by have := i.isLt; omega))
          (input_bits[2 * i.val + 1]'(by have := i.isLt; omega))) _
        (fun _ _ => by simp [Fin.val_castSucc])]
    -- Name the inner foldls (matching `ih'`'s form).
    set sym_inner := Fin.foldl m
        (fun (acc : Expression (F p)) (i : Fin m) =>
          stepCircuit curveParams.ζ
            (input_var_bits[2 * i.val]'(by have := i.isLt; omega))
            (input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega))
            (Boolean.And.main
              ⟨input_var_bits[2 * i.val]'(by have := i.isLt; omega),
               input_var_bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩
              (i₀ + i.val * 3)).1
            acc) (Expression.const 0)
    set nat_inner := Fin.foldl m
        (fun (acc : F p) (i : Fin m) =>
          stepNative curveParams.ζ acc
            (input_bits[2 * i.val]'(by have := i.isLt; omega))
            (input_bits[2 * i.val + 1]'(by have := i.isLt; omega)))
        (2 * (curveParams.ζ + 1))
    -- Now ih' : eval sym_inner + ctFinal m = nat_inner
    -- Goal: eval (stepCircuit ζ bits_var[2m] bits_var[2m+1] (And ...).1 sym_inner) + ctFinal (m+1)
    --        = stepNative ζ nat_inner bits[2m] bits[2m+1]
    -- Unfold the OUTER step only (not the inner foldl bodies).
    have h_ct_rec : ctFinal curveParams.ζ (m + 1) = 2 * ctFinal curveParams.ζ m + 1 := by
      simp only [ctFinal]; ring
    rw [h_ct_rec]
    -- Compute the symbolic step's evaluation explicitly.
    show Expression.eval env (stepCircuit curveParams.ζ
        (input_var_bits[2 * (Fin.last m).val]'(by simp; omega))
        (input_var_bits[2 * (Fin.last m).val + 1]'(by simp; omega))
        (Boolean.And.main _ _).1 sym_inner) + (2 * ctFinal curveParams.ζ m + 1) =
      stepNative curveParams.ζ nat_inner
        (input_bits[2 * (Fin.last m).val]'(by simp; omega))
        (input_bits[2 * (Fin.last m).val + 1]'(by simp; omega))
    simp only [Fin.val_last, stepCircuit, stepNative, Expression.eval,
      h_bm_eq, h_bm1_eq, h_ne_m]
    linear_combination 2 * ih' + hsi

theorem completeness (curveParams : Point.Spec.CurveParams p)
    : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  circuit_proof_start [Boolean.And.circuit, Boolean.And.Assumptions, Boolean.And.Spec]
  -- The goal is `∀ i : Fin 64, IsBool (eval ...input_var_bits[2*i]) ∧ IsBool (eval ...input_var_bits[2*i+1])`.
  -- Derive from h_assumptions (which states IsBool for every bit) + h_input (eval = input).
  intro i
  have hi : 2 * i.val < 128 := by have := i.isLt; omega
  have hi1 : 2 * i.val + 1 < 128 := by have := i.isLt; omega
  have h_bits_eq : ∀ (j : ℕ) (h : j < 128),
      Expression.eval env.toEnvironment (input_var_bits[j]'h) = (input_bits[j]'h) := by
    intro j h
    have := congrArg (fun v => v[j]'h) h_input
    simpa [Vector.getElem_map] using this
  refine ⟨?_, ?_⟩
  · rw [h_bits_eq _ hi]; exact h_assumptions ⟨2 * i.val, hi⟩
  · rw [h_bits_eq _ hi1]; exact h_assumptions ⟨2 * i.val + 1, hi1⟩

def circuit (curveParams : Point.Spec.CurveParams p) : FormalCircuit (F p) Input field :=
  { elaborated curveParams with
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Endoscalar.Lift
