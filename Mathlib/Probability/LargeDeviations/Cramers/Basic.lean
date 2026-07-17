/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Cramér's Theorem — Basic Definitions and Infrastructure

This file contains the core definitions and shared lemmas for Cramér's theorem:
- The definitions `partialSum`, `empiricalMean`, `Cramer.rateFunction`,
  `Cramer.upperTailRateFunction`.
- Basic measurability and integrability results.
- MGF/CGF sum formulas via independence.

The upper and lower bounds are proven in `UpperBound.lean` and `LowerBound.lean`;
the main theorem is assembled in `Theorem.lean`.
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
variable (X : ℕ → Ω → ℝ)

/-- The partial sum X₁ + ... + Xₙ. -/
def partialSum (n : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range n, X i

/-- The empirical mean Sₙ / n. -/
noncomputable def empiricalMean (n : ℕ) : Ω → ℝ := fun ω => partialSum X n ω / n

/-- The Legendre transform of the CGF. This is the rate function for Cramér's theorem. -/
noncomputable def Cramer.rateFunction (X : ℕ → Ω → ℝ) (μ : Measure Ω) (x : ℝ) : ℝ :=
  ⨆ t : ℝ, t * x - cgf (X 0) μ t

/-- The "Effective" Rate Function for the upper tail probability `μ(a ≤ empiricalMean X n)`.
Cramér's theorem only holds when `μ[X 0] ≤ a`, so to state a general Large Deviation Principle
for all `a`, we define the rate function to be `rateFunction X μ a` for `μ[X 0] ≤ a`, and `0`
otherwise. -/
noncomputable def Cramer.upperTailRateFunction (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  if μ[X 0] ≤ a then rateFunction X μ a else 0

/-- The exponentially tilted measure, tilted by `t · Sₙ`. -/
noncomputable def Cramer.tiltedMeasure (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ)
    (t : ℝ) : Measure Ω :=
  Measure.tilted μ (fun ω => t * partialSum X n ω)

/- Assumptions for Cramér's theorem -/
-- The random variables Xᵢ are independent.
variable (h_indep : iIndepFun X μ)
-- The random variables Xᵢ are identically distributed.
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
-- The random variables Xᵢ are measurable.
variable (h_meas : ∀ n, Measurable (X n))
-- The random variable X₀ has a finite moment generating function for all `t ∈ ℝ`.
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
-- Assume that this is a "good" rate function, i.e. bounded above.
-- Note: This is implied by h_mgf but difficult to prove directly and beyond scope here.
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) μ t)))

/-! ### Basic measurability and integrability helpers -/

include h_ident h_mgf in
/-- The random variables Xᵢ have finite moment generating functions. -/
lemma integrable_exp_mul_of_identDistrib (i : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X i ω)) μ :=
  ((h_ident i).comp (measurable_const.mul measurable_id).exp).integrable_iff.mpr (h_mgf t)

include h_meas in
/-- The partial sum `Sₙ` is measurable. -/
lemma measurable_partialSum (n : ℕ) : Measurable (partialSum X n) := by
  simpa [partialSum, ← Finset.sum_apply] using
    Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i)

include h_meas in
/-- The empirical mean `Sₙ/n` is measurable. -/
lemma measurable_empiricalMean (n : ℕ) : Measurable (empiricalMean X n) :=
  (measurable_partialSum X h_meas n).div_const (n : ℝ)

include h_mgf in
/-- All `t ∈ ℝ` lie in the interior of the domain for which `exp(tX₀)` is integrable. -/
lemma Cramer.mem_interior_integrableExpSet (t : ℝ) :
    t ∈ interior (integrableExpSet (X 0) μ) := by
  simp [Set.eq_univ_of_forall h_mgf (s := integrableExpSet (X 0) μ)]

include h_mgf in
/-- Integrability of `X 0` follows from finiteness of the MGF on all of `ℝ`. -/
lemma Cramer.integrable_of_forall_integrable_exp : Integrable (X 0) μ :=
  integrable_of_mem_interior_integrableExpSet (Cramer.mem_interior_integrableExpSet X h_mgf 0)

/-! ### Lemmas requiring `IsProbabilityMeasure` -/

variable [IsProbabilityMeasure μ]

/-- For a random variable Y with finite MGF, the CGF satisfies `t · μ[Y] ≤ Λ_Y(t)`.
This follows from Jensen's inequality applied to the convex function `eᵗˣ` for fixed `t`. -/
lemma mul_integral_le_cgf (Y : Ω → ℝ) (h_int : Integrable Y μ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ) (t : ℝ) :
    t * μ[Y] ≤ cgf Y μ t := by
  -- t μ[Y] = log exp(t μ[Y]) ≤ log μ[exp(tY)] = Λ(t)
  rw [cgf, mgf]
  -- Apply Jensen's inequality: exp(μ[tY]) ≤ μ[exp(tY)]
  have jensen := ConvexOn.map_integral_le
    (g := Real.exp) (s := Set.univ) (f := fun ω => t * Y ω)
    (convexOn_exp) Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (h_int.const_mul t) (h_mgf t)
  -- Extract t: t μ[Y] ≤ μ[exp(tY)]
  rw [integral_const_mul] at jensen
  -- Take log of both sides
  exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) jensen)

/-- When `t < 0` and `μ[Y] ≤ a`, we have `t · a - Λ_Y(t) ≤ 0`. -/
lemma mul_sub_cgf_nonpos_of_neg (Y : Ω → ℝ) (h_int : Integrable Y μ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (t a : ℝ) (ht : t < 0) (ha : μ[Y] ≤ a) :
    t * a - cgf Y μ t ≤ 0 := by
    -- t · a ≤ t · μ[Y] ≤ Λ(t)  (since t < 0, the first inequality flips)
  nlinarith [mul_integral_le_cgf Y h_int h_mgf t, mul_le_mul_of_nonpos_left ha ht.le]

include h_indep h_ident h_meas h_mgf in
/-- If each `Xᵢ` has finite MGF, then `Sₙ` also has finite MGF. -/
lemma integrable_exp_mul_partialSum (t : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (t * partialSum X n ω)) μ := by
  have h_rw : (fun ω => Real.exp (t * partialSum X n ω)) =
      fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω) := by
    ext ω; simp [partialSum, Finset.sum_apply, Finset.mul_sum, Real.exp_sum]
  rw [h_rw]; clear h_rw
  induction n with
  | zero => simp
  | succ n ih =>
      -- Show product `e^(t * Xᵢ)` over range `n + 1`
      --   = (product `e^(t * Xᵢ)` over range `n`) * `e^(t * Xₙ)`
    simp only [Finset.prod_range_succ]
    have h_indep_exp : iIndepFun (fun i ω => Real.exp (t * X i ω)) μ := by
      simpa [Function.comp_def] using h_indep.comp (fun _ x => Real.exp (t * x))
        (fun _ => (measurable_const.mul measurable_id).exp)
    -- `∏ᵢⁿ⁻¹ e^{t * Xᵢ}` is independent of `e^{t * Xₙ}`
    have h_indep_prod : IndepFun (fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω))
        (fun ω => Real.exp (t * X n ω)) μ := by
      convert h_indep_exp.indepFun_finsetProd_of_notMem
        (fun i => (h_meas i).const_mul t |>.exp) (by simp : n ∉ Finset.range n) using 2
      simp [Finset.prod_apply]
    exact h_indep_prod.integrable_mul ih
      (integrable_exp_mul_of_identDistrib X h_ident h_mgf n t)

include h_indep h_ident h_meas h_mgf in
/-- The tilted measure by `t · Sₙ` is a probability measure. -/
lemma Cramer.isProbabilityMeasure_tiltedMeasure (t : ℝ) (n : ℕ) :
    IsProbabilityMeasure (tiltedMeasure X μ n t) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_partialSum X h_indep h_ident h_meas h_mgf t n)

include h_indep h_ident h_meas h_mgf in
/-- All `t ∈ ℝ` is in the interior of the domain where `e^{t Sₙ}` is integrable. -/
lemma mem_interior_integrableExpSet_partialSum (t : ℝ) (n : ℕ) :
    t ∈ interior (integrableExpSet (partialSum X n) μ) := by
  simp [Set.eq_univ_of_forall
    (fun s => integrable_exp_mul_partialSum X h_indep h_ident h_meas h_mgf s n)
    (s := integrableExpSet (partialSum X n) μ)]

include h_bdd h_mgf in
/-- For `μ[X] ≤ a`, the supremum in the rate function is achieved by non-negative `t`.
That is, `rateFunction X μ a = sup_{t ∈ ℝ⁺} (tx - Λ(t))` -/
lemma Cramer.rateFunction_eq_iSup_nonneg (a : ℝ) (h_mean : μ[X 0] ≤ a) :
    rateFunction X μ a = ⨆ t : {(x : ℝ) | 0 ≤ x}, (t : ℝ) * a - cgf (X 0) μ t := by
  have h_int := Cramer.integrable_of_forall_integrable_exp X h_mgf
  rw [rateFunction]
  have : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, by simp⟩⟩
  have h_bdd_restrict : BddAbove (Set.range fun t : {x : ℝ | 0 ≤ x} =>
      (t : ℝ) * a - cgf (X 0) μ t) :=
    let ⟨b, hb⟩ := h_bdd a
    ⟨b, fun _ ⟨t, ht⟩ => ht ▸ hb ⟨t.val, rfl⟩⟩
  refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun t => le_ciSup (h_bdd a) (t : ℝ))
  by_cases ht : 0 ≤ t
  -- Case 0 ≤ t: It's in the restricted set so the supremum exists by h_bdd
  · exact le_ciSup h_bdd_restrict ⟨t, ht⟩
  -- Case t < 0: It's bound by the value at t=0, so the supremum is always achievable with 0 ≤ t
  · calc t * a - cgf (X 0) μ t
        ≤ 0 := mul_sub_cgf_nonpos_of_neg (X 0) h_int h_mgf t a (not_le.mp ht) h_mean
      _ = (0 : ℝ) * a - cgf (X 0) μ 0 := by simp [cgf_zero]
      _ ≤ _ := le_ciSup h_bdd_restrict ⟨0, by simp⟩

include h_indep h_ident h_meas h_mgf in
/-- `M_Sₙ(t) = exp(n · Λ_X₀(t))` -/
lemma mgf_partialSum (n : ℕ) (t : ℝ) :
    mgf (partialSum X n) μ t = Real.exp (n * cgf (X 0) μ t) := by
  rcases n with _ | n
  · simp [partialSum, cgf]
  change mgf (∑ i ∈ Finset.range (n + 1), X i) μ t = _
  rw [mgf_sum_of_identDistrib h_meas h_indep
      (fun i _ j _ => (h_ident i).trans (h_ident j).symm)
      (Finset.mem_range.mpr n.succ_pos) t,
    Finset.card_range, cgf, mgf]
  conv_lhs => rw [← Real.exp_log (integral_exp_pos (h_mgf t))]
  rw [← Real.exp_nsmul, nsmul_eq_mul]

include h_indep h_ident h_meas h_mgf in
/-- `Λ_Sₙ(t) = n · Λ_X₀(t)` -/
lemma cgf_partialSum (n : ℕ) (t : ℝ) :
    cgf (partialSum X n) μ t = (n : ℝ) * cgf (X 0) μ t := by
  rw [cgf, mgf_partialSum X h_indep h_ident h_meas h_mgf, Real.log_exp]

end ProbabilityTheory
