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
- The definitions `partialSum`, `empiricalMean`, `rateFunction`, `upperTailRateFunction`.
- Basic measurability and integrability results.
- MGF/CGF sum formulas via independence.

The upper and lower bounds are proven in `UpperBound.lean` and `LowerBound.lean`;
the main theorem is assembled in `Theorem.lean`.
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped BigOperators ENNReal

@[expose] public section

variable {Ω : Type*} [MeasureSpace Ω]
variable (X : ℕ → Ω → ℝ)

/-- The partial sum X₁ + ... + Xₙ. -/
def partialSum (n : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range n, X i

/-- The empirical mean Sₙ / n. -/
noncomputable def empiricalMean (n : ℕ) : Ω → ℝ := fun ω => partialSum X n ω / n

/-- The Legendre transform of the CGF. This is the rate function for Cramér's theorem. -/
noncomputable def I (x : ℝ) : ℝ := ⨆ t : ℝ, t * x - cgf (X 0) ℙ t

/-- The "Effective" Rate Function for the upper tail probability `ℙ(empiricalMean X n ≥ a)`.
Cramér's theorem only holds when `a ≥ 𝔼[X 0]`, so to state a general Large Deviation Principle
for all `a`, we define the rate function to be `I(a)` for `a ≥ 𝔼[X 0]`, and `0` otherwise. -/
noncomputable def upperTailRateFunction (X : ℕ → Ω → ℝ) (a : ℝ) : ℝ :=
  if 𝔼[X 0] ≤ a then I X a else 0

/-- The exponentially tilted measure, tilted by `t · Sₙ`. -/
noncomputable def ℚₙₜ (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) (t : ℝ) : Measure Ω :=
  Measure.tilted μ (fun ω => t * partialSum X n ω)

/- Assumptions for Cramér's theorem -/
-- The random variables Xᵢ are independent.
variable (h_indep : iIndepFun X ℙ)
-- The random variables Xᵢ are identically distributed.
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
-- The random variables Xᵢ are measurable.
variable (h_meas : ∀ n, Measurable (X n))
-- The random variable X₀ is integrable.
-- Note: This is implied by h_mgf but we assume it directly for convenience.
variable (h_int : Integrable (X 0) ℙ)
-- The random variable X₀ has a finite moment generating function for all `t ∈ ℝ`.
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
-- Assume that this is a "good" rate function, i.e. bounded above.
-- Note: This is implied by h_mgf but difficult to prove directly and beyond scope here.
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) ℙ t)))
-- Assume the distribution is non-degenerate (has positive variance everywhere)
-- Note that `Λ''(0) = Var[X]`, so this implies `Var[X] > 0` which implies `X` is non-const a.e.
-- Cumulant generating functions, when they exist and are non-degenerate, are strictly convex.
variable (h_non_deg : ∀ t : ℝ, 0 < iteratedDeriv 2 (cgf (X 0) ℙ) t)
-- For the lower bound, we assume points are "exposed" (in range of cgf derivative).
-- This is equivalent to stating that we can find a t such that the probability measure
-- tilted by `t · X` has expectation `a`, and thus the measure tilted by `t · Sₙ`
-- has expectation `n · a`.
variable (h_exposed : ∀ a : ℝ, 𝔼[X 0] ≤ a → ∃ t, deriv (cgf (X 0) ℙ) t = a)

-- The empirical means under the sequence of tilted measures `ℚₙₜ` satisfy a CLT.
-- Specifically, we assume that √n (Sₙ/n - a) converges in distribution to Normal(0, σ²) under `ℚₙₜ`
-- and state the immediate consequence that any interval to the right of the mean `[a, a + δ]`
-- will contain a proportion of the probability mass that approaches 1/2 as `n → ∞`.
-- Note that this differs from the regular CLT in that each "row" `n` is associated with its own
-- measure `ℚₙₜ`. The statement is still valid however, as the distribution of `Sₙ` is that same
-- for all `ℚₖₜ` when `k ≥ n`, so we can pick a measure `ℚ = ℚₙₜ` for an arbitrarily large `n = N`
-- and view `S_k` for `k ∈ {1, …, N}` as a sum of iid random variables under a single measure `ℚ`.
-- At the time of writing, mathlib does not have a proof of the Central Limit Theorem,
-- so we take this as an assumption, and explicitly enumerate all other assumptions it relies on.
-- TODO: once the CLT is available in mathlib, remove this assumption.
variable (h_clt_axiom :
    iIndepFun X ℙ →
    (∀ n, IdentDistrib (X n) (X 0) ℙ ℙ) →
    (∀ n, Measurable (X n)) →
    Integrable (X 0) ℙ →
    (∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ) →
    (∀ t : ℝ, 0 < iteratedDeriv 2 (cgf (X 0) ℙ) t) →
    ∀ (t a : ℝ),
    ∀ δ > 0,
    ∀ ε > 0,
    deriv (cgf (X 0) ℙ) t = a →
      ∀ᶠ n in atTop,
      (1 / 2 - ε : ℝ) ≤ ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal)


/-! ### Basic measurability and integrability helpers -/

include h_ident h_mgf in
/- The random variables Xᵢ have finite moment generating functions. -/
lemma integrable_exp_of_identDistrib (i : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X i ω)) ℙ := by
  have hcomp : Measurable (fun x : ℝ => Real.exp (t * x)) :=
    (measurable_const.mul measurable_id).exp
  have : IdentDistrib (fun ω => Real.exp (t * X i ω)) (fun ω => Real.exp (t * X 0 ω)) ℙ ℙ :=
    (h_ident i).comp hcomp
  exact this.integrable_iff.mpr (h_mgf t)

include h_meas in
/-- The partial sum `Sₙ` is measurable. -/
lemma measurable_partialSum (n : ℕ) : Measurable (partialSum X n) := by
  unfold partialSum
  convert Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i) using 2
  exact Finset.sum_apply _ _ _

include h_meas in
/-- The empirical mean `Sₙ/n` is measurable. -/
lemma measurable_empiricalMean (n : ℕ) : Measurable (empiricalMean X n) :=
  (measurable_partialSum X h_meas n).div_const (n : ℝ)

include h_mgf in
/-- All `t ∈ ℝ` lie in the interior of the domain of `t` for which `exp(tX₀)` is integrable. -/
lemma mem_interior_integrableExpSet (t : ℝ) : t ∈ interior (integrableExpSet (X 0) ℙ) := by
  have h_univ : integrableExpSet (X 0) ℙ = Set.univ := by
    ext s; simp [integrableExpSet, h_mgf]
  rw [h_univ, interior_univ]
  exact Set.mem_univ t

-- The following lemmas require the measure to be a probability measure.
variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- For a random variable Y with finite MGF, the CGF satisfies `Λ_Y(t) ≥ t · 𝔼[Y]`.
This follows from Jensen's inequality applied to the convex function `eᵗˣ` for fixed `t`. -/
lemma cgf_ge_mul_expect (Y : Ω → ℝ) (h_int : Integrable Y ℙ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) ℙ) (t : ℝ) :
    cgf Y ℙ t ≥ t * 𝔼[Y] := by
  -- Λ(t) = log 𝔼[exp(tY)] ≥ log exp(t 𝔼[Y]) = t 𝔼[Y]
  rw [cgf, mgf]
  -- Apply Jensen's inequality: exp(𝔼[tY]) ≤ 𝔼[exp(tY)]
  have jensen := ConvexOn.map_integral_le
    (g := Real.exp) (s := Set.univ) (f := fun ω => t * Y ω)
    (convexOn_exp) Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (h_int.const_mul t) (h_mgf t)
  -- Extract t: t 𝔼[Y] ≤ 𝔼[exp(tY)]
  rw [integral_const_mul] at jensen
  -- Take log of both sides
  have h_pos : 0 < mgf Y ℙ t := integral_exp_pos (h_mgf t)
  calc t * 𝔼[Y]
      = Real.log (Real.exp (t * 𝔼[Y])) := by rw [Real.log_exp _]
    _ ≤ cgf Y ℙ t :=
        Real.log_le_log (Real.exp_pos _) jensen

/-- When `t < 0` and `a ≥ 𝔼[Y]`, we have `t · a - Λ_Y(t) ≤ 0`. -/
lemma rate_function_neg_param_le_zero (Y : Ω → ℝ) (h_int : Integrable Y ℙ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) ℙ)
    (t a : ℝ) (ht : t < 0) (ha : 𝔼[Y] ≤ a) :
    t * a - cgf Y ℙ t ≤ 0 := by
  have h_cgf := cgf_ge_mul_expect Y h_int h_mgf t
  -- Λ(t) ≥ t · 𝔼[Y] ≥ t · a  (since t < 0, inequality flips)
  have : t * 𝔼[Y] ≥ t * a := by
    exact mul_le_mul_of_nonpos_left ha (le_of_lt ht)
  calc t * a - cgf Y ℙ t
      ≤ t * a - t * 𝔼[Y] := by linarith [h_cgf]
    _ = t * (a - 𝔼[Y]) := by ring
    _ ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht)
        linarith

include h_indep h_ident h_meas h_mgf in
/-- If each `Xᵢ` has finite MGF, then `Sₙ` also has finite MGF. -/
lemma integrable_exp_sum (t : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (t * partialSum X n ω)) ℙ := by
  have : (fun ω => Real.exp (t * partialSum X n ω)) =
          fun ω => Real.exp (∑ i ∈ Finset.range n, t * X i ω) := by
    ext ω
    unfold partialSum
    simp only [Finset.sum_apply]
    rw [Finset.mul_sum]
  rw [this]
  conv =>
    lhs
    intro ω
    rw [Real.exp_sum]
  -- Goal: Integrable (fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω)) ℙ
  -- Proceed by induction on n
  induction n with
  | zero =>
    -- Base case: Empty product is 1, which is integrable
    simp only [Finset.range_zero, Finset.prod_empty]
    exact integrable_const 1
  | succ n ih =>
    -- Show product `e^(t * Xᵢ)` over range `n + 1`
    --   = (product `e^(t * Xᵢ)` over range `n`) * `e^(t * Xₙ)`
    have h_eq : (fun ω => ∏ i ∈ Finset.range (n + 1), Real.exp (t * X i ω)) =
        (fun ω => (∏ i ∈ Finset.range n, Real.exp (t * X i ω)) * Real.exp (t * X n ω)) := by
      funext ω
      rw [Finset.prod_range_succ]
    rw [h_eq]
    -- We know that `e^(t * Xₙ)` is integrable from integrable_exp_of_identDistrib
    have h_integrable_n : Integrable (fun ω => Real.exp (t * X n ω)) ℙ :=
      integrable_exp_of_identDistrib X h_ident h_mgf n t
    -- `e^{t * Xᵢ}` are independent
    have h_indep_exp : iIndepFun (fun i ω => Real.exp (t * X i ω)) ℙ := by
      have := h_indep.comp (fun _ x => Real.exp (t * x))
        (fun _ => (measurable_const.mul measurable_id).exp)
      simp only [Function.comp_def] at this
      exact this
    -- `∏ᵢⁿ⁻¹ e^{t * Xᵢ}` is independent of `e^{t * Xₙ}`
    have h_indep_prod : IndepFun (fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω))
        (fun ω => Real.exp (t * X n ω)) ℙ := by
      convert h_indep_exp.indepFun_finset_prod_of_notMem
        (fun i => (h_meas i).const_mul t |>.exp)
        (by simp : n ∉ Finset.range n) using 2
      simp [Finset.prod_apply]
    -- Need the equality `e^{t * Sₙ} = e^{∑ᵢⁿ (t * Xᵢ)}` to apply the induction hypothesis
    have h_eq_n : (fun ω => Real.exp (t * partialSum X n ω)) =
        fun ω => Real.exp (∑ i ∈ Finset.range n, t * X i ω) := by
      ext ω
      unfold partialSum
      simp only [Finset.sum_apply]
      rw [Finset.mul_sum]
    -- Use IndepFun.integrable_mul
    exact ProbabilityTheory.IndepFun.integrable_mul h_indep_prod (ih h_eq_n) h_integrable_n

include h_indep h_ident h_meas h_mgf in
/-- The tilted measure by `t · Sₙ` is a probability measure. -/
lemma isProbabilityMeasure_tilted_partialSum (t : ℝ) (n : ℕ) :
    IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
  isProbabilityMeasure_tilted (integrable_exp_sum X h_indep h_ident h_meas h_mgf t n)

include h_indep h_ident h_meas h_mgf in
/-- All `t ∈ ℝ` is in the interior of the domain where `e^{t Sₙ}` is integrable. -/
lemma mem_interior_integrableExpSet_partialSum (t : ℝ) (n : ℕ) :
    t ∈ interior (integrableExpSet (partialSum X n) ℙ) := by
  have h_univ : integrableExpSet (partialSum X n) ℙ = Set.univ := by
    ext s
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact integrable_exp_sum X h_indep h_ident h_meas h_mgf s n
  rw [h_univ, interior_univ]
  exact Set.mem_univ t

include h_bdd h_mgf h_int in
/-- For `a ≥ 𝔼[X]`, the supremum in the rate function is achieved by non-negative `t`.
That is, `I(a) = sup_{t ∈ ℝ⁺} (tx - Λ(t))` -/
lemma rateFunction_eq_sup_nonneg (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    I X a = ⨆ t : {(x : ℝ) | 0 ≤ x}, (t : ℝ) * a - cgf (X 0) ℙ t := by
  rw [I]
  apply le_antisymm
  · -- Direction 1: sup over ℝ≥0 ≤ sup over ℝ
    have h_bdd_restrict : BddAbove (Set.range fun s : {x : ℝ | 0 ≤ x} =>
        (s : ℝ) * a - cgf (X 0) ℙ s) := by
      obtain ⟨b, hb⟩ := h_bdd a
      use b
      rintro y ⟨s, rfl⟩
      exact hb ⟨s.val, rfl⟩
    apply ciSup_le
    intro t
    by_cases ht : 0 ≤ t
    · -- Case t ≥ 0: It's in the restricted set so the supremum exists by h_bdd
      exact le_ciSup h_bdd_restrict ⟨t, ht⟩
    · -- Case t < 0: It's bound by the value at t=0, so the supremum is always achievable
      -- with a t ≥ 0
      rw [not_le] at ht
      -- When t < 0, show t*a - cgf t ≤ 0 = (value at t=0) by rate_function_neg_param_le_zero
      have h_le_zero : t * a - cgf (X 0) ℙ t ≤ 0 :=
        rate_function_neg_param_le_zero (X 0) h_int h_mgf t a ht h_mean
      calc t * a - cgf (X 0) ℙ t
          ≤ 0 := h_le_zero
        _ = (0 : ℝ) * a - cgf (X 0) ℙ 0 := by simp [cgf_zero]
        _ ≤ ⨆ s : {x : ℝ | 0 ≤ x}, (s : ℝ) * a - cgf (X 0) ℙ s :=
            le_ciSup h_bdd_restrict ⟨0, by simp⟩
  · -- Direction 2: sup over ℝ≥0 ≥ sup over ℝ
    have h_nonempty : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, by simp⟩⟩
    apply ciSup_le
    intro t
    exact le_ciSup (h_bdd a) (t : ℝ)

include h_indep h_ident h_meas h_mgf in
/-- `M_Sₙ(t) = exp(n · Λ_X₀(t))` -/
lemma mgf_sum_eq_exp_n_prod_cgf (n : ℕ) (t : ℝ) :
    mgf (partialSum X n) ℙ t = Real.exp (n * cgf (X 0) ℙ t) := by
  have h_eq_sum : partialSum X n = ∑ i ∈ Finset.range n, X i := rfl
  rw [h_eq_sum]
  by_cases hn : n = 0
  · simp [hn, cgf]
  have h0_mem : 0 ∈ Finset.range n := by simp [Finset.mem_range]; omega
  have hident_all : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      IdentDistrib (X i) (X j) ℙ ℙ := by
    intros i _ j _
    exact (h_ident i).trans (h_ident j).symm
  calc mgf (∑ i ∈ Finset.range n, X i) ℙ t
      = mgf (X 0) ℙ t ^ n := by
        rw [mgf_sum_of_identDistrib h_meas h_indep hident_all h0_mem t, Finset.card_range]
    _ = Real.exp (n * cgf (X 0) ℙ t) := by
        rw [cgf, mgf]
        conv_lhs => rw [← Real.exp_log (integral_exp_pos (h_mgf t))]
        rw [← Real.exp_nsmul, nsmul_eq_mul]

include h_indep h_ident h_meas h_mgf in
/-- `Λ_Sₙ(t) = n · Λ_X₀(t)` -/
lemma cgf_sum_eq_n_prod_cgf (n : ℕ) (t : ℝ) :
    cgf (partialSum X n) ℙ t = (n : ℝ) * cgf (X 0) ℙ t := by
  rcases n with _ | n
  · have h_eq_sum : partialSum X 0 = ∑ i ∈ Finset.range 0, X i := rfl
    simp [h_eq_sum, cgf]
  have h0_mem : 0 ∈ Finset.range (n + 1) := by simp [Finset.mem_range]
  have hident_all : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      IdentDistrib (X i) (X j) ℙ ℙ := by
    intros i _ j _
    exact (h_ident i).trans (h_ident j).symm
  have hint : ∀ i ∈ Finset.range (n + 1), Integrable (fun ω => Real.exp (t * X i ω)) ℙ := by
    intros i _
    exact integrable_exp_of_identDistrib X h_ident h_mgf i t
  have h_eq_sum : partialSum X (n+1) = ∑ i ∈ Finset.range (n+1), X i := rfl
  rw [h_eq_sum]
  convert cgf_sum_of_identDistrib h_meas h_indep hident_all h0_mem t hint using 1
  simp [Finset.card_range]
