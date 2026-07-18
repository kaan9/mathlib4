/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.LowerBound
public import Mathlib.Probability.LargeDeviations.Cramers.UpperBound

import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Cramér's theorem

Cramér's theorem describes the exponential decay of the tail probabilities `μ(a ≤ Sₙ / n)` of the
empirical mean of a sequence of i.i.d. real random variables with finite moment-generating
function. This file assembles the two bounds of the theorem, expressed through the rate function
`Cramer.upperTailRateFunction X μ`.

Each bound combines the corresponding estimate from `UpperBound.lean` and `LowerBound.lean` for
`μ[X 0] ≤ a`, and handles the case `a < μ[X 0]` using the strong law of large numbers, under which
`μ(a ≤ Sₙ / n) → 1`.

## Main results

* `Cramer.limsup_le_neg_upperTailRateFunction` (upper bound): for every `a`,
  `limsupₙ (1 / n) log μ(a ≤ Sₙ / n) ≤ -upperTailRateFunction X μ a`.
* `Cramer.neg_upperTailRateFunction_le_liminf` (lower bound): for every `a`,
  `-upperTailRateFunction X μ a ≤ liminfₙ (1 / n) log μ(a ≤ Sₙ / n)`.

## TODO
Define general large deviation principles (the limsup over closed sets / liminf over open sets
with lower semicontinuous rate functions) and restate these two bounds in that language.

## References

The statement and its proof follow Theorem 2.2.3 of
[A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*][demboZeitouni2010].
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
variable (X : ℕ → Ω → ℝ)

/- Assumptions for Cramér's theorem -/
variable (h_indep : iIndepFun X μ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) μ t)))
variable (h_non_deg : ∀ t : ℝ, 0 < iteratedDeriv 2 (cgf (X 0) μ) t)
variable (h_exposed : ∀ a : ℝ, μ[X 0] ≤ a → ∃ t, deriv (cgf (X 0) μ) t = a)

/-! ### Lemmas requiring `IsProbabilityMeasure` -/

variable [IsProbabilityMeasure μ]

include h_indep h_meas h_ident h_mgf in
/-- If `a < μ[X 0]`, `μ(a ≤ Sₙ/n) → 1` by the strong law of large numbers. -/
private lemma Cramer.tendsto_measure_empiricalMean_ge_of_lt_integral (a : ℝ) (h : a < μ[X 0]) :
  Tendsto (fun n : ℕ => (μ {ω | a ≤ empiricalMean X n ω} : ENNReal)) atTop (𝓝 1) := by
  have h_int := Cramer.integrable_of_forall_integrable_exp X h_mgf
  have h_pairwise : Pairwise (fun i j => IndepFun (X i) (X j) μ) :=
    fun i j hij => h_indep.indepFun hij
  -- Almost sure convergence: `μ(limₙ Sₙ/n = μ[X]) = 1`
  have h_strong_law :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => empiricalMean X n ω) atTop (𝓝 μ[X 0]) := by
    have h_orig := strong_law_ae_real X h_int h_pairwise h_ident
    filter_upwards [h_orig] with ω hω
    have h_eq : (fun n : ℕ => empiricalMean X n ω) =
        (fun n => (∑ i ∈ Finset.range n, X i ω) / n) := by
      ext n
      unfold empiricalMean partialSum
      rw [Finset.sum_apply]
    rwa [h_eq]
  have h_gap : 0 < μ[X 0] - a := sub_pos.mpr h
  set ε := (μ[X 0] - a) / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hε_bound : a + ε < μ[X 0] := by linarith
  have h_conv_set :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |empiricalMean X n ω - μ[X 0]| < ε := by
    filter_upwards [h_strong_law] with ω hω
    have h_tend := (Metric.tendsto_nhds.mp hω) ε hε_pos
    filter_upwards [h_tend] with n hn
    rwa [Real.dist_eq] at hn
  have h_eventually_large : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, a ≤ empiricalMean X n ω := by
    filter_upwards [h_conv_set] with ω hω
    filter_upwards [hω] with n hn
    have : μ[X 0] - ε < empiricalMean X n ω := by
      rw [abs_sub_lt_iff] at hn
      linarith
    linarith
  let S : ℕ → Set Ω := fun k => {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω}
  have h_mono : Monotone S := by
    intro k₁ k₂ hk ω hω n hn
    exact hω n (le_trans hk hn)
  have h_union : ⋃ k, S k = {ω | ∀ᶠ n in atTop, a ≤ empiricalMean X n ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Filter.eventually_atTop, S]
  have h_union_meas : μ (⋃ k, S k) = 1 := by
    have h_union_meas_set : MeasurableSet (⋃ k, S k) := by
      refine MeasurableSet.iUnion fun k => ?_
      change MeasurableSet {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω}
      have : {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω} =
          ⋂ n, ⋂ (_ : k ≤ n), {ω | a ≤ empiricalMean X n ω} := by
        ext; simp
      rw [this]
      refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
      exact measurableSet_le measurable_const (measurable_empiricalMean X h_meas n)
    rw [h_union]
    have h_compl : μ {ω | ¬∀ᶠ n in atTop, a ≤ empiricalMean X n ω} = 0 := by
      rw [← ae_iff]
      exact h_eventually_large
    have h_compl_eq : {ω | ∀ᶠ n in atTop, a ≤ empiricalMean X n ω}ᶜ =
        {ω | ¬∀ᶠ n in atTop, a ≤ empiricalMean X n ω} := by
      ext; simp
    rw [← prob_add_prob_compl (μ := μ) (h_union ▸ h_union_meas_set), h_compl_eq, h_compl,
      add_zero]
  have h_tend_S : Tendsto (fun k => μ (S k)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := μ) h_mono
    rw [h_union_meas] at this
    exact this
  have h_superset : ∀ k n, k ≤ n → S k ⊆ {ω | a ≤ empiricalMean X n ω} := by
    intro k n hkn ω hω
    exact hω n hkn
  have h_measure_ge : ∀ k n, k ≤ n → μ (S k) ≤ μ {ω | a ≤ empiricalMean X n ω} := by
    intro k n hkn
    exact measure_mono (h_superset k n hkn)
  have h_measure_le : ∀ n, μ {ω | a ≤ empiricalMean X n ω} ≤ 1 := by
    intro n
    exact prob_le_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h_tend_S tendsto_const_nhds
    (fun n => h_measure_ge n n le_rfl) h_measure_le

include h_indep h_meas h_ident h_mgf h_bdd in
/-- **Cramér's theorem** (upper bound): for i.i.d. random variables with finite MGF, the scaled
log-tail probability of the empirical mean is asymptotically bounded above by the negative rate
function, i.e. for every `a`,
`limsupₙ (1/n) log μ(a ≤ Sₙ/n) ≤ -upperTailRateFunction X μ a`. -/
theorem Cramer.limsup_le_neg_upperTailRateFunction : ∀ a : ℝ,
    limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) *
      ENNReal.log (μ {ω | a ≤ empiricalMean X n ω})) atTop
      ≤ (- Cramer.upperTailRateFunction X μ a : EReal) := by
  intro a
  by_cases h : μ[X 0] ≤ a
  · rw [Cramer.upperTailRateFunction, if_pos h]
    exact Cramer.limsup_le_neg_rateFunction X h_indep h_ident h_meas h_mgf h_bdd a h
  · norm_cast
    rw [Cramer.upperTailRateFunction, if_neg h]
    have h_prob_bound_2 : ∀ n : ℕ, n ≠ 0 →
        1 / ↑n * (μ {ω | a ≤ empiricalMean X n ω}).log ≤ 0 := by
      intro n h_n_nonneg
      have h_log_nonpos : (μ {ω | a ≤ empiricalMean X n ω}).log ≤ 0 := by
        rw [ENNReal.log_le_zero_iff]
        exact prob_le_one
      rw [EReal.mul_nonpos_iff]
      left
      constructor
      · rw [div_eq_mul_inv, one_mul]
        apply EReal.inv_nonneg_of_nonneg
        have : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_n_nonneg)
        exact EReal.coe_nonneg.mpr (le_of_lt this)
      · exact h_log_nonpos
    simp only [neg_zero]
    apply Filter.limsup_le_of_le
    · exact isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
    · apply Filter.eventually_atTop.mpr
      use 1
      intro n hn
      exact h_prob_bound_2 n (Nat.one_le_iff_ne_zero.mp hn)

include h_indep h_meas h_ident h_mgf h_bdd h_non_deg h_exposed in
/-- **Cramér's theorem** (lower bound): for i.i.d. random variables with finite MGF, the scaled
log-tail probability of the empirical mean is asymptotically bounded below by the negative rate
function, i.e. for every `a`,
`-upperTailRateFunction X μ a ≤ liminfₙ (1/n) log μ(a ≤ Sₙ/n)`. -/
theorem Cramer.neg_upperTailRateFunction_le_liminf : ∀ a : ℝ,
    (- Cramer.upperTailRateFunction X μ a : EReal) ≤
      liminf (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) *
        ENNReal.log (μ {ω | a ≤ empiricalMean X n ω})) atTop := by
  intro a
  by_cases h : μ[X 0] ≤ a
  · rw [Cramer.upperTailRateFunction, if_pos h]
    exact Cramer.neg_rateFunction_le_liminf X h_indep h_ident h_meas h_mgf h_bdd h_non_deg
      h_exposed a h
  · rw [Cramer.upperTailRateFunction, if_neg h]
    norm_cast
    rw [neg_zero]
    have h_a_lt_mean : a < μ[X 0] := not_le.mp h
    have h_prob_to_one :
        Tendsto (fun n => (μ {ω | a ≤ empiricalMean X n ω} : ENNReal)) atTop (𝓝 1) :=
      Cramer.tendsto_measure_empiricalMean_ge_of_lt_integral X h_indep h_ident h_meas h_mgf a
        h_a_lt_mean
    have h_seq_to_zero : Tendsto (fun (n : ℕ) =>
        1 / ((n : ℝ) : EReal) * (μ {ω | a ≤ empiricalMean X n ω}).log) atTop
        (𝓝 (0 : EReal)) := by
      have h_log_to_zero : Tendsto (fun n => (μ {ω | a ≤ empiricalMean X n ω}).log) atTop
          (𝓝 (0 : EReal)) := by
        simpa [ENNReal.log_one, Function.comp_def] using
          (ENNReal.continuous_log.tendsto 1).comp h_prob_to_one
      have h_inv_to_zero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) : EReal)) atTop (𝓝 0) := by
        simpa using EReal.tendsto_const_div_atTop_nhds_zero_nat
          (C := ((1 : ℝ) : EReal)) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
      simpa using EReal.Tendsto.mul h_inv_to_zero h_log_to_zero
        (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))
        (Or.inl (EReal.coe_ne_bot 0)) (Or.inl (EReal.coe_ne_top 0))
    have h_lim_eq : liminf (fun (n : ℕ) =>
        1 / ((n : ℝ) : EReal) * (μ {ω | a ≤ empiricalMean X n ω}).log) atTop
        = (0 : EReal) := Filter.Tendsto.liminf_eq h_seq_to_zero
    have : liminf (fun n : ℕ =>
        1 / (n : EReal) * (μ {ω | a ≤ empiricalMean X n ω}).log) atTop = 0 := h_lim_eq
    rw [this]
    norm_cast

end ProbabilityTheory
