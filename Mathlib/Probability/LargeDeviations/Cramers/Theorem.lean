/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.LowerBound
public import Mathlib.Probability.LargeDeviations.Cramers.UpperBound
public import Mathlib.Probability.LargeDeviations.Defs
public import Mathlib.Probability.StrongLaw

/-!
# Cramér's Theorem

This file proves the main result:

- `cramers_theorem`: The empirical mean of i.i.d. random variables with finite MGF satisfies
  the Large Deviation Principle with rate function `upperTailRateFunction X`.

The proof combines the upper and lower bounds from `UpperBound.lean` and `LowerBound.lean`,
and handles the case `a < 𝔼[X 0]` using the strong law of large numbers.
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped BigOperators ENNReal

@[expose] public section

variable {Ω : Type*} [MeasureSpace Ω]
variable (X : ℕ → Ω → ℝ)

/- Assumptions for Cramér's theorem -/
variable (h_indep : iIndepFun X ℙ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_int : Integrable (X 0) ℙ)
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) ℙ t)))
variable (h_non_deg : ∀ t : ℝ, 0 < iteratedDeriv 2 (cgf (X 0) ℙ) t)
variable (h_exposed : ∀ a : ℝ, 𝔼[X 0] ≤ a → ∃ t, deriv (cgf (X 0) ℙ) t = a)
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

/-- If a sequence of `ENNReal` values tends to 1, then their logs tend to 0. -/
private lemma ennreal_log_tendsto_zero_of_tendsto_one {f : ℕ → ℝ≥0∞}
    (h : Tendsto f atTop (𝓝 1)) :
    Tendsto (fun n => (f n).log) atTop (𝓝 0) := by
  have h' := (ENNReal.continuous_log.tendsto (1 : ℝ≥0∞)).comp h
  convert h'
  simp [ENNReal.log_one]

/-- The sequence `1/n → 0` in `EReal`. -/
private lemma ereal_inv_nat_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) : EReal)) atTop (𝓝 0) := by
  have : (fun n : ℕ => 1 / ((n : ℝ) : EReal)) = fun (n : ℕ) => (1 : EReal) / n := by
    funext n; rfl
  rw [this]
  exact (EReal.tendsto_const_div_atTop_nhds_zero_nat (by decide) (by decide))

/-- Product of two sequences tending to 0 tends to 0 in `EReal`. -/
private lemma ereal_mul_tendsto_zero_of_tendsto_zero_of_bounded
    {f g : ℕ → EReal} (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  simpa using EReal.Tendsto.mul hf hg (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))
    (Or.inl (EReal.coe_ne_bot 0)) (Or.inl (EReal.coe_ne_top 0))

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

include h_indep h_meas h_ident h_int in
/-- If `a < 𝔼[X 0]`, `ℙ(Sₙ/n ≥ a) → 1` by the strong law of large numbers. -/
private lemma less_exp_imp_limit_prob_less_mean_one (a : ℝ) (h : a < 𝔼[X 0]) :
  Tendsto (fun n : ℕ => (ℙ {ω | a ≤ empiricalMean X n ω} : ENNReal)) atTop (𝓝 1) := by
  have h_pairwise : Pairwise (fun i j => IndepFun (X i) (X j) ℙ) :=
    fun i j hij => h_indep.indepFun hij
  -- Almost sure convergence: `ℙ(limₙ Sₙ/n = 𝔼[X]) = 1`
  have h_strong_law :
      ∀ᵐ ω ∂ℙ, Tendsto (fun n : ℕ => empiricalMean X n ω) atTop (𝓝 𝔼[X 0]) := by
    have h_orig := strong_law_ae_real X h_int h_pairwise h_ident
    filter_upwards [h_orig] with ω hω
    have h_eq : (fun n : ℕ => empiricalMean X n ω) =
        (fun n => (∑ i ∈ Finset.range n, X i ω) / n) := by
      ext n
      unfold empiricalMean partialSum
      rw [Finset.sum_apply]
    rwa [h_eq]
  have h_gap : 0 < 𝔼[X 0] - a := sub_pos.mpr h
  set ε := (𝔼[X 0] - a) / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hε_bound : a + ε < 𝔼[X 0] := by linarith
  have h_conv_set : ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, |empiricalMean X n ω - 𝔼[X 0]| < ε := by
    filter_upwards [h_strong_law] with ω hω
    have h_tend := (Metric.tendsto_nhds.mp hω) ε hε_pos
    filter_upwards [h_tend] with n hn
    rwa [Real.dist_eq] at hn
  have h_eventually_large : ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, a ≤ empiricalMean X n ω := by
    filter_upwards [h_conv_set] with ω hω
    filter_upwards [hω] with n hn
    have : 𝔼[X 0] - ε < empiricalMean X n ω := by
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
  have h_union_meas : ℙ (⋃ k, S k) = 1 := by
    have h_union_meas_set : MeasurableSet (⋃ k, S k) := by
      refine MeasurableSet.iUnion fun k => ?_
      change MeasurableSet {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω}
      have : {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω} =
          ⋂ n, ⋂ (_ : k ≤ n), {ω | a ≤ empiricalMean X n ω} := by
        ext; simp
      rw [this]
      refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
      refine measurableSet_le measurable_const ?_
      convert (Finset.measurable_sum (Finset.range n)
        (fun i _ => h_meas i)).div_const (n : ℝ) using 1
      ext ω
      simp only [empiricalMean, partialSum, Finset.sum_apply]
    rw [h_union]
    have h_compl : ℙ {ω | ¬∀ᶠ n in atTop, a ≤ empiricalMean X n ω} = 0 := by
      rw [← ae_iff]
      exact h_eventually_large
    have h_compl_eq : {ω | ∀ᶠ n in atTop, a ≤ empiricalMean X n ω}ᶜ =
        {ω | ¬∀ᶠ n in atTop, a ≤ empiricalMean X n ω} := by
      ext; simp
    rw [← prob_add_prob_compl (μ := ℙ) (h_union ▸ h_union_meas_set), h_compl_eq, h_compl, add_zero]
  have h_tend_S : Tendsto (fun k => ℙ (S k)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ℙ) h_mono
    rw [h_union_meas] at this
    exact this
  have h_superset : ∀ k n, k ≤ n → S k ⊆ {ω | a ≤ empiricalMean X n ω} := by
    intro k n hkn ω hω
    exact hω n hkn
  have h_measure_ge : ∀ k n, k ≤ n → ℙ (S k) ≤ ℙ {ω | a ≤ empiricalMean X n ω} := by
    intro k n hkn
    exact measure_mono (h_superset k n hkn)
  have h_measure_le : ∀ n, ℙ {ω | a ≤ empiricalMean X n ω} ≤ 1 := by
    intro n
    exact prob_le_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h_tend_S tendsto_const_nhds
    (fun n => h_measure_ge n n le_rfl) h_measure_le

include h_indep h_meas h_ident h_mgf h_int h_bdd h_non_deg h_exposed h_clt_axiom in
/-- **Cramér's Theorem**: For iid. random variables with finite MGF, the empirical mean
satisfies a Large Deviation Principle with rate function being the Legendre transform of the CGF. -/
theorem cramers_theorem :
    LargeDeviationPrinciple (empiricalMean X) (upperTailRateFunction X) := by
  constructor
  · intro a
    by_cases h : 𝔼[X 0] ≤ a
    · rw [upperTailRateFunction, if_pos h]
      exact cramer_upper_bound X h_indep h_ident h_meas h_int h_mgf h_bdd a h
    · norm_cast
      rw [upperTailRateFunction, if_neg h]
      have h_prob_bound_2 : ∀ n : ℕ, n ≠ 0 →
          1 / ↑n * (ℙ {ω | empiricalMean X n ω ≥ a}).log ≤ 0 := by
        intro n h_n_nonneg
        have h_log_nonpos : (ℙ {ω | empiricalMean X n ω ≥ a}).log ≤ 0 := by
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
  · intro a
    by_cases h : 𝔼[X 0] ≤ a
    · rw [upperTailRateFunction, if_pos h]
      exact cramer_lower_bound X h_indep h_ident h_meas h_int h_mgf h_bdd h_non_deg h_exposed
        h_clt_axiom a h
    · rw [upperTailRateFunction, if_neg h]
      norm_cast
      rw [neg_zero]
      have h_a_lt_mean : a < 𝔼[X 0] := not_le.mp h
      have h_prob_to_one :
          Tendsto (fun n => (ℙ {ω | a ≤ empiricalMean X n ω} : ENNReal)) atTop (𝓝 1) :=
        @less_exp_imp_limit_prob_less_mean_one Ω _ X h_indep h_ident h_meas h_int _ a
          h_a_lt_mean
      have h_seq_to_zero : Tendsto (fun (n : ℕ) =>
          1 / ((n : ℝ) : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop
          (𝓝 (0 : EReal)) := by
        have h_log_to_zero : Tendsto (fun n => (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop (𝓝 0) :=
          ennreal_log_tendsto_zero_of_tendsto_one h_prob_to_one
        have h_inv_to_zero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) : EReal)) atTop (𝓝 0) :=
          ereal_inv_nat_tendsto_zero
        have h_log_ereal :
            Tendsto (fun n => (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop
              (𝓝 (0 : EReal)) := h_log_to_zero
        exact ereal_mul_tendsto_zero_of_tendsto_zero_of_bounded h_inv_to_zero h_log_ereal
      have h_lim_eq : liminf (fun (n : ℕ) =>
          1 / ((n : ℝ) : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop
          = (0 : EReal) := Filter.Tendsto.liminf_eq h_seq_to_zero
      have : liminf (fun n : ℕ =>
          1 / (n : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop = 0 := by
        convert h_lim_eq using 2
      rw [this]
      norm_cast
