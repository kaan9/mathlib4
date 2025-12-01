/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.Basic

/-!
# Cramér's Theorem — Lower Bound

This file proves the lower (exponential tilting) bound for Cramér's theorem:

- `cramer_lower_bound`: For any `a ≥ 𝔼[X 0]`, `liminf n⁻¹ * log ℙ(Sₙ/n ≥ a) ≥ -I(a)`.

The proof uses the change-of-measure approach with the family of tilted measures
`ℚₙₜ = ℙ.tilted(t * Sₙ)` where `t` is chosen so that `cgf'(t) = a`.
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

omit [MeasureSpace Ω] in
/-- `0 < t` and `Sₙ/n ∈ [a, a + δ]` implies `exp(-t · Sₙ) ≥ exp(-t · n · (a + δ))` -/
private lemma exp_neg_mul_S_ge_on_set (t : ℝ) (n : ℕ) (a δ : ℝ) (ht : 0 ≤ t)
    (ω : Ω) (hω : empiricalMean X n ω ∈ Set.Icc a (a + δ)) :
    Real.exp (-t * partialSum X n ω) ≥ Real.exp (-t * n * (a + δ)) := by
  apply Real.exp_le_exp.mpr
  rw [empiricalMean, partialSum] at hω
  have h_upper := hω.2
  by_cases hn : n = 0
  · simp [hn, partialSum]
  · have h_S_bound : partialSum X n ω ≤ n * (a + δ) := by
      calc partialSum X n ω = (partialSum X n ω / n) * n := by field_simp
        _ ≤ (a + δ) * n := mul_le_mul_of_nonneg_right h_upper (Nat.cast_nonneg n)
        _ = n * (a + δ) := by ring
    calc -t * n * (a + δ) = -(t * n * (a + δ)) := by ring
      _ ≤ -(t * partialSum X n ω) := by
          apply neg_le_neg
          calc t * partialSum X n ω ≤ t * (n * (a + δ)) := mul_le_mul_of_nonneg_left h_S_bound ht
            _ = t * n * (a + δ) := by ring
      _ = -t * partialSum X n ω := by ring

include h_indep h_ident h_meas h_int h_mgf h_non_deg h_clt_axiom in
/-- `ℚₙₜ(Sₙ/n ∈ [a, a+δ])` is eventually always positive as `n → ∞`.
That is, `∃ c > 0` s.t. `ℚₙₜ(Sₙ/n ∈ [a, a+δ]) > c` for all sufficiently large `n`.
This is a consequence of the Central Limit Theorem assumption. -/
private lemma tilted_window_lower_bound_from_concentration (a t δ : ℝ) (hδ : 0 < δ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    ∃ c > 0, ∀ᶠ n in atTop,
      c ≤ ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal := by
  use 1/4
  constructor
  · norm_num
  · have h_bound : ∀ᶠ n in atTop,
      (1 / 2 - 1 / 4 : ℝ) ≤ ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal :=
    h_clt_axiom h_indep h_ident h_meas h_int h_mgf h_non_deg t a δ hδ (1/4) (by norm_num) ht_deriv
    rw [Filter.eventually_atTop] at h_bound ⊢
    obtain ⟨N, hN⟩ := h_bound
    use N
    intro n hn
    have h := hN n hn
    norm_num at h
    exact h

/-- `(1 / ↑n) · ↑c → 0` where we lift to `EReal` from `ℝ`. -/
private lemma ereal_inv_nat_mul_const_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * (c : EReal)) atTop (𝓝 0) := by
  have h_real : Tendsto (fun n : ℕ => (1 / n * c : ℝ)) atTop (𝓝 0) := by
    have h_inv : Tendsto (fun n : ℕ => (1 / n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    convert h_inv.mul tendsto_const_nhds using 1
    ext n
    ring_nf
  rw [show (0 : EReal) = ((0 : ℝ) : EReal) by rfl]
  refine continuous_coe_real_ereal.continuousAt.tendsto.comp ?_
  convert h_real using 1

/-- For `y ∈ (0, ∞)` and `n ≥ 1`, `n⁻¹ log(exp(x) · y) = n⁻¹x + n⁻¹ · log(y)`, where we lift
    values to EReal and ENNReal where needed for later results. -/
private lemma log_product_split (n : ℕ) (x : ℝ) (y : ENNReal) (hn : n ≥ 1)
    (hy_ne_zero : y ≠ 0) (hy_ne_top : y ≠ ⊤) :
    ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp x * y.toReal)) =
    ((1 : ℝ) / n : EReal) * (x : EReal) + ((1 : ℝ) / n : EReal) * ENNReal.log y := by
  have hy_pos : 0 < y.toReal := ENNReal.toReal_pos hy_ne_zero hy_ne_top
  have h_prod_pos : 0 < Real.exp x * y.toReal := mul_pos (Real.exp_pos x) hy_pos
  have h_log_eq : ENNReal.log (ENNReal.ofReal (Real.exp x * y.toReal)) =
      (x : EReal) + ENNReal.log y := by
    rw [ENNReal.log_ofReal_of_pos h_prod_pos]
    rw [Real.log_mul (Real.exp_pos x).ne' hy_pos.ne', Real.log_exp]
    rw [ENNReal.log_pos_real hy_ne_zero hy_ne_top]
    rw [EReal.coe_add]
  rw [h_log_eq]
  have h_coef_nonneg : 0 ≤ ((1 : ℝ) / n : EReal) := by
    apply EReal.coe_nonneg.mpr
    positivity
  have h_coef_ne_top : ((1 : ℝ) / n : EReal) ≠ ⊤ := EReal.coe_ne_top _
  exact EReal.left_distrib_of_nonneg_of_ne_top h_coef_nonneg h_coef_ne_top _ _

/-- For `y ∈ (0, ∞)` and `n ≥ 1`,
  `n⁻¹ log(exp(-n (t · (a + δ) - l)) · y) = -(ta - l) - tδ + n⁻¹ log(y)`
  which we will later use with `l := Λ(t)` -/
private lemma log_exp_product_eq_neg_coef_plus_log (n : ℕ) (t a δ : ℝ) (l : ℝ)
    (y : ENNReal) (hn : n ≥ 1) (hy_ne_zero : y ≠ 0) (hy_ne_top : y ≠ ⊤) :
    ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal
      (Real.exp (-n * (t * (a + δ) - l)) * y.toReal)) =
    (-(t * a - l) - t * δ : EReal) + ((1 : ℝ) / n : EReal) * ENNReal.log y := by
  rw [log_product_split n _ y hn hy_ne_zero hy_ne_top]
  congr 1
  have : ((1 : ℝ) / n : EReal) * (-n * (t * (a + δ) - l) : EReal) =
      (-(t * a - l) - t * δ : EReal) := by
    have h_eq : (1 / (n : ℝ)) * (-n * (t * (a + δ) - l)) =
        -(t * a - l) - t * δ := by field_simp; ring
    simp only [← EReal.coe_mul]
    exact congrArg (fun x : ℝ => (x : EReal)) h_eq
  convert this using 2

/-- Given `c ∈ [-∞,∞]` and `f(n) → 0` as `n → ∞`, `f(n) + c → c` as `n → ∞` -/
private lemma tendsto_const_add_vanishing (c : EReal) (f : ℕ → EReal)
    (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c + f n) atTop (𝓝 c) := by
  have h_cont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (c, 0) := by
    apply EReal.continuousAt_add <;> simp
  simpa [add_zero] using h_cont.tendsto.comp (tendsto_const_nhds.prodMk_nhds h)

/-- Given `x, y ∈ [-∞, ∞]`, if `∀ε ∈ ℝ⁺, x - ε ≤ y`, then `x ≤ y`. -/
private lemma EReal.le_of_forall_pos_sub_le {x y : EReal}
    (h : ∀ ε : ℝ, 0 < ε → x - (ε : EReal) ≤ y) : x ≤ y := by
  induction x using EReal.rec
  case bot =>
    exact bot_le
  case coe x_val =>
    induction y using EReal.rec
    case bot =>
      specialize h 1 zero_lt_one
      simp only [EReal.coe_one] at h
      have h_eq_bot : (x_val - 1 : EReal) = ⊥ := le_bot_iff.mp h
      exact absurd h_eq_bot (EReal.coe_ne_bot _)
    case coe y_val =>
      norm_cast
      by_contra h_not_le
      push Not at h_not_le
      have hε_pos : 0 < (x_val - y_val) / 2 := by linarith
      specialize h ((x_val - y_val) / 2) hε_pos
      norm_cast at h
      linarith
    case top =>
      exact le_top
  case top =>
    specialize h 1 zero_lt_one
    rw [EReal.top_sub_coe] at h
    exact h

/-! ### Lemmas requiring IsProbabilityMeasure -/

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- For an event `E ⊆ Ω` and a random variable `f : Ω → ℝ`, we have  `ℙ(E) = 𝔼[eᶠ] ∫_E exp(-f) dℙ_f`
where `ℙ_f` is the measure `ℙ` exponentially tilted with respect to `f`. That is, it has density
proportional to `exp(f)`. -/
private lemma measure_eq_integral_exp_neg_tilted (f : Ω → ℝ) (E : Set Ω)
    (h_int : Integrable (fun ω => Real.exp (f ω)) ℙ)
    (hE : MeasurableSet E) :
    (ℙ E).toReal =
      (𝔼[fun ω => Real.exp (f ω)]) * (∫ ω in E, Real.exp (-f ω) ∂(Measure.tilted ℙ f)) := by
  rw [setIntegral_tilted' f (fun ω => Real.exp (-f ω)) hE]
  simp only [smul_eq_mul]
  have h_pos : 0 < 𝔼[fun x => Real.exp (f x)] := integral_exp_pos h_int
  have h_ne : 𝔼[fun x => Real.exp (f x)] ≠ 0 := ne_of_gt h_pos
  conv_rhs => arg 2; arg 2; ext ω; rw [div_mul_eq_mul_div, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_div]
  rw [setIntegral_const, smul_eq_mul]
  field_simp
  rw [Measure.real]

include h_indep h_ident h_meas h_mgf in
/-- `ℙ(Sₙ/n ∈ [a, a + δ]) ≥ exp(-n(ta - Λ(t))) · ℚₙₜ(Sₙ/n ∈ [a, a + δ])` -/
lemma change_of_measure_lower_bound (a δ t : ℝ) (n : ℕ)
    (_hδ : 0 < δ) (ht : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * partialSum X n ω)) ℙ) :
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    (ℙ E).toReal ≥
      Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
      ((ℚₙₜ X ℙ n t) E).toReal := by
  intro E
  have hE : MeasurableSet E := by
    have h_emp : Measurable (empiricalMean X n) := by
      have hS : Measurable (partialSum X n) := by
        have h_sum := Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i)
        have h_eq : partialSum X n = fun ω => ∑ i ∈ Finset.range n, X i ω := by
          ext ω
          unfold partialSum
          rw [Finset.sum_apply]
        rw [h_eq]
        exact h_sum
      exact hS.div_const _
    exact measurableSet_Icc.preimage h_emp
  rw [measure_eq_integral_exp_neg_tilted (fun ω => t * partialSum X n ω) E h_int hE]
  change mgf (partialSum X n) ℙ t * _ ≥ _
  rw [mgf_sum_eq_exp_n_prod_cgf X h_indep h_ident h_meas h_mgf n t]
  have h_bound :
      ∫ ω in E, Real.exp (-t * partialSum X n ω)
        ∂(ℚₙₜ X ℙ n t) ≥
      Real.exp (-t * n * (a + δ)) *
        ((ℚₙₜ X ℙ n t) E).toReal := by
    have h_ge : ∀ ω ∈ E, Real.exp (-t * n * (a + δ)) ≤ Real.exp (-t * partialSum X n ω) := by
      intro ω hω
      exact exp_neg_mul_S_ge_on_set X t n a δ (le_of_lt ht) ω hω
    haveI : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
      isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
    calc ∫ ω in E, Real.exp (-t * partialSum X n ω)
        ∂(ℚₙₜ X ℙ n t)
        ≥ ∫ ω in E, Real.exp (-t * n * (a + δ))
          ∂(ℚₙₜ X ℙ n t) :=
          setIntegral_mono_on
            (by apply Integrable.integrableOn; apply integrable_const)
            (by apply Integrable.integrableOn
                have h_Q_def : ℚₙₜ X ℙ n t = Measure.tilted ℙ (fun ω => t * partialSum X n ω) := rfl
                rw [h_Q_def]
                rw [integrable_tilted_iff h_int]
                have : (fun ω ↦ Real.exp (t * partialSum X n ω) •
                    Real.exp (-t * partialSum X n ω)) = fun ω ↦ 1 := by
                  ext ω
                  simp only [smul_eq_mul]
                  rw [← Real.exp_add]
                  ring_nf
                  norm_num
                rw [this]
                rw [integrable_const_iff]
                right
                infer_instance)
            hE h_ge
      _ = ((ℚₙₜ X ℙ n t).real E) •
            Real.exp (-t * n * (a + δ)) := setIntegral_const _
      _ = Real.exp (-t * n * (a + δ)) *
            ((ℚₙₜ X ℙ n t) E).toReal := by
          rw [Measure.real, smul_eq_mul]; ring
  have key : Real.exp (n * cgf (X 0) ℙ t) *
      (Real.exp (-t * n * (a + δ)) *
        ((ℚₙₜ X ℙ n t) E).toReal) =
    Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
      ((ℚₙₜ X ℙ n t) E).toReal := by
    ring_nf
    have : n * cgf (X 0) ℙ t + (-(n * t * a) - n * t * δ) =
        -n * (t * (a + δ) - cgf (X 0) ℙ t) := by ring_nf
    rw [← Real.exp_add, this]; ring_nf
  rw [← key]
  gcongr
  convert h_bound.le using 2
  ext ω; ring_nf

include h_indep h_ident h_meas h_int h_mgf h_non_deg h_clt_axiom in
/-- The error term `n⁻¹ * log(ℚₙₜ(Sₙ/n ∈ [a, a+δ])) → 0` as `n → ∞` -/
private lemma error_term_vanishes (a t δ : ℝ) (hδ : 0 < δ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    Tendsto (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})) atTop (𝓝 0) := by
  obtain ⟨c, hc_pos, h_bounded⟩ :=
    tilted_window_lower_bound_from_concentration X h_indep h_ident h_meas h_int h_mgf h_non_deg
      h_clt_axiom a t δ hδ ht_deriv
  have h_log_c_real : ENNReal.log (ENNReal.ofReal c) = ((Real.log c) : EReal) := by
    have : 0 < c := hc_pos
    simp [ENNReal.log_ofReal, this]
  have h_lower_tendsto : Tendsto (fun m : ℕ =>
      ((1 : ℝ) / m : EReal) * ENNReal.log (ENNReal.ofReal c)) atTop (𝓝 0) := by
    rw [h_log_c_real]
    exact ereal_inv_nat_mul_const_tendsto_zero (Real.log c)
  have h_upper_tendsto : Tendsto (fun (_ : ℕ) => (0 : EReal)) atTop (𝓝 0) := tendsto_const_nhds
  -- `0 ≤ a` and `b ≤ 0` implies `a * b ≤ 0` in `EReal`.
  have h_ereal_mul_nonneg_nonpos {a b : EReal} (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
    calc a * b
        ≤ a * 0 := by exact mul_le_mul_of_nonneg_left hb ha
      _ = 0 := mul_zero a
  have h_eventually : ∀ᶠ (m : ℕ) in atTop,
      ((1 : ℝ) / m : EReal) * ENNReal.log (ENNReal.ofReal c)
      ≤ ((1 : ℝ) / m : EReal) * ENNReal.log ((ℚₙₜ X ℙ m t)
          {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)})
      ∧ ((1 : ℝ) / m : EReal) * ENNReal.log ((ℚₙₜ X ℙ m t)
          {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)})
      ≤ 0 := by
    filter_upwards [h_bounded, Filter.eventually_gt_atTop (0 : ℕ)]
    intro (m : ℕ) (hm_bound : c ≤ ((ℚₙₜ X ℙ m t)
        {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)}).toReal) (hm_pos : 0 < m)
    constructor
    · have h_div_nn : 0 ≤ ((1 : ℝ) / m : EReal) := by
        exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg m))
      apply mul_le_mul_of_nonneg_left _ h_div_nn
      apply ENNReal.log_le_log
      haveI : IsProbabilityMeasure (ℚₙₜ X ℙ m t) :=
        isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t m
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      exact hm_bound
    · apply h_ereal_mul_nonneg_nonpos
      · exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg m))
      · calc ENNReal.log ((ℚₙₜ X ℙ m t)
                {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)})
            ≤ ENNReal.log 1 := by
              apply ENNReal.log_le_log
              haveI : IsProbabilityMeasure (ℚₙₜ X ℙ m t) :=
                isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t m
              trans (ℚₙₜ X ℙ m t) Set.univ
              · apply measure_mono
                exact Set.subset_univ _
              · exact IsProbabilityMeasure.measure_univ.le
          _ = 0 := ENNReal.log_one
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto
    (h_eventually.mono fun m h => h.1) (h_eventually.mono fun m h => h.2)

include h_indep h_ident h_meas h_int h_mgf h_non_deg h_clt_axiom in
/-- For `δ,t > 0` with `Λ'(t) = a`, we have `liminfₙ n⁻¹ log ℙ(Sₙ/n ≥ a) ≥ -(ta - Λ(t)) - tδ ` -/
private lemma lower_bound_via_tilted (a t δ : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    liminf (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
    ≥ (-(t * a - cgf (X 0) ℙ t) : EReal) - (t * δ : EReal) := by
  -- `n⁻¹ log ℙ(Sₙ/n ≥ a) ≥ (ta - Λ(t)) - tδ + n⁻¹ log ℚₙₜ(Sₙ/n ∈ [a, a + δ])`
  have h_pointwise : ∀ n : ℕ, n ≥ 1 →
      ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})
      ≥ (-(t * a - cgf (X 0) ℙ t) - t * δ : EReal)
        + ((1 : ℝ) / n : EReal) * ENNReal.log ((ℚₙₜ X ℙ n t)
            {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}) := by
    intro n hn
    have h_subset : {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)} ⊆
        {ω | empiricalMean X n ω ≥ a} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_Icc] at hω ⊢
      exact hω.1
    have h_integrable := integrable_exp_sum X h_indep h_ident h_meas h_mgf t n
    have h_change := @change_of_measure_lower_bound _ _ X h_indep h_ident h_meas h_mgf _
      a δ t n hδ ht h_integrable
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    let F := {ω | empiricalMean X n ω ≥ a}
    have h_prob_mono : (ℙ F).toReal ≥ (ℙ E).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono h_subset
    have h_lower : (ℙ E).toReal ≥
        Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
        ((ℚₙₜ X ℙ n t) E).toReal :=
      h_change
    have h_combined : (ℙ F).toReal ≥
        Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
        ((ℚₙₜ X ℙ n t) E).toReal := by
      linarith [h_prob_mono, h_lower]
    have h_log_ineq : ENNReal.log (ℙ F) ≥
        ENNReal.log (ENNReal.ofReal (Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
          ((ℚₙₜ X ℙ n t) E).toReal)) := by
      apply ENNReal.log_le_log
      haveI : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
        isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      exact h_combined
    have h_div_nn : 0 ≤ ((1 : ℝ) / n : EReal) := by
      exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg n))
    calc ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ F)
        ≥ ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal
            (Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
              ((ℚₙₜ X ℙ n t) E).toReal)) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast h_log_ineq) h_div_nn
      _ = (-(t * a - cgf (X 0) ℙ t) - t * δ : EReal)
          + ((1 : ℝ) / n : EReal) *
            ENNReal.log ((ℚₙₜ X ℙ n t) E) := by
        by_cases h_tilted_zero : (ℚₙₜ X ℙ n t) E = 0
        · rw [h_tilted_zero]
          simp only [ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
          have h1n_pos : (0 : EReal) < ((1 : ℝ) / n : EReal) := by
            apply EReal.coe_pos.mpr
            positivity
          rw [EReal.mul_bot_of_pos h1n_pos]
          simp only [EReal.add_bot]
        · refine log_exp_product_eq_neg_coef_plus_log n t a δ (cgf (X 0) ℙ t) _ hn ?_ ?_
          · exact h_tilted_zero
          · haveI : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
              isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
            exact measure_ne_top _ _
  -- The error term `n⁻¹ log ℚₙₜ(Sₙ/n ∈ [a, a + δ])` vanishes as `n → ∞`.
  have h_error_vanish := @error_term_vanishes _ _ X h_indep h_ident h_meas h_int h_mgf h_non_deg
    h_clt_axiom _ a t δ hδ ht_deriv
  let rhs_seq : ℕ → EReal := fun n =>
    (-(t * a - cgf (X 0) ℙ t) - t * δ : EReal)
    + ((1 : ℝ) / n : EReal) * ENNReal.log ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})
  have h_rhs_limit : Tendsto rhs_seq atTop
      (𝓝 ((-(t * a - cgf (X 0) ℙ t) : EReal) - (t * δ : EReal))) :=
    tendsto_const_add_vanishing _ _ h_error_vanish
  -- Combine the pointwise inequality and vanishing error term to conclude
  have h_eventually : ∀ᶠ (n : ℕ) in atTop,
      ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})
      ≥ rhs_seq n := by
    rw [Filter.eventually_atTop]
    use 1
    intro (m : ℕ) hm
    exact h_pointwise m hm
  rw [← h_rhs_limit.liminf_eq]
  exact liminf_le_liminf h_eventually

include X h_mgf h_non_deg in
/-- If `a ≥ 𝔼[X₁]` and `Λ'(t) = a`, then `0 ≤ t` -/
private lemma deriv_cgf_nonneg_of_ge_mean (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) (t : ℝ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    0 ≤ t := by
  by_contra ht_neg
  push Not at ht_neg
  have h_zero_in_int : (0 : ℝ) ∈ interior (integrableExpSet (X 0) ℙ) :=
    mem_interior_integrableExpSet X h_mgf 0
  have h_deriv_zero : deriv (cgf (X 0) ℙ) 0 = 𝔼[X 0] := by
    rw [deriv_cgf_zero h_zero_in_int]
    simp
  have h_strict_mono : StrictMono (deriv (cgf (X 0) ℙ)) := by
    apply strictMono_of_deriv_pos
    intro x
    rw [← iteratedDeriv_one]
    have : 0 < iteratedDeriv 2 (cgf (X 0) ℙ) x := h_non_deg x
    simpa [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (cgf (X 0) ℙ) t < deriv (cgf (X 0) ℙ) 0 := h_strict_mono ht_neg
  rw [ht_deriv, h_deriv_zero] at this
  linarith

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
include X h_mgf h_bdd h_non_deg in
/-- Given `Λ'(t) = a`, the rate function satisfies `I(a) = ta - Λ(t)`. -/
private lemma rateFunction_eq_of_deriv_eq (a t : ℝ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    I X a = t * a - cgf (X 0) ℙ t := by
  rw [I]
  -- We proceed by proving inequality in both directions
  apply le_antisymm
  · -- Sub-goal `I(a) = supₛ (sa - Λ(s)) ≤ ta - Λ(t)`
    -- We wish to show, for every `s`, that `sa - Λ(s) ≤ ta - Λ(t)`. Rearranging, we get
    -- `Λ(s) ≥ Λ(t) + a(s - t)` and it suffices to show that the CGF `Λ(s)` is above the tangent
    -- line `Λ(t) + a(s - t)`.
    apply ciSup_le
    intro s
    -- Show that `Λ(s)` is strictly convex, which follows from assumption `h_non_deg` (`Λ''(x) > 0`)
    have h_convex : StrictConvexOn ℝ Set.univ (cgf (X 0) ℙ) := by
      apply strictConvexOn_of_deriv2_pos' convex_univ
      · have h_analytic : AnalyticOn ℝ (cgf (X 0) ℙ) Set.univ := by
          have h : interior (integrableExpSet (X 0) ℙ) = Set.univ :=
            Set.eq_univ_of_forall (mem_interior_integrableExpSet X h_mgf)
          rw [← h]; exact analyticOn_cgf
        exact h_analytic.continuousOn
      · intro x _
        rw [← iteratedDeriv_eq_iterate]
        exact h_non_deg x
    -- `Λ(s)` is differentiable at `t` (since it's differentiable everywhere)
    have h_diff : DifferentiableAt ℝ (cgf (X 0) ℙ) t := by
      have h_analytic : AnalyticOn ℝ (cgf (X 0) ℙ) Set.univ := by
        have h : interior (integrableExpSet (X 0) ℙ) = Set.univ :=
          Set.eq_univ_of_forall (mem_interior_integrableExpSet X h_mgf)
        rw [← h]; exact analyticOn_cgf
      exact h_analytic.differentiableOn.differentiableAt
        (isOpen_univ.mem_nhds (Set.mem_univ t))
    -- A convex function is always above its tangent line.
    -- As `Λ'(t) = a`, the tangent line at t is `y = Λ(t) + a(x - t)`
    have h_tangent : cgf (X 0) ℙ s ≥ cgf (X 0) ℙ t + a * (s - t) := by
      rcases lt_trichotomy s t with hst | rfl | hts
      · have h_slope_bound := h_convex.convexOn.slope_le_of_hasDerivAt
          (Set.mem_univ s) (Set.mem_univ t) hst h_diff.hasDerivAt
        rw [ht_deriv] at h_slope_bound
        rw [slope_def_field] at h_slope_bound
        have ht_s_pos : 0 < t - s := sub_pos.mpr hst
        have : cgf (X 0) ℙ t - cgf (X 0) ℙ s ≤ a * (t - s) := by
          field_simp at h_slope_bound
          ring_nf at h_slope_bound ⊢
          exact h_slope_bound
        linarith
      · simp
      · have h_slope_bound := h_convex.convexOn.deriv_le_slope
          (Set.mem_univ t) (Set.mem_univ s) hts h_diff
        rw [ht_deriv] at h_slope_bound
        rw [slope_def_field] at h_slope_bound
        have hs_t_pos : 0 < s - t := sub_pos.mpr hts
        have : a * (s - t) ≤ cgf (X 0) ℙ s - cgf (X 0) ℙ t := by
          field_simp at h_slope_bound
          ring_nf at h_slope_bound ⊢
          exact h_slope_bound
        linarith
    -- Conclude by applying above hypotheses and rearranging terms
    linarith
  · -- Sub-goal `ta - Λ(t) ≤ supₛ (sa - Λ(s))`. This follows directly from the definition of `sup`.
    exact le_ciSup (h_bdd a) t

include h_indep h_ident h_meas h_int h_mgf h_bdd h_non_deg h_exposed h_clt_axiom in
/-- **Cramér's Theorem (Lower Bound)**: Given `a ≥ E[X 0]`, `-I(a) ≤ liminfₙ n⁻¹ log ℙ(Sₙ ≥ a)`. -/
theorem cramer_lower_bound (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    (- I X a : EReal) ≤
      liminf (fun n : ℕ =>
        ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop := by
  -- Get the `t` such that `Λ'(t) = a`.
  obtain ⟨t, ht_deriv⟩ := h_exposed a h_mean
  have ht_nonneg : 0 ≤ t := deriv_cgf_nonneg_of_ge_mean X h_mgf h_non_deg a h_mean t ht_deriv
  have h_rate_eq : I X a = t * a - cgf (X 0) ℙ t :=
    rateFunction_eq_of_deriv_eq X h_mgf h_bdd h_non_deg a t ht_deriv
  rw [h_rate_eq]
  let LHS_val :=
    liminf (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}))
      atTop
  -- Casework on whether `t = 0`
  by_cases ht_zero : t = 0
  · -- `t = 0` (which implies `a = 𝔼[X]` from solving `a = \Lamda'(t) = \Lamda'(0)`).
    subst ht_zero
    simp only [zero_mul, cgf_zero, sub_zero]
    -- `Var[X] > 0`
    have h_var_pos : 0 < variance (X 0) ℙ := by
      have h_int_zero : (0 : ℝ) ∈ interior (integrableExpSet (X 0) ℙ) :=
        mem_interior_integrableExpSet X h_mgf 0
      have h_eq : variance (X 0) ℙ = iteratedDeriv 2 (cgf (X 0) ℙ) 0 := by
        have h_zero_fun : (fun ω => 0 * X 0 ω) = fun _ => 0 := by
          ext ω
          simp [zero_mul]
        have : Measure.tilted ℙ (fun ω => 0 * X 0 ω) = ℙ := by
          simp_rw [h_zero_fun]
          exact tilted_zero ℙ
        calc variance (X 0) ℙ
            = variance (X 0) (Measure.tilted ℙ (fun ω => 0 * X 0 ω)) := by rw [this]
          _ = iteratedDeriv 2 (cgf (X 0) ℙ) 0 := variance_tilted_mul h_int_zero
      rw [h_eq]
      exact h_non_deg 0
    -- `∃ c > 0` such that for all sufficiently large `n`, `ℙ(Sₙ/n ≥ a) ≥ c`
    -- i.e. the asymptotic lower bound `ℙ(Sₙ/n ≥ a)` is greater than 0, which we derive from CLT
    -- on the tilted measures, noting that at `t = 0`, the tilted measures `ℚₙₜ` coincide with `ℙ`.
    have h_prob_lower_bound : ∃ c > 0, ∀ᶠ n in atTop,
        c ≤ (ℙ {ω | a ≤ empiricalMean X n ω}).toReal := by
      have h_bound := h_clt_axiom h_indep h_ident h_meas h_int h_mgf h_non_deg
        0 a 1 (by norm_num) (1/4) (by norm_num) ht_deriv
      refine ⟨1/4, by norm_num, ?_⟩
      filter_upwards [h_bound] with n hn
      have h_eq_meas : ℚₙₜ X ℙ n 0 = ℙ := by
        have h_def : ℚₙₜ X ℙ n 0 = Measure.tilted ℙ (fun ω => 0 * partialSum X n ω) := rfl
        rw [h_def]
        have h_zero : (fun ω => 0 * partialSum X n ω) = fun _ => 0 := by ext ω; simp [zero_mul]
        simp_rw [h_zero]
        exact tilted_zero ℙ
      rw [h_eq_meas] at hn
      have h_subset : {ω | empiricalMean X n ω ∈ Set.Icc a (a + 1)} ⊆
          {ω | a ≤ empiricalMean X n ω} := by
        intro ω hω
        exact hω.1
      have hn_bound : (1 / 4 : ℝ) ≤ (ℙ {ω | empiricalMean X n ω ∈ Set.Icc a (a + 1)}).toReal := by
        calc (1 / 4 : ℝ) = 1 / 2 - 1 / 4 := by norm_num
          _ ≤ (ℙ {ω | empiricalMean X n ω ∈ Set.Icc a (a + 1)}).toReal := hn
      calc
        (1 / 4 : ℝ) ≤ (ℙ {ω | empiricalMean X n ω ∈ Set.Icc a (a + 1)}).toReal := hn_bound
        _ ≤ (ℙ {ω | a ≤ empiricalMean X n ω}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (MeasureTheory.measure_mono h_subset)
    obtain ⟨c, hc_pos, h_eventually_lower⟩ := h_prob_lower_bound
    have h_log_c : ENNReal.log (ENNReal.ofReal c) = (Real.log c : EReal) := by
      simp [ENNReal.log_ofReal, hc_pos]
    have h_lower_tendsto :
        Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal c))
          atTop (𝓝 0) := by
      rw [h_log_c]
      exact ereal_inv_nat_mul_const_tendsto_zero (Real.log c)
    have h_upper_tendsto : Tendsto (fun (_ : ℕ) => (0 : EReal)) atTop (𝓝 0) := tendsto_const_nhds
    -- Establish bounds to apply squeeze theorem `n⁻¹ log (c) ≤ n⁻¹ log ℙ(Sₙ/n ≥ a) ≤ 0`
    have h_squeeze : ∀ᶠ (m : ℕ) in atTop,
        ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal c)
        ≤ ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X m ω})
        ∧ ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X m ω}) ≤ 0 := by
      filter_upwards [h_eventually_lower, Filter.eventually_gt_atTop (0 : ℕ)] with m hm_lower hm_pos
      constructor
      · have h_div_nn : 0 ≤ ((1 : ℝ) / m : EReal) := by
          exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg m))
        apply mul_le_mul_of_nonneg_left _ h_div_nn
        apply ENNReal.log_le_log
        rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
        exact hm_lower
      · apply mul_nonpos_of_nonneg_of_nonpos
        · exact EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg m))
        · rw [ENNReal.log_le_zero_iff]
          calc ℙ {ω | a ≤ empiricalMean X m ω}
            ≤ ℙ Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
    -- `n⁻¹ log ℙ(Sₙ/n ≥ a) → 0` by squeeze theorem
    have h_tendsto :
        Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X n ω}))
          atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto
        (h_squeeze.mono fun n hn => hn.1) (h_squeeze.mono fun n hn => hn.2)
    have h_liminf_eq := Filter.Tendsto.liminf_eq h_tendsto
    change -↑(0 : ℝ) ≤ LHS_val
    rw [show LHS_val =
      liminf (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X n ω}))
        atTop from rfl]
    rw [h_liminf_eq]
    simp
  have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)
  -- Bound the liminf from below for any fixed positive `δ` using the tilted measure bounds.
  have h_bound_for_all_delta : ∀ (δ : ℝ), 0 < δ →
      (-(t * a - cgf (X 0) ℙ t) - t * δ : EReal) ≤ LHS_val := by
    intro δ hδ
    have := lower_bound_via_tilted X h_indep h_ident h_meas h_int h_mgf h_non_deg h_clt_axiom
      a t δ hδ ht_pos ht_deriv
    exact this.le
  -- Conclude the lower bound by taking `δ → 0`.
  suffices ∀ ε : ℝ, 0 < ε → (-(t * a - cgf (X 0) ℙ t) - (ε : EReal) : EReal) ≤ LHS_val by
    exact EReal.le_of_forall_pos_sub_le this
  intro ε hε
  let δ := ε / t
  have hδ_pos : 0 < δ := div_pos hε ht_pos
  have h_delta_eq : t * δ = ε := by
    unfold δ
    field_simp
  calc (-(t * a - cgf (X 0) ℙ t) - (ε : EReal) : EReal)
      = (-(t * a - cgf (X 0) ℙ t) - (t * δ : EReal) : EReal) := by
        rw [← h_delta_eq]
        norm_cast
    _ ≤ LHS_val := h_bound_for_all_delta δ hδ_pos

-- ## Extras
-- The following are additional results that are not used in the current proof of the lower bound,
-- but could be applied towards a proof that does not depend on `h_clt_axiom`.

/-- For constant `C` and `δ > 0`, `n⁻¹ C / δ² → 0` as `n → ∞`. -/
private lemma variance_term_tendsto_zero (C : ℝ) (δ : ℝ) (_hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / n) * C / δ ^ 2)) atTop (𝓝 0) := by
  have h_eq : (fun n : ℕ => ENNReal.ofReal ((1 / n) * C / δ ^ 2)) =
              (fun n : ℕ => ENNReal.ofReal ((C / δ ^ 2) * (1 / n))) := by
    ext n
    ring_nf
  rw [h_eq]
  by_cases hC : C / δ ^ 2 ≤ 0
  · have : ∀ n : ℕ, ENNReal.ofReal ((C / δ ^ 2) * (1 / n)) = 0 := by
      intro n
      apply ENNReal.ofReal_of_nonpos
      exact mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
    simp only [this]
    exact tendsto_const_nhds
  · push Not at hC
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    convert (tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2)) using 1
    ext n
    ring

/-- If `f ≤ c` a.e. under `μ`, `f` is integrable, and `∫ f dμ = c`, then `f = c` a.e. under `μ` -/
private lemma ae_eq_const_of_integral_eq_const_of_le {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (c : ℝ)
    (hf : Integrable f μ) (h_le : ∀ᵐ ω ∂μ, f ω ≤ c) (h_int : μ[f] = c) :
    ∀ᵐ ω ∂μ, f ω = c := by
  have h_diff_nonneg : ∀ᵐ ω ∂μ, 0 ≤ c - f ω := by
    filter_upwards [h_le] with ω hω using sub_nonneg.mpr hω
  have h_integrable_diff : Integrable (fun ω => c - f ω) μ := by
    exact Integrable.sub (integrable_const c) hf
  have h_int_diff : μ[fun ω => c - f ω] = 0 := by
    calc μ[fun ω => c - f ω]
        = μ[fun _ => c] - μ[f] := integral_sub (integrable_const c) hf
      _ = c * (μ Set.univ).toReal - c := by simp [measure_univ, h_int]
      _ = c * 1 - c := by simp
      _ = 0 := by ring
  have h_diff_ae_zero : ∀ᵐ ω ∂μ, c - f ω = 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg h_integrable_diff).mp h_int_diff
    exact this
  filter_upwards [h_diff_ae_zero] with ω h
  linarith


include h_indep h_ident h_meas h_mgf in
/-- `Λ'_Sₙ(t) = n · Λ'_X(t)` -/
private lemma deriv_cgf_sum (t : ℝ) (n : ℕ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    deriv (cgf (partialSum X n) ℙ) t = n * deriv (cgf (X 0) ℙ) t := by
  have h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ :=
    interior_subset (s := integrableExpSet (X 0) ℙ) ht
  calc deriv (cgf (partialSum X n) ℙ) t
      = deriv (fun s => n * cgf (X 0) ℙ s) t := by
        have h_eq : cgf (partialSum X n) ℙ = (fun s => n * cgf (X 0) ℙ s) := by
          ext s
          exact cgf_sum_eq_n_prod_cgf X h_indep h_ident h_meas h_mgf n s
        rw [h_eq]
    _ = n * deriv (cgf (X 0) ℙ) t := by
        have h_diff : DifferentiableAt ℝ (cgf (X 0) ℙ) t := by
          have h_analytic := @analyticOn_cgf _ _ (X 0) ℙ t ht
          have h_nhds : interior (integrableExpSet (X 0) ℙ) ∈ 𝓝 t := isOpen_interior.mem_nhds ht
          have : insert t (interior (integrableExpSet (X 0) ℙ)) ∈ 𝓝 t := by
            simp only [Set.insert_eq_of_mem ht]
            exact h_nhds
          exact h_analytic.differentiableWithinAt.differentiableAt this
        exact deriv_const_mul (n : ℝ) h_diff

include h_indep h_ident h_meas h_mgf in
/-- `Λ''_Sₙ(t) = n · Λ''_X(t)` -/
private lemma iteratedDeriv_two_cgf_sum (t : ℝ) (n : ℕ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    iteratedDeriv 2 (cgf (partialSum X n) ℙ) t =
      n * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  have h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ :=
    interior_subset (s := integrableExpSet (X 0) ℙ) ht
  calc iteratedDeriv 2 (cgf (partialSum X n) ℙ) t
      = iteratedDeriv 2 (fun s => n * cgf (X 0) ℙ s) t := by
        have h_eq : cgf (partialSum X n) ℙ = (fun s => n * cgf (X 0) ℙ s) := by
          ext s
          exact cgf_sum_eq_n_prod_cgf X h_indep h_ident h_meas h_mgf n s
        rw [h_eq]
    _ = n * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
        exact iteratedDeriv_const_mul_field (n : ℝ) (cgf (X 0) ℙ)

include h_indep h_ident h_meas h_mgf in
/-- `𝔼_ℚₙₜ[Sₙ/n] = Λ'_Sₙ(t)` and `𝕍_ℚₙₜ[Sₙ/n] = Λ''_Sₙ(t)` -/
private lemma tilted_Sn_moments (t : ℝ) (n : ℕ) :
    let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
    μ_t[partialSum X n] = deriv (cgf (partialSum X n) ℙ) t ∧
    variance (partialSum X n) μ_t = iteratedDeriv 2 (cgf (partialSum X n) ℙ) t := by
  intro μ_t
  constructor
  · have ht_Sn : t ∈ interior (integrableExpSet (partialSum X n) ℙ) :=
      mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n
    exact integral_tilted_mul_self ht_Sn
  · have ht_Sn : t ∈ interior (integrableExpSet (partialSum X n) ℙ) :=
      mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n
    exact variance_tilted_mul ht_Sn

include h_indep h_ident h_meas h_mgf in
/-- `𝔼_ℚₙₜ[Sₙ/n] = Λ'(t)` and `𝕍_ℚₙₜ[Sₙ/n] = n⁻¹ Λ''(t)` -/
private lemma tilted_empirical_moments (t : ℝ) (n : ℕ) (hn : n ≠ 0)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
    μ_t[empiricalMean X n] = deriv (cgf (X 0) ℙ) t ∧
    variance (empiricalMean X n) μ_t = (1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  intro μ_t
  have h_Sn := @tilted_Sn_moments _ _ X h_indep h_ident h_meas h_mgf _ t n
  constructor
  · change μ_t[fun ω => partialSum X n ω / n] = deriv (cgf (X 0) ℙ) t
    rw [integral_div]
    rw [h_Sn.1]
    rw [@deriv_cgf_sum _ _ X h_indep h_ident h_meas h_mgf _ t n ht]
    field_simp
  · change variance (fun ω => partialSum X n ω / n) μ_t = (1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t
    conv_lhs =>
      arg 1; ext ω; rw [div_eq_inv_mul]
    rw [show (fun ω => ((n : ℝ))⁻¹ * partialSum X n ω) = ((n : ℝ))⁻¹ • (partialSum X n) by rfl]
    rw [variance_smul]
    rw [h_Sn.2]
    rw [@iteratedDeriv_two_cgf_sum _ _ X h_indep h_ident h_meas h_mgf _ t n ht]
    field_simp

include h_indep h_ident h_meas h_mgf in
/-- For `δ > 0`, given `Λ'(t) = a`, `ℚₙₜ(δ ≤ |Sₙ/n - a|) ≤ n⁻¹ Λ''(t) / δ²` -/
private lemma tilted_deviation_bound (t a : ℝ) (n : ℕ) (hn : n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ))
    (h_match : deriv (cgf (X 0) ℙ) t = a) :
    let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
    μ_t {ω | δ ≤ |empiricalMean X n ω - a|} ≤
      ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) := by
  intro μ_t
  have h_moments := @tilted_empirical_moments _ _ X h_indep h_ident h_meas h_mgf _ t n hn ht
  have h_mean : μ_t[empiricalMean X n] = a := by
    calc μ_t[empiricalMean X n]
        = μ_t[fun ω => partialSum X n ω / n] := by rfl
      _ = deriv (cgf (X 0) ℙ) t := h_moments.1
      _ = a := h_match
  have h_prob : IsProbabilityMeasure μ_t :=
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_memLp : MemLp (empiricalMean X n) 2 μ_t := by
    have ht_Sn : t ∈ interior (integrableExpSet (partialSum X n) ℙ) :=
      mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n
    have h_S_memLp : MemLp (partialSum X n) 2 μ_t := memLp_tilted_mul ht_Sn 2
    change MemLp (fun ω => partialSum X n ω / n) 2 μ_t
    have : (fun ω => partialSum X n ω / n) = (fun ω => (1 / (n : ℝ)) * partialSum X n ω) := by
      ext ω
      have hn_cast : (n : ℝ) ≠ 0 := by simp [hn]
      field_simp [hn_cast]
    rw [this]
    exact h_S_memLp.const_mul (1 / (n : ℝ))
  calc μ_t {ω | δ ≤ |empiricalMean X n ω - a|}
      = μ_t {ω | δ ≤ |empiricalMean X n ω - μ_t[empiricalMean X n]|} := by
        congr 1
        ext ω
        simp only [h_mean]
    _ ≤ ENNReal.ofReal (variance (empiricalMean X n) μ_t / δ ^ 2) :=
        meas_ge_le_variance_div_sq h_memLp hδ
    _ = ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) := by
        rw [h_moments.2]

include h_indep h_ident h_meas h_mgf in
/-- For `δ > 0`, given `Λ'(t) = a`, `ℚₙₜ(|Sₙ/n - a| < δ) → 1` as `n → ∞` -/
private lemma tilted_measure_concentrates (t a δ : ℝ) (hδ : 0 < δ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ))
    (h_match : deriv (cgf (X 0) ℙ) t = a) :
    Tendsto (fun n => ((ℚₙₜ X ℙ n t)
      {ω | |empiricalMean X n ω - a| < δ}).toReal) atTop (𝓝 1) := by
  haveI h_prob_n_all : ∀ n, IsProbabilityMeasure (ℚₙₜ X ℙ n t) := fun n =>
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_complement_to_zero : Tendsto (fun n => ((ℚₙₜ X ℙ n t)
      {ω | δ ≤ |empiricalMean X n ω - a|}).toReal) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_toReal_zero_iff]
    refine ENNReal.tendsto_nhds_zero.2 (fun ε hε => ?_)
    have h_var_to_zero : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2)) atTop (𝓝 0) := by
      convert variance_term_tendsto_zero (iteratedDeriv 2 (cgf (X 0) ℙ) t) δ hδ using 2
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 h_var_to_zero) ε hε
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn_ne : n ≠ 0 := by omega
    calc (ℚₙₜ X ℙ n t) {ω | δ ≤ |empiricalMean X n ω - a|}
        ≤ ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) :=
          tilted_deviation_bound (X := X) (h_indep := h_indep) (h_ident := h_ident)
            (h_meas := h_meas) (h_mgf := h_mgf) t a n hn_ne δ hδ ht h_match
      _ ≤ ε := hN n (by omega)
  have h_compl : ∀ n, {ω | |empiricalMean X n ω - a| < δ}ᶜ =
      {ω | δ ≤ |empiricalMean X n ω - a|} := by
    intro n
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have h_eq : ∀ n, (ℚₙₜ X ℙ n t)
      {ω | |empiricalMean X n ω - a| < δ} =
      1 - (ℚₙₜ X ℙ n t)
        {ω | δ ≤ |empiricalMean X n ω - a|} := by
    intro n
    have h_prob_n : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
      isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
    have h_meas' : MeasurableSet {ω | |empiricalMean X n ω - a| < δ} := by
      have h_emp_meas : Measurable (empiricalMean X n) :=
        measurable_empiricalMean X h_meas n
      have h_sub_meas : Measurable (fun ω => empiricalMean X n ω - a) :=
        h_emp_meas.sub_const a
      have h_abs_meas : Measurable (fun ω => |empiricalMean X n ω - a|) :=
        continuous_abs.measurable.comp h_sub_meas
      exact measurableSet_lt h_abs_meas measurable_const
    haveI := h_prob_n
    have h_prob_eq : (ℚₙₜ X ℙ n t)
        {ω | |empiricalMean X n ω - a| < δ}ᶜ =
        1 - (ℚₙₜ X ℙ n t)
          {ω | |empiricalMean X n ω - a| < δ} :=
      prob_compl_eq_one_sub h_meas'
    calc (ℚₙₜ X ℙ n t)
          {ω | |empiricalMean X n ω - a| < δ}
        = 1 - (1 - (ℚₙₜ X ℙ n t)
          {ω | |empiricalMean X n ω - a| < δ}) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
      _ = 1 - (ℚₙₜ X ℙ n t)
          {ω | |empiricalMean X n ω - a| < δ}ᶜ := by
          rw [← h_prob_eq]
      _ = 1 - (ℚₙₜ X ℙ n t)
          {ω | δ ≤ |empiricalMean X n ω - a|} := by
          rw [h_compl]
  simp_rw [h_eq]
  have h_one_sub : Tendsto (fun n => (1 - (ℚₙₜ X ℙ n t)
      {ω | δ ≤ |empiricalMean X n ω - a|}).toReal) atTop (𝓝 1) := by
    have h_measure_to_zero : Tendsto (fun n => (ℚₙₜ X ℙ n t)
        {ω | δ ≤ |empiricalMean X n ω - a|}) atTop (𝓝 0) := by
      rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)]
      exact h_complement_to_zero
    have h_sub_to_one : Tendsto (fun n => 1 - (ℚₙₜ X ℙ n t)
        {ω | δ ≤ |empiricalMean X n ω - a|}) atTop (𝓝 1) := by
      convert ENNReal.Tendsto.sub tendsto_const_nhds h_measure_to_zero
        (Or.inl ENNReal.one_ne_top) using 1
      simp
    rw [← ENNReal.toReal_one]
    refine (ENNReal.tendsto_toReal ?_).comp h_sub_to_one
    simp only [ne_eq, ENNReal.one_ne_top, not_false_eq_true]
  exact h_one_sub

include h_indep h_ident h_meas h_mgf in
/-- `ℚₙₜ(Sₙ/n ≥ a) > 0`.
This follows from the fact that the mean of `Sₙ/n` under `ℚₙₜ` is `a`, so there must be mass `≥a` -/
private lemma tilted_prob_ge_mean_pos (a t : ℝ)
    (ht_int : t ∈ interior (integrableExpSet (X 0) ℙ))
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) (n : ℕ) (hn : n ≠ 0) :
    0 < (ℚₙₜ X ℙ n t) {ω | a ≤ empiricalMean X n ω} := by
  let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
  have h_moments := @tilted_empirical_moments _ _ X h_indep h_ident h_meas h_mgf _ t n hn ht_int
  have h_mean : μ_t[empiricalMean X n] = a := by
    calc μ_t[empiricalMean X n]
        = μ_t[fun ω => partialSum X n ω / n] := by rfl
      _ = deriv (cgf (X 0) ℙ) t := h_moments.1
      _ = a := ht_deriv
  by_contra h_not_pos
  push Not at h_not_pos
  have h_ae_lt : ∀ᵐ ω ∂μ_t, empiricalMean X n ω < a := by
    have h_prob : IsProbabilityMeasure μ_t :=
      isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
    have h_zero : μ_t {ω | a ≤ empiricalMean X n ω} = 0 := le_antisymm h_not_pos (zero_le _)
    have h_meas_ge : MeasurableSet {ω | a ≤ empiricalMean X n ω} :=
      measurableSet_le measurable_const (measurable_empiricalMean X h_meas n)
    have : μ_t {ω | a ≤ empiricalMean X n ω}ᶜ = 1 := by
      calc μ_t {ω | a ≤ empiricalMean X n ω}ᶜ
          = 1 - μ_t {ω | a ≤ empiricalMean X n ω} := prob_compl_eq_one_sub h_meas_ge
        _ = 1 := by rw [h_zero]; norm_num
    rw [ae_iff]
    show μ_t {ω | ¬(empiricalMean X n ω < a)} = 0
    have : {ω | ¬(empiricalMean X n ω < a)} = {ω | a ≤ empiricalMean X n ω} := by
      ext ω; simp only [Set.mem_setOf_eq]; exact not_lt
    rw [this, h_zero]
  have h_prob : IsProbabilityMeasure μ_t :=
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_ae_le : ∀ᵐ ω ∂μ_t, empiricalMean X n ω ≤ a := by
    filter_upwards [h_ae_lt] with ω hω using le_of_lt hω
  have h_integrable_em : Integrable (empiricalMean X n) μ_t := by
    have ht_Sn : t ∈ interior (integrableExpSet (partialSum X n) ℙ) :=
      mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n
    have h_memLp : MemLp (partialSum X n) 1 μ_t := memLp_tilted_mul ht_Sn 1
    have h_int_S : Integrable (partialSum X n) μ_t := memLp_one_iff_integrable.mp h_memLp
    exact h_int_S.div_const (n : ℝ)
  have h_ae_eq : ∀ᵐ ω ∂μ_t, empiricalMean X n ω = a :=
    ae_eq_const_of_integral_eq_const_of_le μ_t a h_integrable_em h_ae_le h_mean
  have h_absurd : ∀ᵐ ω ∂μ_t, empiricalMean X n ω < a ∧ empiricalMean X n ω = a := by
    filter_upwards [h_ae_lt, h_ae_eq] with ω hlt heq using ⟨hlt, heq⟩
  have h_false_ae : ∀ᵐ ω ∂μ_t, False := by
    filter_upwards [h_absurd] with ω ⟨hlt, heq⟩
    linarith
  have : (ae μ_t).NeBot := IsProbabilityMeasure.ae_neBot
  rw [ae_iff] at h_false_ae
  simp only [not_false_eq_true, Set.setOf_true] at h_false_ae
  have : μ_t Set.univ = 1 := measure_univ
  rw [this] at h_false_ae
  norm_num at h_false_ae
