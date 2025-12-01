/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.Basic
public import Mathlib.Probability.LargeDeviations.Cramers.TiltedCLT

/-!
# Cramér's Theorem — Lower Bound

This file proves the lower (exponential tilting) bound for Cramér's theorem:

- `cramer_lower_bound`: For any `a ≥ 𝔼[X 0]`, `liminf n⁻¹ * log ℙ(Sₙ/n ≥ a) ≥ -I(a)`.

The proof uses the change-of-measure approach with the family of tilted measures
`ℚₙₜ = ℙ.tilted(t * Sₙ)` where `t` is chosen so that `cgf'(t) = a`.
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory

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

omit [MeasureSpace Ω] in
/-- `0 < t` and `Sₙ/n ∈ [a, a + δ]` implies `exp(-t · Sₙ) ≥ exp(-t · n · (a + δ))` -/
private lemma exp_neg_mul_S_ge_on_set (t : ℝ) (n : ℕ) (a δ : ℝ) (ht : 0 ≤ t)
    (ω : Ω) (hω : empiricalMean X n ω ∈ Set.Icc a (a + δ)) :
    Real.exp (-t * partialSum X n ω) ≥ Real.exp (-t * n * (a + δ)) := by
  apply Real.exp_le_exp.mpr
  rw [empiricalMean] at hω
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn, partialSum]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    nlinarith [(div_le_iff₀ hn').mp hω.2, mul_nonneg ht hn'.le]

/-- `0 ≤ (1 / n : EReal)` lifted from `ℝ` via `Nat.cast_nonneg`. -/
private lemma ereal_one_div_nat_nonneg (n : ℕ) : (0 : EReal) ≤ ((1 : ℝ) / n : EReal) :=
  EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg n))

/-- `(1 / ↑n) · ↑c → 0` where we lift to `EReal` from `ℝ`. -/
lemma ereal_inv_nat_mul_const_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * (c : EReal)) atTop (𝓝 0) := by
  have h_real : Tendsto (fun n : ℕ => (1 / n * c : ℝ)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      tendsto_natCast_atTop_atTop).mul (tendsto_const_nhds (x := c))
  exact_mod_cast continuous_coe_real_ereal.continuousAt.tendsto.comp h_real

/-- For `y ∈ (0, ∞)` and `n ≥ 1`, `n⁻¹ log(exp(x) · y) = n⁻¹x + n⁻¹ · log(y)`, where we lift
    values to EReal and ENNReal where needed for later results. -/
private lemma log_product_split (n : ℕ) (x : ℝ) (y : ENNReal) (hn : n ≥ 1)
    (hy_ne_zero : y ≠ 0) (hy_ne_top : y ≠ ⊤) :
    ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp x * y.toReal)) =
    ((1 : ℝ) / n : EReal) * (x : EReal) + ((1 : ℝ) / n : EReal) * ENNReal.log y := by
  have hy_pos : 0 < y.toReal := ENNReal.toReal_pos hy_ne_zero hy_ne_top
  rw [ENNReal.log_ofReal_of_pos (mul_pos (Real.exp_pos x) hy_pos),
    Real.log_mul (Real.exp_pos x).ne' hy_pos.ne', Real.log_exp,
    ENNReal.log_pos_real hy_ne_zero hy_ne_top, EReal.coe_add]
  exact EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (by positivity))
    (EReal.coe_ne_top _) _ _

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
  have h_eq : (1 / (n : ℝ)) * (-n * (t * (a + δ) - l)) = -(t * a - l) - t * δ := by
    field_simp; ring
  convert congrArg (fun x : ℝ => (x : EReal)) h_eq using 2

/-- Given `c ∈ [-∞,∞]` and `f(n) → 0` as `n → ∞`, `f(n) + c → c` as `n → ∞` -/
private lemma tendsto_const_add_vanishing (c : EReal) (f : ℕ → EReal)
    (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c + f n) atTop (𝓝 c) := by
  simpa using (EReal.continuousAt_add (by simp) (by simp)).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds h)

/-- Given `x, y ∈ [-∞, ∞]`, if `∀ε ∈ ℝ⁺, x - ε ≤ y`, then `x ≤ y`. -/
private lemma EReal.le_of_forall_pos_sub_le {x y : EReal}
    (h : ∀ ε : ℝ, 0 < ε → x - (ε : EReal) ≤ y) : x ≤ y := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top =>
    have := h 1 zero_lt_one
    rwa [EReal.top_sub_coe] at this
  | coe x_val =>
    induction y using EReal.rec with
    | bot =>
      have := h 1 zero_lt_one
      simp only [EReal.coe_one] at this
      exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)
    | top => exact le_top
    | coe y_val =>
      exact_mod_cast _root_.le_of_forall_sub_le fun ε hε => by exact_mod_cast h ε hε

/-! ### Lemmas requiring IsProbabilityMeasure -/

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- `ℚₙₜ(Sₙ/n ∈ [a, a+δ])` is eventually always positive as `n → ∞`.
That is, `∃ c > 0` s.t. `ℚₙₜ(Sₙ/n ∈ [a, a+δ]) > c` for all sufficiently large `n`.
This is a consequence of the Central Limit Theorem assumption. -/
private lemma tilted_window_lower_bound_from_concentration (a t δ : ℝ) (hδ : 0 < δ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    ∃ c > 0, ∀ᶠ n in atTop,
      c ≤ ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal := by
  refine ⟨1/4, by norm_num, ?_⟩
  filter_upwards [eventually_ℚₙₜ_empiricalMean_mem_Icc_ge X h_indep h_ident h_meas h_mgf
    h_non_deg t a δ hδ (1/4) (by norm_num) ht_deriv] with n hn
  linarith

/-- For an event `E ⊆ Ω` and a random variable `f : Ω → ℝ`, we have  `ℙ(E) = 𝔼[eᶠ] ∫_E exp(-f) dℙ_f`
where `ℙ_f` is the measure `ℙ` exponentially tilted with respect to `f`. That is, it has density
proportional to `exp(f)`. -/
private lemma measure_eq_integral_exp_neg_tilted (f : Ω → ℝ) (E : Set Ω)
    (h_int : Integrable (fun ω => Real.exp (f ω)) ℙ)
    (hE : MeasurableSet E) :
    (ℙ E).toReal =
      (𝔼[fun ω => Real.exp (f ω)]) * (∫ ω in E, Real.exp (-f ω) ∂(Measure.tilted ℙ f)) := by
  rw [setIntegral_tilted' f (fun ω => Real.exp (-f ω)) hE]
  have h_ne : 𝔼[fun x => Real.exp (f x)] ≠ 0 := (integral_exp_pos h_int).ne'
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_div,
    setIntegral_const, Measure.real, smul_eq_mul]
  field_simp

include h_indep h_ident h_meas h_mgf in
/-- `ℙ(Sₙ/n ∈ [a, a + δ]) ≥ exp(-n(ta - Λ(t))) · ℚₙₜ(Sₙ/n ∈ [a, a + δ])` -/
lemma change_of_measure_lower_bound (a δ t : ℝ) (n : ℕ) (ht : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * partialSum X n ω)) ℙ) :
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    (ℙ E).toReal ≥
      Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
      ((ℚₙₜ X ℙ n t) E).toReal := by
  intro E
  have hE : MeasurableSet E :=
    measurableSet_Icc.preimage (measurable_empiricalMean X h_meas n)
  rw [measure_eq_integral_exp_neg_tilted (fun ω => t * partialSum X n ω) E h_int hE]
  change mgf (partialSum X n) ℙ t * _ ≥ _
  rw [mgf_sum_eq_exp_n_prod_cgf X h_indep h_ident h_meas h_mgf n t]
  haveI : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_bound :
      ∫ ω in E, Real.exp (-t * partialSum X n ω)
        ∂(ℚₙₜ X ℙ n t) ≥
      Real.exp (-t * n * (a + δ)) *
        ((ℚₙₜ X ℙ n t) E).toReal := by
    calc ∫ ω in E, Real.exp (-t * partialSum X n ω)
        ∂(ℚₙₜ X ℙ n t)
        ≥ ∫ ω in E, Real.exp (-t * n * (a + δ))
          ∂(ℚₙₜ X ℙ n t) :=
          setIntegral_mono_on (integrable_const _).integrableOn
            (Integrable.integrableOn <| by
              rw [show (ℚₙₜ X ℙ n t) = Measure.tilted ℙ (fun ω => t * partialSum X n ω) from rfl,
                integrable_tilted_iff h_int]
              simp [← Real.exp_add])
            hE (exp_neg_mul_S_ge_on_set X t n a δ ht.le)
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
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  rw [← key]
  gcongr
  convert h_bound.le using 2
  ring_nf

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- The error term `n⁻¹ * log(ℚₙₜ(Sₙ/n ∈ [a, a+δ])) → 0` as `n → ∞` -/
private lemma error_term_vanishes (a t δ : ℝ) (hδ : 0 < δ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    Tendsto (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})) atTop (𝓝 0) := by
  obtain ⟨c, hc_pos, h_bounded⟩ :=
    tilted_window_lower_bound_from_concentration X h_indep h_ident h_meas h_mgf h_non_deg
      a t δ hδ ht_deriv
  haveI : ∀ m, IsProbabilityMeasure (ℚₙₜ X ℙ m t) := fun m =>
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t m
  have h_lower_tendsto : Tendsto (fun m : ℕ =>
      ((1 : ℝ) / m : EReal) * ENNReal.log (ENNReal.ofReal c)) atTop (𝓝 0) := by
    rw [ENNReal.log_ofReal_of_pos hc_pos]
    exact ereal_inv_nat_mul_const_tendsto_zero (Real.log c)
  have h_upper_tendsto : Tendsto (fun (_ : ℕ) => (0 : EReal)) atTop (𝓝 0) := tendsto_const_nhds
  have h_eventually : ∀ᶠ (m : ℕ) in atTop,
      ((1 : ℝ) / m : EReal) * ENNReal.log (ENNReal.ofReal c)
      ≤ ((1 : ℝ) / m : EReal) * ENNReal.log ((ℚₙₜ X ℙ m t)
          {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)})
      ∧ ((1 : ℝ) / m : EReal) * ENNReal.log ((ℚₙₜ X ℙ m t)
          {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)})
      ≤ 0 := by
    filter_upwards [h_bounded] with m hm_bound
    refine ⟨mul_le_mul_of_nonneg_left ?_ (ereal_one_div_nat_nonneg m),
      mul_nonpos_of_nonneg_of_nonpos (ereal_one_div_nat_nonneg m) ?_⟩
    · exact ENNReal.log_le_log <| (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
        hm_bound
    · exact ENNReal.log_le_zero_iff.mpr prob_le_one
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto
    (h_eventually.mono fun m h => h.1) (h_eventually.mono fun m h => h.2)

include h_indep h_ident h_meas h_mgf h_non_deg in
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
    haveI : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
      isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
    have h_subset : {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)} ⊆
        {ω | empiricalMean X n ω ≥ a} := fun _ hω => hω.1
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    let F := {ω | empiricalMean X n ω ≥ a}
    have h_prob_mono : (ℙ F).toReal ≥ (ℙ E).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_subset)
    have h_log_ineq : ENNReal.log (ℙ F) ≥
        ENNReal.log (ENNReal.ofReal (Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
          ((ℚₙₜ X ℙ n t) E).toReal)) := by
      apply ENNReal.log_le_log
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      linarith [h_prob_mono, change_of_measure_lower_bound X h_indep h_ident h_meas h_mgf
        a δ t n ht (integrable_exp_sum X h_indep h_ident h_meas h_mgf t n)]
    calc ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ F)
        ≥ ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal
            (Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
              ((ℚₙₜ X ℙ n t) E).toReal)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast h_log_ineq)
            (ereal_one_div_nat_nonneg n)
      _ = (-(t * a - cgf (X 0) ℙ t) - t * δ : EReal)
          + ((1 : ℝ) / n : EReal) *
            ENNReal.log ((ℚₙₜ X ℙ n t) E) := by
        by_cases h_tilted_zero : (ℚₙₜ X ℙ n t) E = 0
        · rw [h_tilted_zero]
          simp only [ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
          have h1n_pos : (0 : EReal) < ((1 : ℝ) / n : EReal) := EReal.coe_pos.mpr (by positivity)
          rw [EReal.mul_bot_of_pos h1n_pos]
          simp only [EReal.add_bot]
        · exact log_exp_product_eq_neg_coef_plus_log n t a δ (cgf (X 0) ℙ t) _ hn
            h_tilted_zero (measure_ne_top _ _)
  -- The error term `n⁻¹ log ℚₙₜ(Sₙ/n ∈ [a, a + δ])` vanishes as `n → ∞`.
  have h_error_vanish := @error_term_vanishes _ _ X h_indep h_ident h_meas h_mgf h_non_deg
    _ a t δ hδ ht_deriv
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
      ≥ rhs_seq n :=
    Filter.eventually_atTop.mpr ⟨1, h_pointwise⟩
  rw [← h_rhs_limit.liminf_eq]
  exact liminf_le_liminf h_eventually

include h_mgf h_non_deg in
/-- If `a ≥ 𝔼[X₁]` and `Λ'(t) = a`, then `0 ≤ t` -/
private lemma deriv_cgf_nonneg_of_ge_mean (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) (t : ℝ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    0 ≤ t := by
  by_contra! ht_neg
  have h_strict_mono : StrictMono (deriv (cgf (X 0) ℙ)) :=
    strictMono_of_deriv_pos fun x => by simpa [iteratedDeriv_succ] using h_non_deg x
  have := h_strict_mono ht_neg
  rw [ht_deriv, deriv_cgf_zero (mem_interior_integrableExpSet X h_mgf 0)] at this
  simp at this
  linarith

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
include h_mgf in
/-- The CGF of `X 0` is analytic on all of `ℝ`. -/
private lemma analyticOn_cgf_univ : AnalyticOn ℝ (cgf (X 0) ℙ) Set.univ :=
  Set.eq_univ_of_forall (mem_interior_integrableExpSet X h_mgf) ▸ analyticOn_cgf

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
include h_mgf h_bdd h_non_deg in
/-- Given `Λ'(t) = a`, the rate function satisfies `I(a) = ta - Λ(t)`. -/
private lemma rateFunction_eq_of_deriv_eq (a t : ℝ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    I X a = t * a - cgf (X 0) ℙ t := by
  rw [I]
  have h_analytic : AnalyticOn ℝ (cgf (X 0) ℙ) Set.univ := analyticOn_cgf_univ X h_mgf
  -- We proceed by proving inequality in both directions
  refine le_antisymm (ciSup_le fun s => ?_) (le_ciSup (h_bdd a) t)
  -- Sub-goal `sa - Λ(s) ≤ ta - Λ(t)`, i.e. `Λ(s) ≥ Λ(t) + a(s - t)`: the CGF is above its
  -- tangent line at `t`, as it is strictly convex (from `h_non_deg`: `Λ''(x) > 0`).
  have h_convex : StrictConvexOn ℝ Set.univ (cgf (X 0) ℙ) :=
    strictConvexOn_of_deriv2_pos' convex_univ h_analytic.continuousOn
      fun x _ => by simpa [← iteratedDeriv_eq_iterate] using h_non_deg x
  have h_diff : DifferentiableAt ℝ (cgf (X 0) ℙ) t :=
    h_analytic.differentiableOn.differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ t))
  suffices h_tangent : cgf (X 0) ℙ s ≥ cgf (X 0) ℙ t + a * (s - t) by linarith
  rcases lt_trichotomy s t with hst | rfl | hts
  · have h_slope := h_convex.convexOn.slope_le_of_hasDerivAt
      (Set.mem_univ s) (Set.mem_univ t) hst h_diff.hasDerivAt
    rw [ht_deriv, slope_def_field] at h_slope
    rw [ge_iff_le, ← sub_nonneg]
    have : 0 < t - s := sub_pos.mpr hst
    nlinarith [(div_le_iff₀ this).mp h_slope]
  · simp
  · have h_slope := h_convex.convexOn.deriv_le_slope
      (Set.mem_univ t) (Set.mem_univ s) hts h_diff
    rw [ht_deriv, slope_def_field] at h_slope
    rw [ge_iff_le, ← sub_nonneg]
    have : 0 < s - t := sub_pos.mpr hts
    nlinarith [(le_div_iff₀ this).mp h_slope]

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- Edge-case of `cramer_lower_bound` at `a = 𝔼[X 0]` -/
private lemma cramer_lower_bound_at_mean (a : ℝ) (ht_deriv : deriv (cgf (X 0) ℙ) 0 = a) :
    (0 : EReal) ≤
      liminf (fun n : ℕ =>
        ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop := by
  -- `Var[X] > 0`
  have h_var_pos : 0 < variance (X 0) ℙ := by
    have h_int_zero : (0 : ℝ) ∈ interior (integrableExpSet (X 0) ℙ) :=
      mem_interior_integrableExpSet X h_mgf 0
    have h := variance_tilted_mul (X := X 0) (μ := ℙ) h_int_zero
    simp only [zero_mul, show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, tilted_zero] at h
    exact h ▸ h_non_deg 0
  -- `∃ c > 0` such that for all sufficiently large `n`, `ℙ(Sₙ/n ≥ a) ≥ c`
  -- i.e. the asymptotic lower bound `ℙ(Sₙ/n ≥ a)` is greater than 0, which we derive from CLT
  -- on the tilted measures, noting that at `t = 0`, the tilted measures `ℚₙₜ` coincide with `ℙ`.
  have h_prob_lower_bound : ∃ c > 0, ∀ᶠ n in atTop,
      c ≤ (ℙ {ω | a ≤ empiricalMean X n ω}).toReal := by
    have h_bound := eventually_ℚₙₜ_empiricalMean_mem_Icc_ge X h_indep h_ident h_meas h_mgf
      h_non_deg 0 a 1 (by norm_num) (1/4) (by norm_num) ht_deriv
    refine ⟨1/4, by norm_num, ?_⟩
    filter_upwards [h_bound] with n hn
    have h_eq_meas : ℚₙₜ X ℙ n 0 = ℙ := by
      change Measure.tilted ℙ (fun ω => 0 * partialSum X n ω) = ℙ
      simp_rw [zero_mul]; exact tilted_zero ℙ
    rw [h_eq_meas] at hn
    calc (1 / 4 : ℝ)
        = 1 / 2 - 1 / 4 := by norm_num
      _ ≤ (ℙ {ω | empiricalMean X n ω ∈ Set.Icc a (a + 1)}).toReal := hn
      _ ≤ (ℙ {ω | a ≤ empiricalMean X n ω}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun _ hω => hω.1)
  obtain ⟨c, hc_pos, h_eventually_lower⟩ := h_prob_lower_bound
  have h_lower_tendsto :
      Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal c))
        atTop (𝓝 0) := by
    rw [ENNReal.log_ofReal_of_pos hc_pos]
    exact ereal_inv_nat_mul_const_tendsto_zero (Real.log c)
  have h_upper_tendsto : Tendsto (fun (_ : ℕ) => (0 : EReal)) atTop (𝓝 0) := tendsto_const_nhds
  -- Establish bounds to apply squeeze theorem `n⁻¹ log (c) ≤ n⁻¹ log ℙ(Sₙ/n ≥ a) ≤ 0`
  have h_squeeze : ∀ᶠ (m : ℕ) in atTop,
      ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal c)
      ≤ ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X m ω})
      ∧ ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X m ω}) ≤ 0 := by
    filter_upwards [h_eventually_lower] with m hm_lower
    refine ⟨mul_le_mul_of_nonneg_left ?_ (ereal_one_div_nat_nonneg m),
      mul_nonpos_of_nonneg_of_nonpos (ereal_one_div_nat_nonneg m) ?_⟩
    · exact ENNReal.log_le_log <|
        (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hm_lower
    · exact ENNReal.log_le_zero_iff.mpr prob_le_one
  -- `n⁻¹ log ℙ(Sₙ/n ≥ a) → 0` by squeeze theorem
  have h_tendsto :
      Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X n ω}))
        atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto
      (h_squeeze.mono fun _ hn => hn.1) (h_squeeze.mono fun _ hn => hn.2)
  change (0 : EReal) ≤
    liminf (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | a ≤ empiricalMean X n ω}))
      atTop
  rw [h_tendsto.liminf_eq]

include h_indep h_ident h_meas h_mgf h_bdd h_non_deg h_exposed in
/-- **Cramér's Theorem (Lower Bound)**: Given `a ≥ E[X 0]`, `-I(a) ≤ liminfₙ n⁻¹ log ℙ(Sₙ/n ≥ a)` -/
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
  · -- `t = 0` (which implies `a = 𝔼[X]` from solving `a = Λ'(t) = Λ'(0)`).
    subst ht_zero
    simp only [zero_mul, cgf_zero, sub_zero, EReal.coe_zero, neg_zero]
    exact cramer_lower_bound_at_mean X h_indep h_ident h_meas h_mgf h_non_deg a ht_deriv
  have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)
  -- Bound the liminf from below for any fixed positive `δ` using the tilted measure bounds.
  have h_bound_for_all_delta : ∀ (δ : ℝ), 0 < δ →
      (-(t * a - cgf (X 0) ℙ t) - t * δ : EReal) ≤ LHS_val := fun δ hδ =>
    (lower_bound_via_tilted X h_indep h_ident h_meas h_mgf h_non_deg a t δ hδ ht_pos ht_deriv).le
  -- Conclude the lower bound by taking `δ → 0`.
  refine EReal.le_of_forall_pos_sub_le fun ε hε => ?_
  have h := h_bound_for_all_delta (ε / t) (div_pos hε ht_pos)
  rwa [show ((t : EReal) * (ε / t : ℝ) : EReal) = ((ε : ℝ) : EReal) from by
    rw [← EReal.coe_mul]; norm_cast; field_simp] at h

/-! ### Extras: Chebyshev-based concentration of the tilted measure

The following results are not used by the current lower-bound proof. They establish additional
elementary results on the concentration by Chebyshev's inequality, instead of the CLT on
tilted measures approach used by the actual result. -/

/-- For constant `C` and `δ > 0`, `n⁻¹ C / δ² → 0` as `n → ∞`. -/
private lemma variance_term_tendsto_zero (C : ℝ) (δ : ℝ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / n) * C / δ ^ 2)) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
  convert tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2) using 1
  ext n
  ring

/-- If `f ≤ c` a.e. under `μ`, `f` is integrable, and `∫ f dμ = c`, then `f = c` a.e. under `μ` -/
private lemma ae_eq_const_of_integral_eq_const_of_le {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (c : ℝ)
    (hf : Integrable f μ) (h_le : ∀ᵐ ω ∂μ, f ω ≤ c) (h_int : μ[f] = c) :
    ∀ᵐ ω ∂μ, f ω = c := by
  have h_diff_nonneg : ∀ᵐ ω ∂μ, 0 ≤ c - f ω := by
    filter_upwards [h_le] with ω hω using sub_nonneg.mpr hω
  have h_int_diff : μ[fun ω => c - f ω] = 0 := by
    rw [integral_sub (integrable_const c) hf]; simp [h_int]
  have h_diff_ae_zero : ∀ᵐ ω ∂μ, c - f ω = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg ((integrable_const c).sub hf)).mp h_int_diff
  filter_upwards [h_diff_ae_zero] with ω h using by linarith

include h_indep h_ident h_meas h_mgf in
/-- `Λ_Sₙ = fun t => n · Λ_X(t)` -/
private lemma cgf_partialSum_eq_smul_cgf (n : ℕ) :
    cgf (partialSum X n) ℙ = fun s => n * cgf (X 0) ℙ s :=
  funext <| cgf_sum_eq_n_prod_cgf X h_indep h_ident h_meas h_mgf n

include h_indep h_ident h_meas h_mgf in
/-- `Λ'_Sₙ(t) = n · Λ'_X(t)` -/
private lemma deriv_cgf_sum (t : ℝ) (n : ℕ) :
    deriv (cgf (partialSum X n) ℙ) t = n * deriv (cgf (X 0) ℙ) t := by
  rw [cgf_partialSum_eq_smul_cgf X h_indep h_ident h_meas h_mgf n]
  exact deriv_const_mul (n : ℝ) ((analyticOn_cgf_univ X h_mgf).differentiableOn.differentiableAt
    (isOpen_univ.mem_nhds (Set.mem_univ t)))

include h_indep h_ident h_meas h_mgf in
/-- `Λ''_Sₙ(t) = n · Λ''_X(t)` -/
private lemma iteratedDeriv_two_cgf_sum (t : ℝ) (n : ℕ) :
    iteratedDeriv 2 (cgf (partialSum X n) ℙ) t =
      n * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  rw [cgf_partialSum_eq_smul_cgf X h_indep h_ident h_meas h_mgf n]
  exact iteratedDeriv_const_mul_field (n : ℝ) (cgf (X 0) ℙ)

include h_indep h_ident h_meas h_mgf in
/-- `𝔼_ℚₙₜ[Sₙ/n] = Λ'_Sₙ(t)` and `𝕍_ℚₙₜ[Sₙ/n] = Λ''_Sₙ(t)` -/
private lemma tilted_Sn_moments (t : ℝ) (n : ℕ) :
    let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
    μ_t[partialSum X n] = deriv (cgf (partialSum X n) ℙ) t ∧
    variance (partialSum X n) μ_t = iteratedDeriv 2 (cgf (partialSum X n) ℙ) t := by
  have ht_Sn : t ∈ interior (integrableExpSet (partialSum X n) ℙ) :=
    mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n
  exact ⟨integral_tilted_mul_self ht_Sn, variance_tilted_mul ht_Sn⟩

include h_indep h_ident h_meas h_mgf in
/-- `𝔼_ℚₙₜ[Sₙ/n] = Λ'(t)` and `𝕍_ℚₙₜ[Sₙ/n] = n⁻¹ Λ''(t)` -/
private lemma tilted_empirical_moments (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
    μ_t[empiricalMean X n] = deriv (cgf (X 0) ℙ) t ∧
    variance (empiricalMean X n) μ_t = (1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  intro μ_t
  have h_Sn := @tilted_Sn_moments _ _ X h_indep h_ident h_meas h_mgf _ t n
  refine ⟨?_, ?_⟩
  · change μ_t[fun ω => partialSum X n ω / n] = deriv (cgf (X 0) ℙ) t
    rw [integral_div, h_Sn.1, @deriv_cgf_sum _ _ X h_indep h_ident h_meas h_mgf _ t n]
    field_simp
  · change variance (fun ω => partialSum X n ω / n) μ_t = (1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t
    simp_rw [div_eq_inv_mul]
    rw [show (fun ω => ((n : ℝ))⁻¹ * partialSum X n ω) = ((n : ℝ))⁻¹ • (partialSum X n) from rfl,
      variance_smul, h_Sn.2, @iteratedDeriv_two_cgf_sum _ _ X h_indep h_ident h_meas h_mgf _ t n]
    field_simp

include h_indep h_ident h_meas h_mgf in
/-- Given `Λ'(t) = a`, `𝔼_{ℚₙₜ}[Sₙ/n] = a` -/
private lemma tilted_empirical_mean_eq_of_deriv (t a : ℝ) (n : ℕ) (hn : n ≠ 0)
    (h_deriv : deriv (cgf (X 0) ℙ) t = a) :
    (Measure.tilted ℙ (fun ω => t * partialSum X n ω))[empiricalMean X n] = a :=
  (tilted_empirical_moments X h_indep h_ident h_meas h_mgf t n hn).1.trans h_deriv

include h_indep h_ident h_meas h_mgf in
/-- For `δ > 0`, given `Λ'(t) = a`, `ℚₙₜ(δ ≤ |Sₙ/n - a|) ≤ n⁻¹ Λ''(t) / δ²` -/
private lemma tilted_deviation_bound (t a : ℝ) (n : ℕ) (hn : n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (h_match : deriv (cgf (X 0) ℙ) t = a) :
    let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
    μ_t {ω | δ ≤ |empiricalMean X n ω - a|} ≤
      ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) := by
  intro μ_t
  have h_mean : μ_t[empiricalMean X n] = a :=
    tilted_empirical_mean_eq_of_deriv X h_indep h_ident h_meas h_mgf t a n hn h_match
  haveI : IsProbabilityMeasure μ_t :=
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_memLp : MemLp (empiricalMean X n) 2 μ_t := by
    have ht_Sn : t ∈ interior (integrableExpSet (partialSum X n) ℙ) :=
      mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n
    have : (empiricalMean X n) = fun ω => (n : ℝ)⁻¹ * partialSum X n ω := by
      ext ω; simp [empiricalMean, div_eq_inv_mul]
    rw [this]
    exact (memLp_tilted_mul ht_Sn 2 : MemLp (partialSum X n) 2 μ_t).const_mul _
  calc μ_t {ω | δ ≤ |empiricalMean X n ω - a|}
      = μ_t {ω | δ ≤ |empiricalMean X n ω - μ_t[empiricalMean X n]|} := by
        simp_rw [h_mean]
    _ ≤ ENNReal.ofReal (variance (empiricalMean X n) μ_t / δ ^ 2) :=
        meas_ge_le_variance_div_sq h_memLp hδ
    _ = ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) := by
        rw [(tilted_empirical_moments X h_indep h_ident h_meas h_mgf t n hn).2]

include h_indep h_ident h_meas h_mgf in
/-- For `δ > 0`, given `Λ'(t) = a`, `ℚₙₜ(|Sₙ/n - a| < δ) → 1` as `n → ∞` -/
private lemma tilted_measure_concentrates (t a δ : ℝ) (hδ : 0 < δ)
    (h_match : deriv (cgf (X 0) ℙ) t = a) :
    Tendsto (fun n => ((ℚₙₜ X ℙ n t)
      {ω | |empiricalMean X n ω - a| < δ}).toReal) atTop (𝓝 1) := by
  haveI h_prob_n_all : ∀ n, IsProbabilityMeasure (ℚₙₜ X ℙ n t) := fun n =>
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_complement_to_zero : Tendsto (fun n => ((ℚₙₜ X ℙ n t)
      {ω | δ ≤ |empiricalMean X n ω - a|}).toReal) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_toReal_zero_iff]
    refine ENNReal.tendsto_nhds_zero.2 (fun ε hε => ?_)
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1
      (variance_term_tendsto_zero (iteratedDeriv 2 (cgf (X 0) ℙ) t) δ)) ε hε
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    calc (ℚₙₜ X ℙ n t) {ω | δ ≤ |empiricalMean X n ω - a|}
        ≤ ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) :=
          tilted_deviation_bound (X := X) (h_indep := h_indep) (h_ident := h_ident)
            (h_meas := h_meas) (h_mgf := h_mgf) t a n (by omega) δ hδ h_match
      _ ≤ ε := hN n (by omega)
  have h_compl : ∀ n, {ω | |empiricalMean X n ω - a| < δ}ᶜ =
      {ω | δ ≤ |empiricalMean X n ω - a|} := fun _ => by
    ext; simp [not_lt]
  have h_eq : ∀ n, (ℚₙₜ X ℙ n t)
      {ω | |empiricalMean X n ω - a| < δ} =
      1 - (ℚₙₜ X ℙ n t)
        {ω | δ ≤ |empiricalMean X n ω - a|} := fun n => by
    have h_meas' : MeasurableSet {ω | |empiricalMean X n ω - a| < δ} :=
      measurableSet_lt ((measurable_empiricalMean X h_meas n).sub_const a).abs measurable_const
    rw [← h_compl n, prob_compl_eq_one_sub h_meas',
      ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  simp_rw [h_eq]
  have h_measure_to_zero : Tendsto (fun n => (ℚₙₜ X ℙ n t)
      {ω | δ ≤ |empiricalMean X n ω - a|}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)).mp h_complement_to_zero
  have h_sub_to_one : Tendsto (fun n => 1 - (ℚₙₜ X ℙ n t)
      {ω | δ ≤ |empiricalMean X n ω - a|}) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h_measure_to_zero
      (Or.inl ENNReal.one_ne_top)
  rw [← ENNReal.toReal_one]
  exact (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h_sub_to_one

include h_indep h_ident h_meas h_mgf in
/-- `ℚₙₜ(Sₙ/n ≥ a) > 0`.
This follows from the fact that the mean of `Sₙ/n` under `ℚₙₜ` is `a`, so there must be mass `≥a` -/
private lemma tilted_prob_ge_mean_pos (a t : ℝ)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) (n : ℕ) (hn : n ≠ 0) :
    0 < (ℚₙₜ X ℙ n t) {ω | a ≤ empiricalMean X n ω} := by
  let μ_t := Measure.tilted ℙ (fun ω => t * partialSum X n ω)
  haveI h_prob : IsProbabilityMeasure μ_t :=
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have h_mean : μ_t[empiricalMean X n] = a :=
    tilted_empirical_mean_eq_of_deriv X h_indep h_ident h_meas h_mgf t a n hn ht_deriv
  by_contra! h_not_pos
  have h_zero : μ_t {ω | a ≤ empiricalMean X n ω} = 0 := le_antisymm h_not_pos (zero_le _)
  have h_ae_lt : ∀ᵐ ω ∂μ_t, empiricalMean X n ω < a := by
    rw [ae_iff, show {ω | ¬(empiricalMean X n ω < a)} = {ω | a ≤ empiricalMean X n ω} from
      Set.ext fun _ => not_lt, h_zero]
  have h_integrable_em : Integrable (empiricalMean X n) μ_t :=
    (memLp_one_iff_integrable.mp (memLp_tilted_mul
      (mem_interior_integrableExpSet_partialSum X h_indep h_ident h_meas h_mgf t n) 1)).div_const n
  have h_ae_eq : ∀ᵐ ω ∂μ_t, empiricalMean X n ω = a :=
    ae_eq_const_of_integral_eq_const_of_le μ_t a h_integrable_em
      (h_ae_lt.mono fun _ => le_of_lt) h_mean
  exact (h_ae_lt.and h_ae_eq).exists.elim fun _ ⟨hlt, heq⟩ => (heq ▸ hlt).ne rfl

end ProbabilityTheory
