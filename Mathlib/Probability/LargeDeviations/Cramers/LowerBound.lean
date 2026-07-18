/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.Basic
public import Mathlib.Probability.LargeDeviations.Cramers.TiltedCLT
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Cramér's Theorem — Lower Bound

This file proves the lower (exponential tilting) bound for Cramér's theorem:

- `Cramer.neg_rateFunction_le_liminf`: For any `a` with `μ[X 0] ≤ a`,
  `-rateFunction X μ a ≤ liminf n⁻¹ * log μ(a ≤ Sₙ/n)`.

The proof uses the change-of-measure approach with the family of tilted measures
`tiltedMeasure = μ.tilted(t * Sₙ)` where `t` is chosen so that `cgf'(t) = a`.
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

/-- `0 ≤ t` and `Sₙ/n ∈ [a, a + δ]` implies `exp(-t · n · (a + δ)) ≤ exp(-t · Sₙ)` -/
private lemma exp_le_exp_neg_mul_partialSum (t : ℝ) (n : ℕ) (a δ : ℝ) (ht : 0 ≤ t)
    (ω : Ω) (hω : empiricalMean X n ω ∈ Set.Icc a (a + δ)) :
    Real.exp (-t * n * (a + δ)) ≤ Real.exp (-t * partialSum X n ω) := by
  apply Real.exp_le_exp.mpr
  rw [empiricalMean] at hω
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn, partialSum]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    nlinarith [(div_le_iff₀ hn').mp hω.2, mul_nonneg ht hn'.le]

/-- `0 ≤ (1 / n : EReal)` lifted from `ℝ` via `Nat.cast_nonneg`. -/
private lemma ereal_one_div_nat_nonneg (n : ℕ) : (0 : EReal) ≤ ((1 : ℝ) / n : EReal) :=
  EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg n))

/-- For `y ∈ (0, ∞)` and `1 ≤ n`, `n⁻¹ log(exp(x) · y) = n⁻¹x + n⁻¹ · log(y)`,
    where we lift values to EReal and ENNReal where needed for later results. -/
private lemma log_product_split (n : ℕ) (x : ℝ) (y : ENNReal) (hn : 1 ≤ n)
    (hy_ne_zero : y ≠ 0) (hy_ne_top : y ≠ ⊤) :
    ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp x * y.toReal)) =
    ((1 : ℝ) / n : EReal) * (x : EReal) + ((1 : ℝ) / n : EReal) * ENNReal.log y := by
  have hy_pos : 0 < y.toReal := ENNReal.toReal_pos hy_ne_zero hy_ne_top
  rw [ENNReal.log_ofReal_of_pos (mul_pos (Real.exp_pos x) hy_pos),
    Real.log_mul (Real.exp_pos x).ne' hy_pos.ne', Real.log_exp,
    ENNReal.log_pos_real hy_ne_zero hy_ne_top, EReal.coe_add]
  exact EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (by positivity))
    (EReal.coe_ne_top _) _ _

/-- For `y ∈ (0, ∞)` and `1 ≤ n`,
  `n⁻¹ log(exp(-n (t · (a + δ) - l)) · y) = -(ta - l) - tδ + n⁻¹ log(y)`
  which we will later use with `l := Λ(t)` -/
private lemma log_exp_product_eq_neg_coef_plus_log (n : ℕ) (t a δ : ℝ) (l : ℝ)
    (y : ENNReal) (hn : 1 ≤ n) (hy_ne_zero : y ≠ 0) (hy_ne_top : y ≠ ⊤) :
    ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal
      (Real.exp (-n * (t * (a + δ) - l)) * y.toReal)) =
    (-(t * a - l) - t * δ : EReal) + ((1 : ℝ) / n : EReal) * ENNReal.log y := by
  rw [log_product_split n _ y hn hy_ne_zero hy_ne_top]
  congr 1
  have h_eq : (1 / (n : ℝ)) * (-n * (t * (a + δ) - l)) = -(t * a - l) - t * δ := by
    field_simp; ring
  rw [show ((1 : ℝ) / n : EReal) = ((1 / n : ℝ) : EReal) by norm_cast,
    ← EReal.coe_mul, h_eq]
  norm_cast

/-- Given `c ∈ [-∞,∞]` and `f(n) → 0` as `n → ∞`, `f(n) + c → c` as `n → ∞` -/
private lemma tendsto_const_add_vanishing (c : EReal) (f : ℕ → EReal)
    (h : Tendsto f atTop (𝓝 0)) : Tendsto (fun n => c + f n) atTop (𝓝 c) := by
  simpa [Function.comp_def] using (EReal.continuousAt_add (by simp) (by simp)).tendsto.comp
    (tendsto_const_nhds.prodMk_nhds h)

/-! ### Lemmas requiring IsProbabilityMeasure -/

variable [IsProbabilityMeasure μ]

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- `tiltedMeasure(Sₙ/n ∈ [a, a+δ])` is eventually always positive as `n → ∞`.
That is, `∃ c > 0` s.t. `c ≤ tiltedMeasure(Sₙ/n ∈ [a, a+δ])` for all sufficiently large `n`.
This is a consequence of the Central Limit Theorem assumption. -/
private lemma Cramer.tilted_window_lower_bound_from_concentration (a t δ : ℝ) (hδ : 0 < δ)
    (ht_deriv : deriv (cgf (X 0) μ) t = a) :
    ∃ c > 0, ∀ᶠ n in atTop,
      c ≤ ((tiltedMeasure X μ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal := by
  refine ⟨1/4, by norm_num, ?_⟩
  filter_upwards [eventually_tiltedMeasure_empiricalMean_mem_Icc_ge X h_indep h_ident h_meas h_mgf
    h_non_deg t a δ hδ (1/4) (by norm_num) ht_deriv] with n hn
  linarith

/-- For an event `E ⊆ Ω` and a random variable `f : Ω → ℝ`, we have
`μ(E) = μ[eᶠ] ∫_E exp(-f) dμ_f`
where `μ_f` is the measure `μ` exponentially tilted with respect to `f`. That is, it has density
proportional to `exp(f)`. -/
private lemma measure_eq_integral_exp_neg_tilted (f : Ω → ℝ) (E : Set Ω)
    (h_int : Integrable (fun ω => Real.exp (f ω)) μ)
    (hE : MeasurableSet E) :
    (μ E).toReal =
      (μ[fun ω => Real.exp (f ω)]) *
        (∫ ω in E, Real.exp (-f ω) ∂(Measure.tilted μ f)) := by
  rw [setIntegral_tilted' f (fun ω => Real.exp (-f ω)) hE]
  have h_ne : μ[fun x => Real.exp (f x)] ≠ 0 := (integral_exp_pos h_int).ne'
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_div, setIntegral_const, Measure.real, smul_eq_mul]
  field_simp

include h_indep h_ident h_meas h_mgf in
/-- `exp(-n(ta - Λ(t))) · tiltedMeasure(Sₙ/n ∈ [a, a + δ]) ≤
μ(Sₙ/n ∈ [a, a + δ])` -/
lemma Cramer.change_of_measure_lower_bound (a δ t : ℝ) (n : ℕ) (ht : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * partialSum X n ω)) μ) :
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    Real.exp (-n * (t * (a + δ) - cgf (X 0) μ t)) *
      ((tiltedMeasure X μ n t) E).toReal ≤ (μ E).toReal := by
  intro E
  have hE : MeasurableSet E :=
    measurableSet_Icc.preimage (measurable_empiricalMean X h_meas n)
  rw [measure_eq_integral_exp_neg_tilted (fun ω => t * partialSum X n ω) E h_int hE]
  change _ ≤ mgf (partialSum X n) μ t * _
  rw [mgf_partialSum X h_indep h_ident h_meas h_mgf n t]
  haveI : IsProbabilityMeasure (tiltedMeasure X μ n t) :=
    isProbabilityMeasure_tiltedMeasure X h_indep h_ident h_meas h_mgf t n
  have h_bound :
      Real.exp (-t * n * (a + δ)) *
        ((tiltedMeasure X μ n t) E).toReal ≤
      ∫ ω in E, Real.exp (-t * partialSum X n ω)
        ∂(tiltedMeasure X μ n t) := by
    calc Real.exp (-t * n * (a + δ)) *
            ((tiltedMeasure X μ n t) E).toReal
        = ((tiltedMeasure X μ n t).real E) •
            Real.exp (-t * n * (a + δ)) := by
          rw [Measure.real, smul_eq_mul]; ring
      _ = ∫ ω in E, Real.exp (-t * n * (a + δ))
          ∂(tiltedMeasure X μ n t) := (setIntegral_const _).symm
      _ ≤ ∫ ω in E, Real.exp (-t * partialSum X n ω)
          ∂(tiltedMeasure X μ n t) :=
          setIntegral_mono_on (integrable_const _).integrableOn
            (Integrable.integrableOn <| by
              rw [show (tiltedMeasure X μ n t) =
                  Measure.tilted μ (fun ω => t * partialSum X n ω) from rfl,
                integrable_tilted_iff h_int]
              simp [← Real.exp_add])
            hE (exp_le_exp_neg_mul_partialSum X t n a δ ht.le)
  have key : Real.exp (n * cgf (X 0) μ t) *
      (Real.exp (-t * n * (a + δ)) *
        ((tiltedMeasure X μ n t) E).toReal) =
    Real.exp (-n * (t * (a + δ) - cgf (X 0) μ t)) *
      ((tiltedMeasure X μ n t) E).toReal := by
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  rw [← key]
  gcongr
  simpa [tiltedMeasure, neg_mul] using h_bound

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- The error term `n⁻¹ * log(tiltedMeasure(Sₙ/n ∈ [a, a+δ])) → 0` as `n → ∞` -/
private lemma Cramer.error_term_vanishes (a t δ : ℝ) (hδ : 0 < δ)
    (ht_deriv : deriv (cgf (X 0) μ) t = a) :
    Tendsto (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log ((tiltedMeasure X μ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})) atTop (𝓝 0) := by
  obtain ⟨c, hc_pos, h_bounded⟩ :=
    tilted_window_lower_bound_from_concentration X h_indep h_ident h_meas h_mgf h_non_deg
      a t δ hδ ht_deriv
  haveI : ∀ m, IsProbabilityMeasure (tiltedMeasure X μ m t) := fun m =>
    isProbabilityMeasure_tiltedMeasure X h_indep h_ident h_meas h_mgf t m
  have h_lower_tendsto : Tendsto (fun m : ℕ =>
      ((1 : ℝ) / m : EReal) * ENNReal.log (ENNReal.ofReal c)) atTop (𝓝 0) := by
    rw [ENNReal.log_ofReal_of_pos hc_pos]
    refine (EReal.tendsto_const_div_atTop_nhds_zero_nat (C := (Real.log c : EReal))
      (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).congr fun n => ?_
    rw [EReal.div_eq_inv_mul, div_eq_mul_inv, EReal.coe_one, one_mul]
  have h_upper_tendsto : Tendsto (fun (_ : ℕ) => (0 : EReal)) atTop (𝓝 0) := tendsto_const_nhds
  have h_eventually : ∀ᶠ (m : ℕ) in atTop,
      ((1 : ℝ) / m : EReal) * ENNReal.log (ENNReal.ofReal c)
      ≤ ((1 : ℝ) / m : EReal) * ENNReal.log ((tiltedMeasure X μ m t)
          {ω | empiricalMean X m ω ∈ Set.Icc a (a + δ)})
      ∧ ((1 : ℝ) / m : EReal) * ENNReal.log ((tiltedMeasure X μ m t)
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
/-- For `0 < δ` and `0 < t` with `Λ'(t) = a`, we have
`-(ta - Λ(t)) - tδ ≤ liminfₙ n⁻¹ log μ(a ≤ Sₙ/n)` -/
private lemma Cramer.lower_bound_via_tilted (a t δ : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (ht_deriv : deriv (cgf (X 0) μ) t = a) :
    (-(t * a - cgf (X 0) μ t) : EReal) - (t * δ : EReal)
    ≤ liminf (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log (μ {ω | a ≤ empiricalMean X n ω})) atTop := by
  -- `(ta - Λ(t)) - tδ + n⁻¹ log tiltedMeasure(Sₙ/n ∈ [a, a + δ])
  --   ≤ n⁻¹ log μ(a ≤ Sₙ/n)`
  have h_pointwise : ∀ n : ℕ, 1 ≤ n →
      (-(t * a - cgf (X 0) μ t) - t * δ : EReal)
        + ((1 : ℝ) / n : EReal) * ENNReal.log ((tiltedMeasure X μ n t)
            {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})
      ≤ ((1 : ℝ) / n : EReal) * ENNReal.log (μ {ω | a ≤ empiricalMean X n ω}) := by
    intro n hn
    haveI : IsProbabilityMeasure (tiltedMeasure X μ n t) :=
      isProbabilityMeasure_tiltedMeasure X h_indep h_ident h_meas h_mgf t n
    have h_subset : {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)} ⊆
        {ω | a ≤ empiricalMean X n ω} := fun _ hω => hω.1
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    let F := {ω | a ≤ empiricalMean X n ω}
    have h_prob_mono : (μ E).toReal ≤ (μ F).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_subset)
    have h_log_ineq :
        ENNReal.log (ENNReal.ofReal (Real.exp (-n * (t * (a + δ) - cgf (X 0) μ t)) *
          ((tiltedMeasure X μ n t) E).toReal)) ≤ ENNReal.log (μ F) := by
      apply ENNReal.log_le_log
      rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
      linarith [h_prob_mono, change_of_measure_lower_bound X h_indep h_ident h_meas h_mgf
        a δ t n ht (integrable_exp_mul_partialSum X h_indep h_ident h_meas h_mgf t n)]
    calc (-(t * a - cgf (X 0) μ t) - t * δ : EReal)
          + ((1 : ℝ) / n : EReal) *
            ENNReal.log ((tiltedMeasure X μ n t) E)
        = ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal
            (Real.exp (-n * (t * (a + δ) - cgf (X 0) μ t)) *
              ((tiltedMeasure X μ n t) E).toReal)) := by
          symm
          by_cases h_tilted_zero : (tiltedMeasure X μ n t) E = 0
          · rw [h_tilted_zero]
            simp only [ENNReal.toReal_zero, mul_zero, ENNReal.ofReal_zero, ENNReal.log_zero]
            have h1n_pos : (0 : EReal) < ((1 : ℝ) / n : EReal) :=
              EReal.coe_pos.mpr (by positivity)
            rw [EReal.mul_bot_of_pos h1n_pos]
            simp only [EReal.add_bot]
          · exact log_exp_product_eq_neg_coef_plus_log n t a δ (cgf (X 0) μ t) _ hn
              h_tilted_zero (measure_ne_top _ _)
      _ ≤ ((1 : ℝ) / n : EReal) * ENNReal.log (μ F) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast h_log_ineq)
            (ereal_one_div_nat_nonneg n)
  -- The error term `n⁻¹ log tiltedMeasure(Sₙ/n ∈ [a, a + δ])` vanishes as `n → ∞`.
  have h_error_vanish := error_term_vanishes X h_indep h_ident h_meas h_mgf h_non_deg
    a t δ hδ ht_deriv
  let rhs_seq : ℕ → EReal := fun n =>
    (-(t * a - cgf (X 0) μ t) - t * δ : EReal)
    + ((1 : ℝ) / n : EReal) * ENNReal.log ((tiltedMeasure X μ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})
  have h_rhs_limit : Tendsto rhs_seq atTop
      (𝓝 ((-(t * a - cgf (X 0) μ t) : EReal) - (t * δ : EReal))) :=
    tendsto_const_add_vanishing _ _ h_error_vanish
  -- Combine the pointwise inequality and vanishing error term to conclude
  have h_eventually : ∀ᶠ (n : ℕ) in atTop,
      rhs_seq n ≤
      ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (μ {ω | a ≤ empiricalMean X n ω}) :=
    Filter.eventually_atTop.mpr ⟨1, h_pointwise⟩
  rw [← h_rhs_limit.liminf_eq]
  exact liminf_le_liminf h_eventually

include h_mgf h_non_deg in
/-- If `μ[X₁] ≤ a` and `Λ'(t) = a`, then `0 ≤ t` -/
private lemma Cramer.deriv_cgf_nonneg_of_integral_le (a : ℝ) (h_mean : μ[X 0] ≤ a) (t : ℝ)
    (ht_deriv : deriv (cgf (X 0) μ) t = a) :
    0 ≤ t := by
  by_contra! ht_neg
  have h_strict_mono : StrictMono (deriv (cgf (X 0) μ)) :=
    strictMono_of_deriv_pos fun x => by simpa [iteratedDeriv_succ] using h_non_deg x
  have := h_strict_mono ht_neg
  rw [ht_deriv, deriv_cgf_zero (mem_interior_integrableExpSet X h_mgf 0)] at this
  simp at this
  linarith

omit [IsProbabilityMeasure μ] in
include h_mgf in
/-- The CGF of `X 0` is analytic on all of `ℝ`. -/
private lemma analyticOn_cgf_univ : AnalyticOn ℝ (cgf (X 0) μ) Set.univ :=
  Set.eq_univ_of_forall (Cramer.mem_interior_integrableExpSet X h_mgf) ▸ analyticOn_cgf

omit [IsProbabilityMeasure μ] in
include h_mgf h_bdd h_non_deg in
/-- Given `Λ'(t) = a`, the rate function satisfies `rateFunction X μ a = ta - Λ(t)`. -/
private lemma Cramer.rateFunction_eq_of_deriv_eq (a t : ℝ)
    (ht_deriv : deriv (cgf (X 0) μ) t = a) :
    rateFunction X μ a = t * a - cgf (X 0) μ t := by
  rw [rateFunction]
  have h_analytic : AnalyticOn ℝ (cgf (X 0) μ) Set.univ := analyticOn_cgf_univ X h_mgf
  -- We proceed by proving inequality in both directions
  refine le_antisymm (ciSup_le fun s => ?_) (le_ciSup (h_bdd a) t)
  -- Sub-goal `sa - Λ(s) ≤ ta - Λ(t)`, i.e. `Λ(t) + a(s - t) ≤ Λ(s)`: the CGF is above its
  -- tangent line at `t`, as it is strictly convex (from `h_non_deg`: `0 < Λ''(x)`).
  have h_convex : StrictConvexOn ℝ Set.univ (cgf (X 0) μ) :=
    strictConvexOn_of_deriv2_pos' convex_univ h_analytic.continuousOn
      fun x _ => by simpa [← iteratedDeriv_eq_iterate] using h_non_deg x
  have h_diff : DifferentiableAt ℝ (cgf (X 0) μ) t :=
    h_analytic.differentiableOn.differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ t))
  suffices h_tangent : cgf (X 0) μ t + a * (s - t) ≤ cgf (X 0) μ s by linarith
  rcases lt_trichotomy s t with hst | rfl | hts
  · have h_slope := h_convex.convexOn.slope_le_of_hasDerivAt
      (Set.mem_univ s) (Set.mem_univ t) hst h_diff.hasDerivAt
    rw [ht_deriv, slope_def_field] at h_slope
    rw [← sub_nonneg]
    have : 0 < t - s := sub_pos.mpr hst
    nlinarith [(div_le_iff₀ this).mp h_slope]
  · simp
  · have h_slope := h_convex.convexOn.deriv_le_slope
      (Set.mem_univ t) (Set.mem_univ s) hts h_diff
    rw [ht_deriv, slope_def_field] at h_slope
    rw [← sub_nonneg]
    have : 0 < s - t := sub_pos.mpr hts
    nlinarith [(le_div_iff₀ this).mp h_slope]

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- Edge-case of `Cramer.neg_rateFunction_le_liminf` at `a = μ[X 0]` -/
private lemma Cramer.liminf_nonneg_at_mean (a : ℝ) (ht_deriv : deriv (cgf (X 0) μ) 0 = a) :
    (0 : EReal) ≤
      liminf (fun n : ℕ =>
        ((1 : ℝ) / (n : ℝ) : EReal) *
          ENNReal.log (μ {ω | a ≤ empiricalMean X n ω})) atTop := by
  -- `0 < Var[X]`
  have h_var_pos : 0 < variance (X 0) μ := by
    have h_int_zero : (0 : ℝ) ∈ interior (integrableExpSet (X 0) μ) :=
      mem_interior_integrableExpSet X h_mgf 0
    have h := variance_tilted_mul (X := X 0) (μ := μ) h_int_zero
    simp only [zero_mul, show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, tilted_zero] at h
    exact h ▸ h_non_deg 0
  -- `∃ c > 0` such that for all sufficiently large `n`, `c ≤ μ(a ≤ Sₙ/n)`
  -- i.e. the asymptotic lower bound `μ(a ≤ Sₙ/n)` is greater than 0, which we derive from CLT
  -- on the tilted measures, noting that at `t = 0`, the tilted measures `tiltedMeasure`
  -- coincide with `μ`.
  have h_prob_lower_bound : ∃ c > 0, ∀ᶠ n in atTop,
      c ≤ (μ {ω | a ≤ empiricalMean X n ω}).toReal := by
    have h_bound := eventually_tiltedMeasure_empiricalMean_mem_Icc_ge X h_indep h_ident h_meas h_mgf
      h_non_deg 0 a 1 (by norm_num) (1/4) (by norm_num) ht_deriv
    refine ⟨1/4, by norm_num, ?_⟩
    filter_upwards [h_bound] with n hn
    have h_eq_meas : tiltedMeasure X μ n 0 = μ := by
      change Measure.tilted μ (fun ω => 0 * partialSum X n ω) = μ
      simp_rw [zero_mul]; exact tilted_zero μ
    rw [h_eq_meas] at hn
    calc (1 / 4 : ℝ)
        = 1 / 2 - 1 / 4 := by norm_num
      _ ≤ (μ {ω | empiricalMean X n ω ∈ Set.Icc a (a + 1)}).toReal := hn
      _ ≤ (μ {ω | a ≤ empiricalMean X n ω}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun _ hω => hω.1)
  obtain ⟨c, hc_pos, h_eventually_lower⟩ := h_prob_lower_bound
  have h_lower_tendsto :
      Tendsto (fun n : ℕ => ((1 : ℝ) / n : EReal) * ENNReal.log (ENNReal.ofReal c))
        atTop (𝓝 0) := by
    rw [ENNReal.log_ofReal_of_pos hc_pos]
    refine (EReal.tendsto_const_div_atTop_nhds_zero_nat (C := (Real.log c : EReal))
      (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).congr fun n => ?_
    rw [EReal.div_eq_inv_mul, div_eq_mul_inv, EReal.coe_one, one_mul]
  have h_upper_tendsto : Tendsto (fun (_ : ℕ) => (0 : EReal)) atTop (𝓝 0) := tendsto_const_nhds
  -- Establish bounds to apply squeeze theorem
  -- `n⁻¹ log (c) ≤ n⁻¹ log μ(a ≤ Sₙ/n) ≤ 0`
  have h_squeeze : ∀ᶠ (m : ℕ) in atTop,
      ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal c)
      ≤ ((1 : ℝ) / (m : ℝ) : EReal) * ENNReal.log (μ {ω | a ≤ empiricalMean X m ω})
      ∧ ((1 : ℝ) / (m : ℝ) : EReal) *
        ENNReal.log (μ {ω | a ≤ empiricalMean X m ω}) ≤ 0 := by
    filter_upwards [h_eventually_lower] with m hm_lower
    refine ⟨mul_le_mul_of_nonneg_left ?_ (ereal_one_div_nat_nonneg m),
      mul_nonpos_of_nonneg_of_nonpos (ereal_one_div_nat_nonneg m) ?_⟩
    · exact ENNReal.log_le_log <|
        (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hm_lower
    · exact ENNReal.log_le_zero_iff.mpr prob_le_one
  -- `n⁻¹ log μ(a ≤ Sₙ/n) → 0` by squeeze theorem
  have h_tendsto :
      Tendsto (fun n : ℕ =>
          ((1 : ℝ) / n : EReal) * ENNReal.log (μ {ω | a ≤ empiricalMean X n ω}))
        atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lower_tendsto h_upper_tendsto
      (h_squeeze.mono fun _ hn => hn.1) (h_squeeze.mono fun _ hn => hn.2)
  exact h_tendsto.liminf_eq.symm.le

include h_indep h_ident h_meas h_mgf h_bdd h_non_deg h_exposed in
/-- **Cramér's Theorem (Lower Bound)**: Given `E[X 0] ≤ a`,
`-rateFunction X μ a ≤ liminfₙ n⁻¹ log μ(a ≤ Sₙ/n)` -/
theorem Cramer.neg_rateFunction_le_liminf (a : ℝ) (h_mean : μ[X 0] ≤ a) :
    (- rateFunction X μ a : EReal) ≤
      liminf (fun n : ℕ =>
        ((1 : ℝ) / (n : ℝ) : EReal) *
          ENNReal.log (μ {ω | a ≤ empiricalMean X n ω})) atTop := by
  -- Get the `t` such that `Λ'(t) = a`.
  obtain ⟨t, ht_deriv⟩ := h_exposed a h_mean
  have ht_nonneg : 0 ≤ t := deriv_cgf_nonneg_of_integral_le X h_mgf h_non_deg a h_mean t ht_deriv
  have h_rate_eq : rateFunction X μ a = t * a - cgf (X 0) μ t :=
    rateFunction_eq_of_deriv_eq X h_mgf h_bdd h_non_deg a t ht_deriv
  rw [h_rate_eq]
  let LHS_val :=
    liminf (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log (μ {ω | a ≤ empiricalMean X n ω}))
      atTop
  -- Casework on whether `t = 0`
  by_cases ht_zero : t = 0
  · -- `t = 0` (which implies `a = μ[X]` from solving `a = Λ'(t) = Λ'(0)`).
    subst ht_zero
    simp only [zero_mul, cgf_zero, sub_zero, EReal.coe_zero, neg_zero]
    exact liminf_nonneg_at_mean X h_indep h_ident h_meas h_mgf h_non_deg a ht_deriv
  have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_zero)
  -- Bound the liminf from below for any fixed positive `δ` using the tilted measure bounds.
  have h_bound_for_all_delta : ∀ (δ : ℝ), 0 < δ →
      (-(t * a - cgf (X 0) μ t) - t * δ : EReal) ≤ LHS_val := fun δ hδ =>
    lower_bound_via_tilted X h_indep h_ident h_meas h_mgf h_non_deg a t δ hδ ht_pos ht_deriv
  -- Conclude the lower bound by taking `δ → 0`.
  refine EReal.le_of_forall_sub_le fun ε hε => ?_
  have h := h_bound_for_all_delta (ε / t) (div_pos hε ht_pos)
  rwa [show ((t : EReal) * (ε / t : ℝ) : EReal) = ((ε : ℝ) : EReal) from by
    rw [← EReal.coe_mul]; norm_cast; field_simp] at h

end ProbabilityTheory
