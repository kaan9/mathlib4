/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.Basic
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Cramér's Theorem — CLT over Tilted Measures

This file provides a proof of the Central Limit Therem over a sequence of tilted measures,
used in the proof of the lower bound of Cramér's theorem.

Under the assumptions of Cramér's theorem, for `t` with `Λ'(t) = a` the family of tilted measures
`ℚₙₜ := ℙ.tilted (t · Sₙ)` satisfies a CLT statement:
The normalized partial sum `Zₙ := (Sₙ - n Λ'(t))/√(n Λ''(t))` converges in distribution to `𝒩(0,1)`
under `ℚₙₜ` as `n → ∞`.
An immediate corrollary is a concentration statement used in `LowerBound.lean`.

## Main Definitions

* `μₜ X t`: the pushforward measure of `ℙ` by `X₀`, tilted by `t · x`,
* `νₜ X t`: the pushforward measure of `μₜ X t` by a linear function to standardize it to zero mean
  and unit variance.
* `Z X t n`: the standardized partial sum `(Sₙ - n Λ'(t)) / √(n Λ''(t))`.

## Main Results

* `tendsto_charFun_Z_ℚₙₜ`: under `ℚₙₜ`, the characteristic function of `Zₙ` converges pointwise to
  that of `𝒩(0,1)`.
* `eventually_ℚₙₜ_empiricalMean_mem_Icc_ge`: the concentration statement for the lower bound proof:
  For every `δ, ε > 0` and `t` with `Λ'(t) = a`, eventually `1/2 - ε ≤ ℚₙₜ(Sₙ/n ∈ [a, a+δ])`.

-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω]

/-- The law of `X 0` under `ℙ`, tilted by `t · x`. -/
noncomputable def μₜ (X : ℕ → Ω → ℝ) (t : ℝ) : Measure ℝ :=
  ((ℙ : Measure Ω).map (X 0)).tilted (fun x => t * x)

/-- The push-forward of `μₜ` by the map `x ↦ (x - Λ'(t)) / √Λ''(t)`,
  so that it has zero mean and unit variance. -/
noncomputable def νₜ (X : ℕ → Ω → ℝ) (t : ℝ) : Measure ℝ :=
  (μₜ X t).map
    (fun x => (x - deriv (cgf (X 0) ℙ) t) / Real.sqrt (iteratedDeriv 2 (cgf (X 0) ℙ) t))

/-- The standardized partial sum under `ℚₙₜ`: `Z = (Sₙ - n Λ'(t)) / √(n Λ''(t))`. -/
noncomputable def Z (X : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) : Ω → ℝ := fun ω =>
  (partialSum X n ω - n * deriv (cgf (X 0) ℙ) t) /
    Real.sqrt (n * iteratedDeriv 2 (cgf (X 0) ℙ) t)

variable (X : ℕ → Ω → ℝ)

/- Assumptions for Cramér's theorem -/
variable (h_indep : iIndepFun X ℙ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
variable (h_non_deg : ∀ t : ℝ, 0 < iteratedDeriv 2 (cgf (X 0) ℙ) t)

include h_meas in
/-- The MGF of the identity under `μₜ` at `u` equals `mgf(X₀)(t + u)/mgf(X₀)(t)`. -/
lemma mgf_id_tiltedLaw (t u : ℝ) :
    mgf id (μₜ X t) u = mgf (X 0) ℙ (t + u) / mgf (X 0) ℙ t := by
  have hX0 : AEMeasurable (X 0) ℙ := (h_meas 0).aemeasurable
  simp only [mgf, μₜ, id]
  rw [integral_exp_tilted (fun x => t * x) (fun x => u * x),
    integral_map hX0 (by fun_prop), integral_map hX0 (by fun_prop)]
  simp [add_mul]

include h_meas h_mgf in
private lemma t_mem_interior_integrableExpSet_id (t : ℝ) :
    t ∈ interior (integrableExpSet id ((ℙ : Measure Ω).map (X 0))) := by
  have h_univ : integrableExpSet id ((ℙ : Measure Ω).map (X 0)) = Set.univ := by
    ext s
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true, id]
    exact (integrable_map_measure (by fun_prop) (h_meas 0).aemeasurable).mpr (h_mgf s)
  rw [h_univ, interior_univ]
  exact Set.mem_univ t

include h_meas in
private lemma cgf_id_map_eq : cgf id ((ℙ : Measure Ω).map (X 0)) = cgf (X 0) ℙ := by
  ext s; simp [cgf, mgf_id_map (h_meas 0).aemeasurable]

private lemma t_mul_eq_mul_id (t : ℝ) : (fun x : ℝ => t * x) = (t * id ·) := rfl

include h_meas h_mgf in
/-- The mean of `μₜ` is `Λ'(t)`. -/
lemma integral_id_tiltedLaw (t : ℝ) : ∫ x, x ∂(μₜ X t) = deriv (cgf (X 0) ℙ) t := by
  simp only [μₜ]
  rw [t_mul_eq_mul_id, ← cgf_id_map_eq X h_meas]
  exact integral_tilted_mul_self (t_mem_interior_integrableExpSet_id X h_meas h_mgf t)

include h_meas h_mgf in
/-- The variance of `μₜ` is `Λ''(t)`. -/
lemma variance_id_tiltedLaw (t : ℝ) :
    Var[id; μₜ X t] = iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  simp only [μₜ]
  rw [t_mul_eq_mul_id, ← cgf_id_map_eq X h_meas]
  exact variance_tilted_mul (t_mem_interior_integrableExpSet_id X h_meas h_mgf t)

include h_meas h_mgf in
/-- The identity is in `L²` under `μₜ`. -/
lemma memLp_id_tiltedLaw (t : ℝ) : MemLp (id : ℝ → ℝ) 2 (μₜ X t) := by
  simp only [μₜ]
  rw [t_mul_eq_mul_id]
  exact memLp_tilted_mul (t_mem_interior_integrableExpSet_id X h_meas h_mgf t) 2

/-! ### Algebraic Identities -/

/-- Algebraic identity: for `t` with `Λ'(t) = a` and `n ≥ 1`, the event
`{Sₙ/n ∈ [a, a+δ]}` is exactly `{Zₙ ∈ [0, δ · √(n / Λ''(t))]}`. -/
lemma empiricalMean_mem_Icc_iff_Z_mem_Icc (t a δ : ℝ) (n : ℕ) (hn : 0 < n)
    (h_non_deg_t : 0 < iteratedDeriv 2 (cgf (X 0) ℙ) t)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) (ω : Ω) :
    empiricalMean X n ω ∈ Set.Icc a (a + δ) ↔
      Z X t n ω ∈ Set.Icc (0 : ℝ)
        (δ * Real.sqrt (n / iteratedDeriv 2 (cgf (X 0) ℙ) t)) := by
  rw [Set.mem_Icc, Set.mem_Icc, empiricalMean, Z, ht_deriv]
  set v := iteratedDeriv 2 (cgf (X 0) ℙ) t
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnv : (0 : ℝ) < Real.sqrt (n * v) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ hn', div_le_iff₀ hn', le_div_iff₀ hnv, div_le_iff₀ hnv]
  have key : Real.sqrt (n / v) * Real.sqrt (n * v) = n := by
    rw [← Real.sqrt_mul (by positivity), show (n / v * (n * v) : ℝ) = n ^ 2 by field_simp,
      Real.sqrt_sq hn'.le]
  refine ⟨fun ⟨h1, h2⟩ => ⟨by linarith, ?_⟩, fun ⟨h1, h2⟩ => ⟨by linarith, ?_⟩⟩ <;> nlinarith [key]

include h_meas h_mgf h_non_deg in
/-- The second moment of `νₜ` is `1`. -/
lemma integral_sq_id_stdTiltedLaw (t : ℝ) :
    ∫ x, x ^ 2 ∂(νₜ X t) = 1 := by
  have hv := h_non_deg t
  set m := deriv (cgf (X 0) ℙ) t
  set v := iteratedDeriv 2 (cgf (X 0) ℙ) t
  simp only [νₜ]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hμ_mean : ∫ x, x ∂μₜ X t = m :=
    integral_id_tiltedLaw X h_meas h_mgf t
  have hvar : Var[id; μₜ X t] = v :=
    variance_id_tiltedLaw X h_meas h_mgf t
  have hint_sq : ∫ x, (x - m) ^ 2 ∂μₜ X t = v := by
    rw [← hvar, variance_eq_integral aemeasurable_id]
    congr 1; ext x; simp [hμ_mean]
  rw [show (fun x : ℝ => ((x - m) / Real.sqrt v) ^ 2) = fun x => (x - m) ^ 2 / v from
    funext fun x => by rw [div_pow, Real.sq_sqrt hv.le], integral_div, hint_sq, div_self hv.ne']

/-! ### Lemmas requiring `ℙ` to be a probability measure -/

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

include h_meas h_mgf in
/-- `μₜ` is a probability measure. -/
lemma isProbabilityMeasure_tiltedLaw (t : ℝ) :
    IsProbabilityMeasure (μₜ X t) := by
  haveI : IsProbabilityMeasure ((ℙ : Measure Ω).map (X 0)) :=
    Measure.isProbabilityMeasure_map (h_meas 0).aemeasurable
  exact isProbabilityMeasure_tilted
    ((integrable_map_measure (by fun_prop) (h_meas 0).aemeasurable).mpr (h_mgf t))

/-! ### Properties of `νₜ` -/

include h_meas h_mgf in
/-- `νₜ` is a probability measure. -/
lemma isProbabilityMeasure_stdTiltedLaw (t : ℝ) :
    IsProbabilityMeasure (νₜ X t) :=
  haveI := isProbabilityMeasure_tiltedLaw X h_meas h_mgf t
  Measure.isProbabilityMeasure_map (by fun_prop)

include h_meas h_mgf in
/-- The mean of `νₜ` is `0`. -/
lemma integral_id_stdTiltedLaw (t : ℝ) :
    ∫ x, x ∂(νₜ X t) = 0 := by
  simp only [νₜ]
  haveI : IsProbabilityMeasure (μₜ X t) :=
    isProbabilityMeasure_tiltedLaw X h_meas h_mgf t
  have hid : Integrable (fun x : ℝ => x) (μₜ X t) :=
    (memLp_id_tiltedLaw X h_meas h_mgf t).integrable (by norm_num)
  rw [integral_map (by fun_prop) (by fun_prop), integral_div,
    integral_sub hid (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_id_tiltedLaw X h_meas h_mgf t, sub_self, zero_div]

include h_meas h_mgf in
/-- The identity is in `L²` under `νₜ`. -/
lemma memLp_id_stdTiltedLaw (t : ℝ) :
    MemLp (id : ℝ → ℝ) 2 (νₜ X t) := by
  simp only [νₜ]
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  haveI : IsProbabilityMeasure (μₜ X t) :=
    isProbabilityMeasure_tiltedLaw X h_meas h_mgf t
  have h_sub : MemLp (fun x : ℝ => x - deriv (cgf (X 0) ℙ) t) 2 (μₜ X t) :=
    (memLp_id_tiltedLaw X h_meas h_mgf t).sub (memLp_const _)
  have h_div : MemLp (fun x : ℝ => (x - deriv (cgf (X 0) ℙ) t) *
      (Real.sqrt (iteratedDeriv 2 (cgf (X 0) ℙ) t))⁻¹) 2 (μₜ X t) :=
    h_sub.mul_const _
  exact h_div.congr_norm (by fun_prop) (Eventually.of_forall fun x => by
    simp [Function.comp, div_eq_mul_inv])

/-! ### Factorization of `X₀, …, Xₙ₋₁` under `ℚₙₜ`

Under the tilted measure `ℚₙₜ = ℙ.tilted(t · Sₙ)`, the coordinates `X₀, …, Xₙ₋₁` are
still independent and each has law `μₜ`.
These follow from factoring the tilting density `exp(t Sₙ) = ∏ᵢ exp(t Xᵢ)`. -/

private lemma measurable_ennreal_ofReal_exp_t_mul (t : ℝ) :
    Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x))) :=
  (measurable_id.const_mul t |>.exp).ennreal_ofReal

omit [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- `↑e^(t · Sₙ) = ∏ᵢ ↑e^(t Xᵢ)` where `↑` is coercion to extended reals. -/
private lemma ennreal_ofReal_exp_t_partialSum_eq_prod (t : ℝ) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (Real.exp (t * partialSum X n ω)) =
    ∏ j ∈ Finset.range n, ENNReal.ofReal (Real.exp (t * X j ω)) := by
  rw [show Real.exp (t * partialSum X n ω) = ∏ j ∈ Finset.range n, Real.exp (t * X j ω) by
    simp [partialSum, Finset.sum_apply, Finset.mul_sum, Real.exp_sum],
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
include h_meas in
/-- `↑e^(t Xᵢ)` is measurable for each `i`. -/
private lemma measurable_ennreal_ofReal_exp_t_mul_X (t : ℝ) (j : ℕ) :
    Measurable (fun ω => ENNReal.ofReal (Real.exp (t * X j ω))) :=
  (measurable_ennreal_ofReal_exp_t_mul t).comp (h_meas j)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
include h_indep in
/-- The family `↑e^(t Xᵢ)` is independent. -/
private lemma iIndepFun_ennreal_ofReal_exp_t_mul_X (t : ℝ) :
    iIndepFun (fun j ω => ENNReal.ofReal (Real.exp (t * X j ω))) ℙ :=
  h_indep.comp (fun _ x => ENNReal.ofReal (Real.exp (t * x)))
    (fun _ => measurable_ennreal_ofReal_exp_t_mul t)

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
include h_ident h_mgf in
/-- The integral of `↑e^(t Xᵢ)` against `ℙ` is `↑ mgf(X 0)(t)`. -/
private lemma lintegral_ennreal_ofReal_exp_t_mul_X (t : ℝ) (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X j ω)) ∂ℙ = ENNReal.ofReal (mgf (X 0) ℙ t) :=
  ((h_ident j).comp (measurable_ennreal_ofReal_exp_t_mul t)).lintegral_eq.trans
    (ofReal_integral_eq_lintegral_ofReal (h_mgf t)
      (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm

include h_indep h_ident h_meas h_mgf in
/-- `MGF(X₁)` and `MGF(Sₙ)` are positive and `↑MGF(Sₙ) = (↑MGF(X₁))ⁿ` -/
private lemma mgf_preamble (n : ℕ) (t : ℝ) :
    0 < mgf (X 0) ℙ t ∧
    0 < mgf (partialSum X n) ℙ t ∧
    ENNReal.ofReal (mgf (partialSum X n) ℙ t) = (ENNReal.ofReal (mgf (X 0) ℙ t)) ^ n := by
  have hM₀_pos : 0 < mgf (X 0) ℙ t := integral_exp_pos (h_mgf t)
  refine ⟨hM₀_pos,
    integral_exp_pos (integrable_exp_sum X h_indep h_ident h_meas h_mgf t n), ?_⟩
  rw [show mgf (partialSum X n) ℙ t = (mgf (X 0) ℙ t) ^ n by
      rw [mgf_sum_eq_exp_n_prod_cgf X h_indep h_ident h_meas h_mgf n t, cgf, ← Real.log_pow,
        Real.exp_log (pow_pos hM₀_pos n)],
    ENNReal.ofReal_pow hM₀_pos.le]

include h_indep h_ident h_meas h_mgf in
/-- Under `ℚₙₜ`, each `Xᵢ` (for `i < n`) has the same law `μₜ`. -/
lemma map_X_ℚₙₜ (t : ℝ) (n : ℕ) {i : ℕ} (hi : i < n) :
    (ℚₙₜ X ℙ n t).map (X i) = μₜ X t := by
  obtain ⟨hM₀_pos, hMₙ_pos, hMₙ_pow⟩ := mgf_preamble X h_indep h_ident h_meas h_mgf n t
  have hi_mem : i ∈ Finset.range n := Finset.mem_range.mpr hi
  have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  set M₀ := mgf (X 0) ℙ t with hM₀_def
  set Mₙ := mgf (partialSum X n) ℙ t with hMₙ_def
  have hM₀_nn : ENNReal.ofReal M₀ ≠ 0 := (ENNReal.ofReal_pos.mpr hM₀_pos).ne'
  have hMₙ_nn : ENNReal.ofReal Mₙ ≠ 0 := (ENNReal.ofReal_pos.mpr hMₙ_pos).ne'
  have hMₙ_inv_ne_top : (ENNReal.ofReal Mₙ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hMₙ_nn
  have hM₀_inv_ne_top : (ENNReal.ofReal M₀)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hM₀_nn
  have hk_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x))) :=
    measurable_ennreal_ofReal_exp_t_mul t
  set e : ℕ → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal (Real.exp (t * X j ω))
  have he_meas := measurable_ennreal_ofReal_exp_t_mul_X X h_meas t
  have he_indep := iIndepFun_ennreal_ofReal_exp_t_mul_X X h_indep t
  have he_lint := lintegral_ennreal_ofReal_exp_t_mul_X X h_ident h_mgf t
  apply Measure.ext_of_lintegral
  intro g hg
  have hg_exp : Measurable (fun x : ℝ => g x * ENNReal.ofReal (Real.exp (t * x))) :=
    hg.mul hk_meas
  set I₀ : ℝ≥0∞ := ∫⁻ ω, g (X 0 ω) * e 0 ω ∂ℙ with hI₀_def
  have hI_eq : (∫⁻ ω, g (X i ω) * e i ω ∂ℙ) = I₀ :=
    ((h_ident i).comp hg_exp).lintegral_eq
  have hmeas_gxe : Measurable (fun ω : Ω => g (X i ω) * e i ω) :=
    (hg.comp (h_meas i)).mul (he_meas i)
  have hmeas_prod : Measurable fun ω => ∏ j ∈ (Finset.range n).erase i, e j ω :=
    Finset.measurable_prod _ fun j _ => he_meas j
  set ψ : ℕ → ℝ → ℝ≥0∞ := fun j x =>
    if j = i then g x * ENNReal.ofReal (Real.exp (t * x))
    else ENNReal.ofReal (Real.exp (t * x))
  have hψ_meas : ∀ j, Measurable (ψ j) := fun j => by
    simp only [ψ]; split_ifs; exacts [hg_exp, hk_meas]
  have hindep : IndepFun (fun ω => g (X i ω) * e i ω)
      (fun ω => ∏ j ∈ (Finset.range n).erase i, e j ω) ℙ := by
    have h : IndepFun (∏ j ∈ (Finset.range n).erase i, (ψ j ∘ X j)) (ψ i ∘ X i) ℙ :=
      (h_indep.comp ψ hψ_meas).indepFun_finset_prod_of_notMem
        (fun j => (hψ_meas j).comp (h_meas j)) (Finset.notMem_erase i _)
    convert h.symm using 1
    · ext ω; simp [ψ, e]
    · ext ω; rw [Finset.prod_apply]
      exact Finset.prod_congr rfl fun j hj => by simp [ψ, e, Finset.ne_of_mem_erase hj]
  rw [lintegral_map hg (h_meas i)]
  simp only [ℚₙₜ, μₜ, lintegral_tilted]
  have hsum_prod : ∀ ω, ENNReal.ofReal (Real.exp (t * partialSum X n ω) /
      ∫ x, Real.exp (t * partialSum X n x) ∂ℙ) * g (X i ω) =
      (g (X i ω) * e i ω) * (∏ j ∈ (Finset.range n).erase i, e j ω) *
        (ENNReal.ofReal Mₙ)⁻¹ := fun ω => by
    rw [show (∫ x, Real.exp (t * partialSum X n x) ∂ℙ) = Mₙ from rfl,
      ENNReal.ofReal_div_of_pos hMₙ_pos, div_eq_mul_inv,
      ennreal_ofReal_exp_t_partialSum_eq_prod X t n ω,
      ← Finset.mul_prod_erase _ (e · ω) hi_mem]
    ring
  simp_rw [hsum_prod]
  rw [lintegral_mul_const' _ _ hMₙ_inv_ne_top,
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hmeas_gxe.aemeasurable hmeas_prod.aemeasurable hindep,
    lintegral_prod_eq_prod_lintegral_of_indepFun _ _ he_indep he_meas,
    Finset.prod_congr rfl (fun j _ => he_lint j), Finset.prod_const,
    Finset.card_erase_of_mem hi_mem, Finset.card_range, hI_eq, hMₙ_pow]
  have hmap_mgf : (∫ x : ℝ, Real.exp (t * x) ∂Measure.map (X 0) ℙ) = M₀ :=
    integral_map (h_meas 0).aemeasurable ((measurable_id.const_mul t).exp).aestronglyMeasurable
  conv_rhs => rw [show (fun x : ℝ => ENNReal.ofReal (Real.exp (t * x) /
      ∫ y, Real.exp (t * y) ∂Measure.map (X 0) ℙ) * g x) = fun x =>
    (g x * ENNReal.ofReal (Real.exp (t * x))) * (ENNReal.ofReal M₀)⁻¹ from funext fun x => by
      rw [hmap_mgf, ENNReal.ofReal_div_of_pos hM₀_pos, div_eq_mul_inv]; ring]
  rw [lintegral_mul_const' _ _ hM₀_inv_ne_top, lintegral_map hg_exp (h_meas 0), ← hI₀_def]
  rw [show (ENNReal.ofReal M₀) ^ n = (ENNReal.ofReal M₀) ^ (n - 1) * ENNReal.ofReal M₀ by
      conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn_pos).symm, pow_succ],
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hM₀_nn))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_lt_top.ne)),
    mul_assoc, ← mul_assoc ((ENNReal.ofReal M₀) ^ (n - 1)),
    ENNReal.mul_inv_cancel (pow_ne_zero _ hM₀_nn) (ENNReal.pow_ne_top ENNReal.ofReal_lt_top.ne),
    one_mul]

include h_indep h_ident h_meas h_mgf in
/-- Under `ℚₙₜ`, `Xᵢ` (for `i < n`) are independent. -/
lemma iIndepFun_range_ℚₙₜ (t : ℝ) (n : ℕ) :
    iIndepFun (fun i : Finset.range n => X i.val) (ℚₙₜ X ℙ n t) := by
  classical
  obtain ⟨hM₀_pos, hMₙ_pos, hMₙ_pow⟩ := mgf_preamble X h_indep h_ident h_meas h_mgf n t
  set M₀ := mgf (X 0) ℙ t with hM₀_def
  set Mₙ := mgf (partialSum X n) ℙ t with hMₙ_def
  have hM₀_nn : ENNReal.ofReal M₀ ≠ 0 := (ENNReal.ofReal_pos.mpr hM₀_pos).ne'
  have hM₀_top : ENNReal.ofReal M₀ ≠ ∞ := ENNReal.ofReal_lt_top.ne
  have hMₙ_nn : ENNReal.ofReal Mₙ ≠ 0 := (ENNReal.ofReal_pos.mpr hMₙ_pos).ne'
  have hMₙ_inv_ne_top : (ENNReal.ofReal Mₙ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hMₙ_nn
  set e : ℕ → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal (Real.exp (t * X j ω)) with he_def
  have he_meas := measurable_ennreal_ofReal_exp_t_mul_X X h_meas t
  have he_indep := iIndepFun_ennreal_ofReal_exp_t_mul_X X h_indep t
  have he_lint := lintegral_ennreal_ofReal_exp_t_mul_X X h_ident h_mgf t
  have hsum_eq : ∀ ω,
      ENNReal.ofReal (Real.exp (t * partialSum X n ω)) =
      ∏ j ∈ Finset.range n, e j ω :=
    fun ω => ennreal_ofReal_exp_t_partialSum_eq_prod X t n ω
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  let A' : ℕ → Set ℝ := fun j =>
    if hj : j < n then
      if h : ⟨j, Finset.mem_range.mpr hj⟩ ∈ S then sets ⟨j, Finset.mem_range.mpr hj⟩
      else Set.univ
    else Set.univ
  have hA'_meas : ∀ j, MeasurableSet (A' j) := fun j => by
    simp only [A']; split_ifs with hj hjS
    exacts [hsets _ hjS, MeasurableSet.univ, MeasurableSet.univ]
  have hA'_inS : ∀ (i : Finset.range n), i ∈ S → A' (i : ℕ) = sets i := by
    intro i hi
    have hi_lt : (i : ℕ) < n := Finset.mem_range.mp i.2
    have heq : (⟨(i : ℕ), Finset.mem_range.mpr hi_lt⟩ : Finset.range n) = i := Subtype.ext rfl
    simp only [A', dif_pos hi_lt]
    rw [dif_pos (by rw [heq]; exact hi), heq]
  let φ : ℕ → ℝ → ℝ≥0∞ := fun j x =>
    (A' j).indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal (Real.exp (t * x))
  have hφ_meas : ∀ j, Measurable (φ j) := fun j =>
    (measurable_const.indicator (hA'_meas j)).mul (measurable_ennreal_ofReal_exp_t_mul t)
  have hφ_comp_indep : iIndepFun (fun j => φ j ∘ X j) ℙ := h_indep.comp φ hφ_meas
  have hφ_meas' : ∀ j, Measurable (fun ω => φ j (X j ω)) :=
    fun j => (hφ_meas j).comp (h_meas j)
  have hφ_lint_not_inS : ∀ j, (∀ hj : j < n, ⟨j, Finset.mem_range.mpr hj⟩ ∉ S) →
      ∫⁻ ω, φ j (X j ω) ∂ℙ = ENNReal.ofReal M₀ := by
    intro j hj_notmem
    refine (lintegral_congr fun ω => ?_).trans (he_lint j)
    simp only [φ, A']; split_ifs with hj hjS
    · exact absurd hjS (hj_notmem hj)
    · rw [Set.indicator_univ]; simp
    · rw [Set.indicator_univ]; simp
  have hprod_indicator : ∀ ω,
      ∏ j ∈ Finset.range n, φ j (X j ω) =
      (⋂ i ∈ S, (fun ω' => X (i : ℕ) ω') ⁻¹' sets i).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ∏ j ∈ Finset.range n, e j ω := by
    intro ω
    by_cases hω : ω ∈ ⋂ i ∈ S, (fun ω' => X (i : ℕ) ω') ⁻¹' sets i
    · rw [Set.indicator_of_mem hω, one_mul]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjn : j < n := Finset.mem_range.mp hj
      change (A' j).indicator _ (X j ω) * _ = e j ω
      by_cases hjS : (⟨j, Finset.mem_range.mpr hjn⟩ : Finset.range n) ∈ S
      · rw [hA'_inS ⟨j, Finset.mem_range.mpr hjn⟩ hjS]
        have hmem : X j ω ∈ sets ⟨j, Finset.mem_range.mpr hjn⟩ :=
          Set.mem_iInter₂.mp hω _ hjS
        rw [Set.indicator_of_mem hmem, one_mul]
      · have hA'_univ : A' j = Set.univ := by
          simp only [A', dif_pos hjn, dif_neg hjS]
        rw [hA'_univ, Set.indicator_univ, one_mul]
    · rw [Set.indicator_of_notMem hω, zero_mul]
      have : ∃ i ∈ S, X (i : ℕ) ω ∉ sets i := by
        by_contra! h_all
        exact hω (Set.mem_iInter₂.mpr h_all)
      obtain ⟨i, hiS, hi⟩ := this
      apply Finset.prod_eq_zero (i.2 : (i : ℕ) ∈ Finset.range n)
      change (A' (i : ℕ)).indicator _ (X (i : ℕ) ω) * _ = 0
      rw [hA'_inS i hiS, Set.indicator_of_notMem hi, zero_mul]
  have hIcap_meas : MeasurableSet
      (⋂ i ∈ S, (fun ω => X (i : ℕ) ω) ⁻¹' sets i) :=
    .biInter (Set.to_countable _) fun i hi => (h_meas _) (hsets i hi)
  have hfun_eq : ∀ ω,
      ENNReal.ofReal (Real.exp (t * partialSum X n ω) / Mₙ) =
      ENNReal.ofReal (Real.exp (t * partialSum X n ω)) * (ENNReal.ofReal Mₙ)⁻¹ := fun ω => by
    rw [ENNReal.ofReal_div_of_pos hMₙ_pos, div_eq_mul_inv]
  have hLHS :
      (ℚₙₜ X ℙ n t) (⋂ i ∈ S, (fun ω => X i.val ω) ⁻¹' sets i) =
      (ENNReal.ofReal Mₙ)⁻¹ *
        ∫⁻ ω, ∏ j ∈ Finset.range n, φ j (X j ω) ∂ℙ := by
    simp only [ℚₙₜ]
    rw [tilted_apply' _ _ hIcap_meas]
    change ∫⁻ ω in _, ENNReal.ofReal (Real.exp (t * partialSum X n ω) / Mₙ) ∂ℙ = _
    rw [setLIntegral_congr_fun hIcap_meas (fun ω _ => hfun_eq ω),
      lintegral_mul_const' _ _ hMₙ_inv_ne_top, mul_comm, ← lintegral_indicator hIcap_meas]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [hprod_indicator ω]
    by_cases hω : ω ∈ ⋂ i ∈ S, (fun ω' => X (i : ℕ) ω') ⁻¹' sets i
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, one_mul, hsum_eq ω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  have hLHS_factor :
      ∫⁻ ω, ∏ j ∈ Finset.range n, φ j (X j ω) ∂ℙ =
      ∏ j ∈ Finset.range n, ∫⁻ ω, φ j (X j ω) ∂ℙ :=
    lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hφ_comp_indep hφ_meas'
  have hAᵢ_meas : ∀ i ∈ S, MeasurableSet ((X (i : ℕ)) ⁻¹' sets i) := fun i hi =>
    (h_meas _) (hsets i hi)
  have h_single : ∀ (i : Finset.range n) (hi : i ∈ S),
      (ℚₙₜ X ℙ n t) ((X (i : ℕ)) ⁻¹' sets i) =
      (ENNReal.ofReal Mₙ)⁻¹ *
        (∫⁻ ω, (sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) *
          e (i : ℕ) ω ∂ℙ) *
        ∏ j ∈ (Finset.range n).erase (i : ℕ), ENNReal.ofReal M₀ := by
    intro i hi
    have hmeas_i : MeasurableSet ((X (i : ℕ)) ⁻¹' sets i) := hAᵢ_meas _ hi
    simp only [ℚₙₜ]
    rw [tilted_apply' _ _ hmeas_i]
    change ∫⁻ ω in _, ENNReal.ofReal (Real.exp (t * partialSum X n ω) / Mₙ) ∂ℙ = _
    rw [setLIntegral_congr_fun hmeas_i (fun ω _ => hfun_eq ω),
      lintegral_mul_const' _ _ hMₙ_inv_ne_top, mul_right_comm, ← lintegral_indicator hmeas_i]
    have hi_range : (i : ℕ) ∈ Finset.range n := i.2
    have hrewrite : ∀ ω,
        ((X (i : ℕ)) ⁻¹' sets i).indicator
          (fun a => ENNReal.ofReal (Real.exp (t * partialSum X n a))) ω =
        ((sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) * e (i : ℕ) ω) *
          ∏ j ∈ (Finset.range n).erase (i : ℕ), e j ω := by
      intro ω
      rw [Set.indicator]
      by_cases hω : X (i : ℕ) ω ∈ sets i
      · rw [hsum_eq ω]
        have hhω : ω ∈ (X (i : ℕ)) ⁻¹' sets i := hω
        simp only [hhω, if_true]
        rw [Set.indicator_of_mem hω]
        rw [← Finset.mul_prod_erase _ _ hi_range]
        ring
      · have hhω : ω ∉ (X (i : ℕ)) ⁻¹' sets i := hω
        simp only [hhω, if_false]
        rw [Set.indicator_of_notMem hω]
        simp
    rw [lintegral_congr hrewrite]
    have hmeas_first : AEMeasurable
        (fun ω => (sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) *
          e (i : ℕ) ω) ℙ :=
      ((measurable_const.indicator (hsets _ hi)).comp (h_meas _)).mul
        (he_meas _) |>.aemeasurable
    have hmeas_rest : AEMeasurable
        (fun ω => ∏ j ∈ (Finset.range n).erase (i : ℕ), e j ω) ℙ :=
      (Finset.measurable_prod _ (fun j _ => he_meas j)).aemeasurable
    have hindep_first_rest :
        IndepFun (fun ω => (sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) *
            e (i : ℕ) ω)
          (fun ω => ∏ j ∈ (Finset.range n).erase (i : ℕ), e j ω) ℙ := by
      let ψ : ℕ → ℝ → ℝ≥0∞ := fun j x =>
        if j = (i : ℕ) then
          (sets i).indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal (Real.exp (t * x))
        else ENNReal.ofReal (Real.exp (t * x))
      have hψ_meas : ∀ j, Measurable (ψ j) := by
        intro j
        simp only [ψ]
        split_ifs
        · exact (measurable_const.indicator (hsets _ hi)).mul
            (measurable_ennreal_ofReal_exp_t_mul t)
        · exact measurable_ennreal_ofReal_exp_t_mul t
      convert ((h_indep.comp ψ hψ_meas).indepFun_finset_prod_of_notMem
        (fun j => (hψ_meas j).comp (h_meas j))
        (Finset.notMem_erase (i : ℕ) (Finset.range n))).symm using 1
      · ext ω
        show (sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) * e (i : ℕ) ω
             = (ψ (i : ℕ) ∘ X (i : ℕ)) ω
        simp [ψ, e]
      · ext ω
        show ∏ j ∈ (Finset.range n).erase (i : ℕ), e j ω
             = (∏ j ∈ (Finset.range n).erase (i : ℕ), (ψ j ∘ X j)) ω
        rw [Finset.prod_apply]
        apply Finset.prod_congr rfl
        intro j hj
        have hj_ne : j ≠ (i : ℕ) := Finset.ne_of_mem_erase hj
        simp [ψ, e, hj_ne]
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hmeas_first hmeas_rest hindep_first_rest]
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ e he_indep he_meas]
    rw [Finset.prod_congr rfl (fun j _ => he_lint j)]
    ring
  rw [hLHS, hLHS_factor]
  rw [show (∏ i ∈ S, (ℚₙₜ X ℙ n t) ((fun ω => X i.val ω) ⁻¹' sets i)) =
      ∏ i ∈ S, (ℚₙₜ X ℙ n t) ((X (i : ℕ)) ⁻¹' sets i) from rfl]
  rw [Finset.prod_congr rfl (fun i hi => h_single i hi)]
  have hprod_const_erase : ∀ (i : Finset.range n),
      (∏ j ∈ (Finset.range n).erase (i : ℕ), ENNReal.ofReal M₀) =
        (ENNReal.ofReal M₀) ^ (n - 1) := fun i => by
    rw [Finset.prod_const, Finset.card_erase_of_mem i.2, Finset.card_range]
  have h_image_S : (S.image (Subtype.val : Finset.range n → ℕ)) ⊆ Finset.range n :=
    fun j hj => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj; exact i.2
  have h_g_inS : ∀ (i : Finset.range n) (hi : i ∈ S),
      ∫⁻ ω, φ (i : ℕ) (X (i : ℕ) ω) ∂ℙ =
      ∫⁻ ω, (sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) *
        e (i : ℕ) ω ∂ℙ := fun i hi =>
    lintegral_congr fun ω => by
      change (A' (i : ℕ)).indicator _ _ * _ = _; rw [hA'_inS i hi]
  have h_g_notinS : ∀ j ∈ Finset.range n,
      j ∉ S.image (Subtype.val : Finset.range n → ℕ) →
      ∫⁻ ω, φ j (X j ω) ∂ℙ = ENNReal.ofReal M₀ := fun j _ hj_notmem =>
    hφ_lint_not_inS j fun hj hjS =>
      hj_notmem (Finset.mem_image.mpr ⟨⟨j, Finset.mem_range.mpr hj⟩, hjS, rfl⟩)
  rw [show ∏ j ∈ Finset.range n, ∫⁻ ω, φ j (X j ω) ∂ℙ =
      (∏ j ∈ S.image (Subtype.val : Finset.range n → ℕ), ∫⁻ ω, φ j (X j ω) ∂ℙ) *
        (∏ j ∈ Finset.range n \ S.image (Subtype.val : Finset.range n → ℕ),
          ∫⁻ ω, φ j (X j ω) ∂ℙ) from by rw [← Finset.prod_sdiff h_image_S, mul_comm],
    Finset.prod_congr rfl (fun j hj => h_g_notinS j (Finset.mem_sdiff.mp hj).1
      (Finset.mem_sdiff.mp hj).2), Finset.prod_const,
    show ∏ j ∈ S.image (Subtype.val : Finset.range n → ℕ), ∫⁻ ω, φ j (X j ω) ∂ℙ =
        ∏ i ∈ S, ∫⁻ ω, (sets i).indicator (fun _ => (1 : ℝ≥0∞)) (X (i : ℕ) ω) *
          e (i : ℕ) ω ∂ℙ from by
      rw [Finset.prod_image (fun _ _ _ _ => Subtype.ext)]
      exact Finset.prod_congr rfl h_g_inS,
    show (Finset.range n \ S.image (Subtype.val : Finset.range n → ℕ)).card = n - S.card from by
      rw [Finset.card_sdiff_of_subset h_image_S, Finset.card_range,
        Finset.card_image_of_injective _ fun _ _ hxy => Subtype.ext hxy]]
  simp_rw [hprod_const_erase, Finset.prod_mul_distrib, Finset.prod_const, hMₙ_pow,
    ENNReal.inv_pow]
  have hS_card_le : S.card ≤ n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq <| by
      rw [Finset.card_univ, Fintype.card_coe, Finset.card_range]
  have hcancel : (ENNReal.ofReal M₀)⁻¹ * ENNReal.ofReal M₀ = 1 :=
    ENNReal.inv_mul_cancel hM₀_nn hM₀_top
  have hcancel_pow : ∀ k, (ENNReal.ofReal M₀)⁻¹ ^ k * (ENNReal.ofReal M₀) ^ k = 1 :=
    fun k => by rw [← mul_pow, hcancel, one_pow]
  set s := S.card with hs_def
  set P : ℝ≥0∞ := ∏ i ∈ S, ∫⁻ ω, (sets i).indicator (fun _ => (1 : ℝ≥0∞))
    (X (i : ℕ) ω) * e (i : ℕ) ω ∂ℙ
  conv_lhs => rw [show (ENNReal.ofReal M₀)⁻¹ ^ n =
      (ENNReal.ofReal M₀)⁻¹ ^ s * (ENNReal.ofReal M₀)⁻¹ ^ (n - s) by
    rw [← pow_add, Nat.add_sub_cancel' hS_card_le]]
  rw [mul_assoc, ← mul_assoc ((ENNReal.ofReal M₀)⁻¹ ^ (n - s)), mul_comm _ P, mul_assoc,
    hcancel_pow, mul_one]
  rw [← pow_mul, ← pow_mul]
  have h_expand : n * s = s + (n - 1) * s := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hs0 : s = 0 := Nat.le_zero.mp (hn ▸ hS_card_le)
      simp [hn, hs0]
    · conv_lhs => rw [show n = 1 + (n - 1) from (Nat.add_sub_cancel' hn).symm]
      rw [Nat.add_mul, one_mul]
  rw [h_expand, pow_add, show (ENNReal.ofReal M₀)⁻¹ ^ s * (ENNReal.ofReal M₀)⁻¹ ^ ((n - 1) * s) *
      P * ENNReal.ofReal M₀ ^ ((n - 1) * s) = (ENNReal.ofReal M₀)⁻¹ ^ s * P *
      ((ENNReal.ofReal M₀)⁻¹ ^ ((n - 1) * s) * ENNReal.ofReal M₀ ^ ((n - 1) * s)) by ring,
    hcancel_pow, mul_one]

include h_indep h_ident h_meas h_mgf in
/-- Under `ℚₙₜ`, `Xᵢ` (for `i < n`) are identically distributed. -/
lemma identDistrib_X_X0_ℚₙₜ (t : ℝ) (n : ℕ) {i : ℕ} (hi : i < n) (h0 : 0 < n) :
    IdentDistrib (X i) (X 0) (ℚₙₜ X ℙ n t) (ℚₙₜ X ℙ n t) where
  aemeasurable_fst := (h_meas i).aemeasurable
  aemeasurable_snd := (h_meas 0).aemeasurable
  map_eq := (map_X_ℚₙₜ X h_indep h_ident h_meas h_mgf t n hi).trans
    (map_X_ℚₙₜ X h_indep h_ident h_meas h_mgf t n h0).symm

/-! ### Characteristic function of `Z` under `ℚₙₜ` -/

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- Under `ℚₙₜ`, the characteristic function of `Zₙ` at `s` is `[charFun νₜ ((√n)⁻¹ · s)]ⁿ`. -/
lemma charFun_map_Z_ℚₙₜ (t : ℝ) (n : ℕ) (s : ℝ) :
    charFun ((ℚₙₜ X ℙ n t).map (Z X t n)) s =
      (charFun (νₜ X t) ((Real.sqrt n)⁻¹ * s)) ^ n := by
  haveI : IsProbabilityMeasure (ℚₙₜ X ℙ n t) :=
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  set m := deriv (cgf (X 0) ℙ) t
  set v := iteratedDeriv 2 (cgf (X 0) ℙ) t
  have hv_ne : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr (h_non_deg t)).ne'
  set Y : ℕ → Ω → ℝ := fun k ω => (X k ω - m) / Real.sqrt v with hY_def
  have hY_meas : ∀ k, Measurable (Y k) := fun _ => by fun_prop
  --  `Z = (√n)⁻¹ * ∑ⁿ Yᵢ`.
  have hZ_eq : Z X t n = fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω := by
    ext ω
    simp only [Z, hY_def, partialSum, Finset.sum_apply,
      Real.sqrt_mul (Nat.cast_nonneg _), ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hZ_eq, charFun_map_mul_comp
    (Finset.aemeasurable_fun_sum _ fun k _ => (hY_meas k).aemeasurable)]
  -- Independence of the family `Yᵢ` under `ℚₙₜ`.
  have hY_indep : iIndepFun ((Finset.range n).restrict Y) (ℚₙₜ X ℙ n t) :=
    (iIndepFun_range_ℚₙₜ X h_indep h_ident h_meas h_mgf t n).comp
      (fun _ : Finset.range n => fun x : ℝ => (x - m) / Real.sqrt v) (fun _ => by fun_prop)
  -- Apply the characteristic function factorization on `1..n`.
  rw [hY_indep.charFun_map_fun_finset_sum_eq_prod (fun k _ => (hY_meas k).aemeasurable)]
  -- Every factor is `charFun (νₜ X t) ((√n)⁻¹ * s)`.
  have hY_map : ∀ i ∈ Finset.range n,
      (ℚₙₜ X ℙ n t).map (Y i) = νₜ X t := fun i hi => by
    rw [show Y i = (fun x : ℝ => (x - m) / Real.sqrt v) ∘ X i from rfl,
      ← Measure.map_map (by fun_prop) (h_meas i),
      map_X_ℚₙₜ X h_indep h_ident h_meas h_mgf t n (Finset.mem_range.mp hi)]
    rfl
  rw [Finset.prod_apply, Finset.prod_congr rfl fun i hi => by rw [hY_map i hi],
    Finset.prod_const, Finset.card_range]

include h_meas h_mgf h_non_deg in
/-- `(charFun νₜ ((√n)⁻¹ · s))ⁿ → e^(-s²/2)` as `n → ∞`, the characteristic function of `𝒩(0, 1)` -/
lemma tendsto_charFun_stdTiltedLaw_pow (t : ℝ) (s : ℝ) :
    Tendsto (fun n : ℕ => (charFun (νₜ X t) ((Real.sqrt n)⁻¹ * s)) ^ n)
      atTop (𝓝 (Complex.exp (-s ^ 2 / 2))) := by
  haveI : IsProbabilityMeasure (νₜ X t) :=
    isProbabilityMeasure_stdTiltedLaw X h_meas h_mgf t
  have h0 : (νₜ X t)[id] = 0 := integral_id_stdTiltedLaw X h_meas h_mgf t
  have h1 : (νₜ X t)[(id : ℝ → ℝ) ^ 2] = 1 := by
    simpa using integral_sq_id_stdTiltedLaw X h_meas h_mgf h_non_deg t
  have hmap : (νₜ X t).map id = νₜ X t := Measure.map_id
  have := tendsto_charFun_inv_sqrt_mul_pow (P := νₜ X t) (X := id)
    aemeasurable_id h0 h1 s
  rwa [hmap] at this

/-! ### Central Limit Theorem under the tilted measures -/

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- **CLT for tilted measures (characteristic function form):** under `ℚₙₜ`, the
characteristic function of `Zₙ` converges pointwise to that of `𝒩(0, 1)` (i.e `e^(-s²/2)`). -/
theorem tendsto_charFun_Z_ℚₙₜ (t : ℝ) (s : ℝ) :
    Tendsto (fun n : ℕ => charFun ((ℚₙₜ X ℙ n t).map (Z X t n)) s)
      atTop (𝓝 (Complex.exp (-s ^ 2 / 2))) := by
  refine (tendsto_charFun_stdTiltedLaw_pow X h_meas h_mgf h_non_deg t s).congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    (charFun_map_Z_ℚₙₜ X h_indep h_ident h_meas h_mgf h_non_deg t n s).symm

/-! ### Consequence: concentration of the empirical mean

As a consequence of the CLT, we show that given `Λ'(t) = a`, `{Sₙ/n ∈ [a, a+δ]} → 1/2}`, which is
used in the proof of the lower bound of Cramér's theorem, by demonstrating that this is equivalent
to `{Zₙ ∈ [0, δ · √(n/Λ''(t))]}` and using the convergence of `Zₙ` to `𝒩(0, 1)`. -/

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- For `t` with `Λ'(t) = a` and any `M > 0`, eventually the tilted probability that
`Zₙ ∈ [0, M]` is at least `𝒩(0,1)([0, M]) - ε`. -/
lemma liminf_ℚₙₜ_Z_Icc_ge (t : ℝ) (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ((gaussianReal 0 1) (Set.Icc (0 : ℝ) M)).toReal - ε ≤
      ((ℚₙₜ X ℙ n t).map (Z X t n) (Set.Icc (0 : ℝ) M)).toReal := by
  haveI : ∀ n, IsProbabilityMeasure (ℚₙₜ X ℙ n t) := fun n =>
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  haveI : ∀ n, IsProbabilityMeasure ((ℚₙₜ X ℙ n t).map (Z X t n)) := fun n =>
    Measure.isProbabilityMeasure_map
      (((measurable_partialSum X h_meas n).sub_const _).div_const _).aemeasurable
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  set μ_n : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(ℚₙₜ X ℙ n t).map (Z X t n), inferInstance⟩
  set μ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  -- apply Lévy's convergence theorem
  have h_weak : Tendsto μ_n atTop (𝓝 μ) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun s => by
      have h_gauss : charFun (gaussianReal 0 1 : Measure ℝ) s =
          Complex.exp (-s ^ 2 / 2) := by rw [charFun_gaussianReal]; push_cast; ring_nf
      simpa [μ_n, μ, h_gauss] using
        tendsto_charFun_Z_ℚₙₜ X h_indep h_ident h_meas h_mgf h_non_deg t s
  have h_fr : (μ : Measure ℝ) (frontier (Set.Icc (0 : ℝ) M)) = 0 := by
    rw [show (μ : Measure ℝ) = gaussianReal 0 1 from rfl, frontier_Icc hM]
    exact Set.Finite.measure_zero (by simp) _
  have h_lt : ((μ : Measure ℝ) (Set.Icc (0 : ℝ) M)).toReal - ε <
      ((μ : Measure ℝ) (Set.Icc (0 : ℝ) M)).toReal := by linarith
  simpa using ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      h_weak h_fr)).eventually_const_le h_lt

/-- The standard Gaussian has mass `1/2` on `(-∞, 0]`. -/
private lemma gaussianReal_Iic_zero_eq_half :
    (gaussianReal 0 1) (Set.Iic (0 : ℝ)) = 1 / 2 := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  set N := gaussianReal 0 1
  -- By symmetry, `N((-∞, 0]) = N([0, ∞))`.
  have hIoi_eq_Iic : N (Set.Ioi (0 : ℝ)) = N (Set.Iic 0) := by
    have hsym : N.map (fun x : ℝ => -x) = N := by
      simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    refine (measure_congr Ioi_ae_eq_Ici).trans ?_
    conv_lhs => rw [← hsym, Measure.map_apply (by fun_prop) measurableSet_Ici]
    congr 1; ext x; simp
  -- `N((-∞, 0]) = 1/2` as `N((-∞, 0]) + N([0, ∞)) = N(ℝ) = 1`.
  have hcompl : N (Set.Iic (0 : ℝ)) + N (Set.Iic 0) = 1 := by
    have := measure_add_measure_compl (μ := N) (s := Set.Iic (0 : ℝ)) measurableSet_Iic
    rwa [Set.compl_Iic, measure_univ, hIoi_eq_Iic] at this
  rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), two_mul]; exact hcompl

/-- The standard Gaussian's mass on `[0, M]` tends to `1/2` as `M → ∞`. -/
lemma tendsto_gaussianReal_Icc_toReal_half :
    Tendsto (fun M : ℝ => ((gaussianReal 0 1) (Set.Icc (0 : ℝ) M)).toReal)
      atTop (𝓝 (1 / 2)) := by
  haveI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal one_ne_zero
  set N := gaussianReal 0 1
  have hIic0 : N (Set.Iic (0 : ℝ)) = 1 / 2 := gaussianReal_Iic_zero_eq_half
  have hIio_eq_Iic : N (Set.Iio (0 : ℝ)) = N (Set.Iic 0) := measure_congr Iio_ae_eq_Iic
  -- For `M ≥ 0`, `N([0, M]) = N((-∞, M]) - 1/2`.
  have hIcc_eq : ∀ᶠ M : ℝ in atTop,
      N (Set.Iic M) - (1 / 2 : ℝ≥0∞) = N (Set.Icc (0 : ℝ) M) :=
    (Filter.eventually_ge_atTop 0).mono fun M hM => by
      have hunion : N (Set.Iio 0) + N (Set.Icc 0 M) = N (Set.Iic M) := by
        rw [← Set.Iio_union_Icc_eq_Iic hM]
        exact (measure_union ((Set.Iio_disjoint_Ici le_rfl).mono_right
          Set.Icc_subset_Ici_self) measurableSet_Icc).symm
      rw [← hIic0, ← hIio_eq_Iic]
      exact (ENNReal.eq_sub_of_add_eq (measure_ne_top N _)
        ((add_comm (N (Set.Iio 0)) _) ▸ hunion)).symm
  -- `N([0, M]) → 1/2` in ENNReal
  have hIcc_tendsto : Tendsto (fun M : ℝ => N (Set.Icc (0 : ℝ) M)) atTop (𝓝 (1 / 2)) := by
    have hIic_tendsto : Tendsto (fun M : ℝ => N (Set.Iic M)) atTop (𝓝 1) := by
      simpa using tendsto_measure_Iic_atTop N
    have key := (ENNReal.Tendsto.sub hIic_tendsto
      (tendsto_const_nhds (x := (1 / 2 : ℝ≥0∞))) (Or.inl ENNReal.one_ne_top))
    rw [show (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 from by norm_num] at key
    exact key.congr' hIcc_eq
  rw [show (1 : ℝ) / 2 = ((1 : ℝ≥0∞) / 2).toReal from by norm_num]
  exact (ENNReal.tendsto_toReal (by norm_num)).comp hIcc_tendsto

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- **Corrollary of Tilted CLT:** Given `Λ'(t) = a`, for all `δ > 0` and `ε > 0`,
 `1/2 - ε ≤ ℚₙₜ(Sₙ/n ∈ [a, a+δ])` holds for all sufficiently large `n`. -/
lemma eventually_ℚₙₜ_empiricalMean_mem_Icc_ge (t a δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε)
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    ∀ᶠ n in atTop,
      (1 / 2 - ε : ℝ) ≤ ((ℚₙₜ X ℙ n t)
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal := by
  -- Let `v := Λ''(t)`
  set v := iteratedDeriv 2 (cgf (X 0) ℙ) t with hv_def
  have hv_pos : 0 < v := h_non_deg t
  haveI hℚ_prob : ∀ n, IsProbabilityMeasure (ℚₙₜ X ℙ n t) := fun n =>
    isProbabilityMeasure_tilted_partialSum X h_indep h_ident h_meas h_mgf t n
  have hZ_meas : ∀ n, Measurable (Z X t n) := fun n => by
    unfold Z
    exact ((measurable_partialSum X h_meas n).sub_const _).div_const _
  -- Pick `M₀ ≥ 0` with `1/2 - ε/2 < N([0, M₀])`.
  obtain ⟨M₀, hM₀_lb, hM₀_nonneg⟩ :=
    ((tendsto_gaussianReal_Icc_toReal_half.eventually_const_lt
        (show (1/2 - ε/2 : ℝ) < 1/2 by linarith)).and (Filter.eventually_ge_atTop 0)).exists
  -- Apply `liminf_ℚₙₜ_Z_Icc_ge` with `M₀` and `ε/2`.
  have h_liminf := liminf_ℚₙₜ_Z_Icc_ge X h_indep h_ident h_meas h_mgf h_non_deg
    t M₀ hM₀_nonneg (ε/2) (by linarith)
  -- `δ · √(n/v) → ∞` as `n → ∞`.
  have h_Mn_ge : ∀ᶠ n : ℕ in atTop, M₀ ≤ δ * Real.sqrt ((n : ℝ) / v) :=
    ((Real.tendsto_sqrt_atTop.comp
      (Filter.Tendsto.atTop_div_const hv_pos tendsto_natCast_atTop_atTop)).const_mul_atTop
        hδ).eventually_ge_atTop M₀
  filter_upwards [h_liminf, h_Mn_ge, Filter.eventually_gt_atTop 0]
    with n h_lim hMn_ge hn_pos
  -- `M_n = δ * √(n / v) ≥ M₀ ≥ 0`.
  set M_n := δ * Real.sqrt ((n : ℝ) / v)
  haveI : IsProbabilityMeasure ((ℚₙₜ X ℙ n t).map (Z X t n)) :=
    Measure.isProbabilityMeasure_map (hZ_meas n).aemeasurable
  -- Rewrite the preimage of `Z([0, Mₙ])` as `{ω | Sₙ(ω)/n ∈ [a, a+δ]}`
  have h_set_eq :
      (Z X t n) ⁻¹' Set.Icc (0 : ℝ) M_n =
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [empiricalMean_mem_Icc_iff_Z_mem_Icc X t a δ n hn_pos (h_non_deg t) ht_deriv ω]
  -- `[0, M₀] ⊆ [0, M_n]` implies `Zₙ([0, M₀]) ≤ Zₙ([0, M_n])` under `ℚₙₜ`.
  have h_toReal_mono :
      (((ℚₙₜ X ℙ n t).map (Z X t n)) (Set.Icc (0 : ℝ) M₀)).toReal ≤
        (((ℚₙₜ X ℙ n t).map (Z X t n)) (Set.Icc (0 : ℝ) M_n)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.Icc_subset_Icc le_rfl hMn_ge))
  -- Combine: `1/2 - ε ≤ N([0, M₀]) - ε/2 ≤ ℚₙₜ.map(Zₙ)([0, Mₙ]) = ℚₙₜ(Sₙ / n ∈ [a, a+δ])`.
  rw [← h_set_eq, ← Measure.map_apply (hZ_meas n) measurableSet_Icc]
  linarith [h_lim, h_toReal_mono]

end ProbabilityTheory
