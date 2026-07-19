/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramer.Basic
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.CharacteristicFunction

import Mathlib.MeasureTheory.Constructions.Pi.Tilted
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramér's theorem: CLT over tilted measures

This file provides a proof of the Central Limit Theorem over a sequence of tilted measures,
used in the proof of the lower bound of Cramér's theorem.

Under the assumptions of Cramér's theorem, for `t` with `Λ'(t) = a` the family of tilted measures
`tiltedMeasure := μ.tilted (t · Sₙ)` satisfies a CLT statement:
The normalized partial sum `Zₙ := (Sₙ - n Λ'(t))/√(n Λ''(t))` converges in distribution
to `𝒩(0,1)` under `tiltedMeasure` as `n → ∞`.
An immediate corollary is a concentration statement used in `LowerBound.lean`.

## Main definitions

* `Cramer.tiltedLaw X μ t`: the pushforward measure of `μ` by `X₀`, tilted by `t · x`,
* `Cramer.stdTiltedLaw X μ t`: the pushforward of `Cramer.tiltedLaw X μ t` by a linear map that
  standardizes it to zero mean and unit variance.
* `Cramer.stdPartialSum X μ t n`: the standardized partial sum `(Sₙ - n Λ'(t)) / √(n Λ''(t))`.

## Main results

* `Cramer.tendsto_charFun_stdPartialSum`: under `tiltedMeasure`, the characteristic function of
  `Zₙ` converges pointwise to that of `𝒩(0,1)`.
* `Cramer.eventually_tiltedMeasure_sum_div_mem_Icc_ge`: the concentration statement for the
  lower bound proof: For every `0 < δ`, `0 < ε` and `t` with `Λ'(t) = a`, eventually
  `1/2 - ε ≤ tiltedMeasure(Sₙ/n ∈ [a, a+δ])`.

-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The law of `X 0` under `μ`, tilted by `t · x`. -/
noncomputable def Cramer.tiltedLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (t : ℝ) : Measure ℝ :=
  (μ.map (X 0)).tilted (fun x => t * x)

/-- The push-forward of `tiltedLaw` by the map `x ↦ (x - Λ'(t)) / √Λ''(t)`,
  so that it has zero mean and unit variance. -/
noncomputable def Cramer.stdTiltedLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (t : ℝ) : Measure ℝ :=
  (tiltedLaw X μ t).map
    (fun x => (x - deriv (cgf (X 0) μ) t) / Real.sqrt (iteratedDeriv 2 (cgf (X 0) μ) t))

/-- The standardized partial sum under `tiltedMeasure`: `Z = (Sₙ - n Λ'(t)) / √(n Λ''(t))`. -/
noncomputable def Cramer.stdPartialSum (X : ℕ → Ω → ℝ) (μ : Measure Ω) (t : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ((∑ i ∈ Finset.range n, X i ω) - n * deriv (cgf (X 0) μ) t) /
    Real.sqrt (n * iteratedDeriv 2 (cgf (X 0) μ) t)

variable {X : ℕ → Ω → ℝ}

/- Assumptions for Cramér's theorem -/
variable (h_indep : iIndepFun X μ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
variable (h_non_deg : ∀ t : ℝ, 0 < iteratedDeriv 2 (cgf (X 0) μ) t)

include h_meas in
/-- The MGF of the identity under `tiltedLaw` at `u` equals `mgf(X₀)(t + u)/mgf(X₀)(t)`. -/
lemma Cramer.mgf_id_tiltedLaw (t u : ℝ) :
    mgf id (tiltedLaw X μ t) u = mgf (X 0) μ (t + u) / mgf (X 0) μ t := by
  have hX0 : AEMeasurable (X 0) μ := (h_meas 0).aemeasurable
  simp only [mgf, tiltedLaw, id]
  rw [integral_exp_tilted (fun x => t * x) (fun x => u * x),
    integral_map hX0 (by fun_prop), integral_map hX0 (by fun_prop)]
  simp [add_mul]

include h_meas h_mgf in
private lemma Cramer.t_mem_interior_integrableExpSet_id (t : ℝ) :
    t ∈ interior (integrableExpSet id (μ.map (X 0))) := by
  have h_univ : integrableExpSet id (μ.map (X 0)) = Set.univ := by
    ext s
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true, id]
    exact (integrable_map_measure (by fun_prop) (h_meas 0).aemeasurable).mpr (h_mgf s)
  rw [h_univ, interior_univ]
  exact Set.mem_univ t

private lemma t_mul_eq_mul_id (t : ℝ) : (fun x : ℝ => t * x) = (t * id ·) := rfl

include h_meas h_mgf in
/-- The mean of `tiltedLaw` is `Λ'(t)`. -/
lemma Cramer.integral_id_tiltedLaw (t : ℝ) :
    ∫ x, x ∂(tiltedLaw X μ t) = deriv (cgf (X 0) μ) t := by
  simp only [tiltedLaw]
  rw [t_mul_eq_mul_id, ← cgf_id_map (h_meas 0).aemeasurable]
  exact integral_tilted_mul_self (t_mem_interior_integrableExpSet_id h_meas h_mgf t)

include h_meas h_mgf in
/-- The variance of `tiltedLaw` is `Λ''(t)`. -/
lemma Cramer.variance_id_tiltedLaw (t : ℝ) :
    Var[id; tiltedLaw X μ t] = iteratedDeriv 2 (cgf (X 0) μ) t := by
  simp only [tiltedLaw]
  rw [t_mul_eq_mul_id, ← cgf_id_map (h_meas 0).aemeasurable]
  exact variance_tilted_mul (t_mem_interior_integrableExpSet_id h_meas h_mgf t)

include h_meas h_mgf in
/-- The identity is in `L²` under `tiltedLaw`. -/
lemma Cramer.memLp_id_tiltedLaw (t : ℝ) : MemLp (id : ℝ → ℝ) 2 (tiltedLaw X μ t) := by
  simp only [tiltedLaw]
  rw [t_mul_eq_mul_id]
  exact memLp_tilted_mul (t_mem_interior_integrableExpSet_id h_meas h_mgf t) 2

/-! ### Algebraic Identities -/

/-- Algebraic identity: for `t` with `Λ'(t) = a` and `0 < n`, the event
`{Sₙ/n ∈ [a, a+δ]}` is exactly `{Zₙ ∈ [0, δ · √(n / Λ''(t))]}`. -/
lemma Cramer.sum_div_mem_Icc_iff_stdPartialSum_mem_Icc (t a δ : ℝ) (n : ℕ) (hn : 0 < n)
    (h_non_deg_t : 0 < iteratedDeriv 2 (cgf (X 0) μ) t)
    (ht_deriv : deriv (cgf (X 0) μ) t = a) (ω : Ω) :
    (∑ i ∈ Finset.range n, X i ω) / n ∈ Set.Icc a (a + δ) ↔
      stdPartialSum X μ t n ω ∈ Set.Icc (0 : ℝ)
        (δ * Real.sqrt (n / iteratedDeriv 2 (cgf (X 0) μ) t)) := by
  rw [Set.mem_Icc, Set.mem_Icc, stdPartialSum, ht_deriv]
  set v := iteratedDeriv 2 (cgf (X 0) μ) t
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnv : (0 : ℝ) < Real.sqrt (n * v) := Real.sqrt_pos.mpr (by positivity)
  rw [le_div_iff₀ hn', div_le_iff₀ hn', le_div_iff₀ hnv, div_le_iff₀ hnv]
  have key : Real.sqrt (n / v) * Real.sqrt (n * v) = n := by
    rw [← Real.sqrt_mul (by positivity), show (n / v * (n * v) : ℝ) = n ^ 2 by field_simp,
      Real.sqrt_sq hn'.le]
  refine ⟨fun ⟨h1, h2⟩ => ⟨by linarith, ?_⟩,
    fun ⟨h1, h2⟩ => ⟨by linarith, ?_⟩⟩ <;> nlinarith [key]

include h_meas h_mgf h_non_deg in
/-- The second moment of `stdTiltedLaw` is `1`. -/
lemma Cramer.integral_sq_id_stdTiltedLaw (t : ℝ) :
    ∫ x, x ^ 2 ∂(stdTiltedLaw X μ t) = 1 := by
  have hv := h_non_deg t
  set m := deriv (cgf (X 0) μ) t
  set v := iteratedDeriv 2 (cgf (X 0) μ) t
  simp only [stdTiltedLaw]
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hμ_mean : ∫ x, x ∂tiltedLaw X μ t = m :=
    integral_id_tiltedLaw h_meas h_mgf t
  have hvar : Var[id; tiltedLaw X μ t] = v :=
    variance_id_tiltedLaw h_meas h_mgf t
  have hint_sq : ∫ x, (x - m) ^ 2 ∂tiltedLaw X μ t = v := by
    rw [← hvar, variance_eq_integral aemeasurable_id]
    congr 1; ext x; simp [hμ_mean]
  rw [show (fun x : ℝ => ((x - m) / Real.sqrt v) ^ 2) = fun x => (x - m) ^ 2 / v from
    funext fun x => by rw [div_pow, Real.sq_sqrt hv.le], integral_div, hint_sq, div_self hv.ne']

/-! ### Lemmas requiring `μ` to be a probability measure -/

variable [IsProbabilityMeasure μ]

include h_meas h_mgf in
/-- `tiltedLaw` is a probability measure. -/
lemma Cramer.isProbabilityMeasure_tiltedLaw (t : ℝ) :
    IsProbabilityMeasure (tiltedLaw X μ t) := by
  haveI : IsProbabilityMeasure (μ.map (X 0)) :=
    Measure.isProbabilityMeasure_map (h_meas 0).aemeasurable
  exact isProbabilityMeasure_tilted
    ((integrable_map_measure (by fun_prop) (h_meas 0).aemeasurable).mpr (h_mgf t))

/-! ### Properties of `stdTiltedLaw` -/

include h_meas h_mgf in
/-- `stdTiltedLaw` is a probability measure. -/
lemma Cramer.isProbabilityMeasure_stdTiltedLaw (t : ℝ) :
    IsProbabilityMeasure (stdTiltedLaw X μ t) :=
  haveI := isProbabilityMeasure_tiltedLaw h_meas h_mgf t
  Measure.isProbabilityMeasure_map (by fun_prop)

include h_meas h_mgf in
/-- The mean of `stdTiltedLaw` is `0`. -/
lemma Cramer.integral_id_stdTiltedLaw (t : ℝ) :
    ∫ x, x ∂(stdTiltedLaw X μ t) = 0 := by
  simp only [stdTiltedLaw]
  haveI : IsProbabilityMeasure (tiltedLaw X μ t) :=
    isProbabilityMeasure_tiltedLaw h_meas h_mgf t
  have hid : Integrable (fun x : ℝ => x) (tiltedLaw X μ t) :=
    (memLp_id_tiltedLaw h_meas h_mgf t).integrable (by norm_num)
  rw [integral_map (by fun_prop) (by fun_prop), integral_div,
    integral_sub hid (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_id_tiltedLaw h_meas h_mgf t, sub_self, zero_div]

include h_meas h_mgf in
/-- The identity is in `L²` under `stdTiltedLaw`. -/
lemma Cramer.memLp_id_stdTiltedLaw (t : ℝ) :
    MemLp (id : ℝ → ℝ) 2 (stdTiltedLaw X μ t) := by
  simp only [stdTiltedLaw]
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  haveI : IsProbabilityMeasure (tiltedLaw X μ t) :=
    isProbabilityMeasure_tiltedLaw h_meas h_mgf t
  have h_sub : MemLp (fun x : ℝ => x - deriv (cgf (X 0) μ) t) 2 (tiltedLaw X μ t) :=
    (memLp_id_tiltedLaw h_meas h_mgf t).sub (memLp_const _)
  have h_div : MemLp (fun x : ℝ => (x - deriv (cgf (X 0) μ) t) *
      (Real.sqrt (iteratedDeriv 2 (cgf (X 0) μ) t))⁻¹) 2 (tiltedLaw X μ t) :=
    h_sub.mul_const _
  exact h_div.congr_norm (by fun_prop) (Eventually.of_forall fun x => by
    simp [Function.comp, div_eq_mul_inv])

/-! ### Factorization of `X₀, …, Xₙ₋₁` under `tiltedMeasure`

Under the tilted measure `tiltedMeasure = μ.tilted(t · Sₙ)`, the coordinates
`X₀, …, Xₙ₋₁` are still independent and each has law `tiltedLaw`.
These are corollaries of general facts about exponential tilting: tilting commutes with
pushforward along the tilting function (`MeasureTheory.map_tilted_comp`), and tilting a finite
product measure by a sum of coordinate functions yields the product of the tilted factors
(`MeasureTheory.tilted_pi`). -/

include h_indep h_ident h_meas in
/-- Under `tiltedMeasure`, the joint law of `(Xᵢ)_{i ∈ range n}` is the product of `n` copies
of `tiltedLaw`. -/
private lemma Cramer.map_range_tiltedMeasure (t : ℝ) (n : ℕ) :
    (tiltedMeasure X μ n t).map (fun ω (i : Finset.range n) => X i.val ω) =
      Measure.pi (fun _ : Finset.range n => tiltedLaw X μ t) := by
  have h_fun : (fun ω => t * ∑ i ∈ Finset.range n, X i ω) =
      (fun v : Finset.range n → ℝ => ∑ i, t * v i) ∘
        (fun ω (i : Finset.range n) => X i.val ω) := by
    funext ω
    simp only [Function.comp_apply, Finset.mul_sum, Finset.univ_eq_attach]
    exact (Finset.sum_attach (Finset.range n) fun j => t * X j ω).symm
  have h_tilt : tiltedMeasure X μ n t =
      μ.tilted ((fun v : Finset.range n → ℝ => ∑ i, t * v i) ∘
        (fun ω (i : Finset.range n) => X i.val ω)) := congrArg μ.tilted h_fun
  have h_pi : μ.map (fun ω (i : Finset.range n) => X i.val ω) =
      Measure.pi (fun i : Finset.range n => μ.map (X i.val)) :=
    (h_indep.precomp Subtype.val_injective).map_fun_eq_pi_map fun i => (h_meas i.val).aemeasurable
  have hT : AEMeasurable (fun ω (i : Finset.range n) => X i.val ω) μ :=
    Measurable.aemeasurable (measurable_pi_lambda _ fun i => h_meas i.val)
  have hg : AEMeasurable (fun v : Finset.range n → ℝ => ∑ i, t * v i)
      (μ.map (fun ω (i : Finset.range n) => X i.val ω)) :=
    Measurable.aemeasurable (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i : Measurable fun v : Finset.range n → ℝ => v i).const_mul t)
  rw [h_tilt, map_tilted_comp hT hg, h_pi,
    show (fun i : Finset.range n => μ.map (X i.val)) = fun _ => μ.map (X 0) from
      funext fun i => (h_ident i.val).map_eq]
  exact tilted_pi _ fun _ x => t * x

include h_indep h_ident h_meas h_mgf in
/-- Under `tiltedMeasure`, each `Xᵢ` (for `i < n`) has the same law `tiltedLaw`. -/
lemma Cramer.map_X_tiltedMeasure (t : ℝ) (n : ℕ) {i : ℕ} (hi : i < n) :
    (tiltedMeasure X μ n t).map (X i) = tiltedLaw X μ t := by
  haveI := isProbabilityMeasure_tiltedLaw h_meas h_mgf t
  calc (tiltedMeasure X μ n t).map (X i)
      = ((tiltedMeasure X μ n t).map (fun ω (j : Finset.range n) => X j.val ω)).map
          (Function.eval ⟨i, Finset.mem_range.mpr hi⟩) :=
        (Measure.map_map (g := Function.eval (⟨i, Finset.mem_range.mpr hi⟩ : Finset.range n))
          (f := fun ω (j : Finset.range n) => X j.val ω) (measurable_pi_apply _)
          (measurable_pi_lambda _ fun j => h_meas j.val)).symm
    _ = (Measure.pi fun _ : Finset.range n => tiltedLaw X μ t).map
          (Function.eval ⟨i, Finset.mem_range.mpr hi⟩) := by
        rw [map_range_tiltedMeasure h_indep h_ident h_meas t n]
    _ = tiltedLaw X μ t := (measurePreserving_eval _ _).map_eq

include h_indep h_ident h_meas h_mgf in
/-- Under `tiltedMeasure`, `Xᵢ` (for `i < n`) are independent. -/
lemma Cramer.iIndepFun_range_tiltedMeasure (t : ℝ) (n : ℕ) :
    iIndepFun (fun i : Finset.range n => X i.val) (tiltedMeasure X μ n t) := by
  haveI := isProbabilityMeasure_tiltedMeasure h_indep h_ident h_meas h_mgf t n
  rw [iIndepFun_iff_map_fun_eq_pi_map (f := fun i : Finset.range n => X i.val)
      fun i => (h_meas i.val).aemeasurable,
    map_range_tiltedMeasure h_indep h_ident h_meas t n]
  exact congrArg Measure.pi <| funext fun i =>
    (map_X_tiltedMeasure h_indep h_ident h_meas h_mgf t n (Finset.mem_range.mp i.2)).symm

/-! ### Characteristic function of `stdPartialSum` under `tiltedMeasure` -/

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- Under `tiltedMeasure`, the characteristic function of `Zₙ` at `s` is
`[charFun stdTiltedLaw ((√n)⁻¹ · s)]ⁿ`. -/
lemma Cramer.charFun_map_stdPartialSum (t : ℝ) (n : ℕ) (s : ℝ) :
    charFun ((tiltedMeasure X μ n t).map (stdPartialSum X μ t n)) s =
      (charFun (stdTiltedLaw X μ t) ((Real.sqrt n)⁻¹ * s)) ^ n := by
  haveI : IsProbabilityMeasure (tiltedMeasure X μ n t) :=
    isProbabilityMeasure_tiltedMeasure h_indep h_ident h_meas h_mgf t n
  set m := deriv (cgf (X 0) μ) t
  set v := iteratedDeriv 2 (cgf (X 0) μ) t
  have hv_ne : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr (h_non_deg t)).ne'
  set Y : ℕ → Ω → ℝ := fun k ω => (X k ω - m) / Real.sqrt v with hY_def
  have hY_meas : ∀ k, Measurable (Y k) := fun _ => by fun_prop
  --  `Z = (√n)⁻¹ * ∑ⁿ Yᵢ`.
  have hZ_eq : stdPartialSum X μ t n =
      fun ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, Y k ω := by
    ext ω
    simp only [stdPartialSum, hY_def,
      Real.sqrt_mul (Nat.cast_nonneg _), ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hZ_eq, charFun_map_mul_comp
    (Finset.aemeasurable_fun_sum _ fun k _ => (hY_meas k).aemeasurable)]
  -- Independence of the family `Yᵢ` under `tiltedMeasure`.
  have hY_indep : iIndepFun ((Finset.range n).restrict Y) (tiltedMeasure X μ n t) :=
    (iIndepFun_range_tiltedMeasure h_indep h_ident h_meas h_mgf t n).comp
      (fun _ : Finset.range n => fun x : ℝ => (x - m) / Real.sqrt v) (fun _ => by fun_prop)
  -- Apply the characteristic function factorization on `1..n`.
  rw [hY_indep.charFun_map_fun_finsetSum_eq_prod (fun k _ => (hY_meas k).aemeasurable)]
  -- Every factor is `charFun (stdTiltedLaw X μ t) ((√n)⁻¹ * s)`.
  have hY_map : ∀ i ∈ Finset.range n,
      (tiltedMeasure X μ n t).map (Y i) = stdTiltedLaw X μ t := fun i hi => by
    rw [show Y i = (fun x : ℝ => (x - m) / Real.sqrt v) ∘ X i from rfl,
      ← Measure.map_map (by fun_prop) (h_meas i),
      map_X_tiltedMeasure h_indep h_ident h_meas h_mgf t n (Finset.mem_range.mp hi)]
    rfl
  rw [Finset.prod_apply, Finset.prod_congr rfl fun i hi => by rw [hY_map i hi],
    Finset.prod_const, Finset.card_range]

include h_meas h_mgf h_non_deg in
/-- `(charFun stdTiltedLaw ((√n)⁻¹ · s))ⁿ → e^(-s²/2)` as `n → ∞`,
the characteristic function of `𝒩(0, 1)` -/
lemma Cramer.tendsto_charFun_stdTiltedLaw_pow (t : ℝ) (s : ℝ) :
    Tendsto (fun n : ℕ => (charFun (stdTiltedLaw X μ t) ((Real.sqrt n)⁻¹ * s)) ^ n)
      atTop (𝓝 (Complex.exp (-s ^ 2 / 2))) := by
  haveI : IsProbabilityMeasure (stdTiltedLaw X μ t) :=
    isProbabilityMeasure_stdTiltedLaw h_meas h_mgf t
  have h0 : (stdTiltedLaw X μ t)[id] = 0 := integral_id_stdTiltedLaw h_meas h_mgf t
  have h1 : (stdTiltedLaw X μ t)[(id : ℝ → ℝ) ^ 2] = 1 := by
    simpa using integral_sq_id_stdTiltedLaw h_meas h_mgf h_non_deg t
  have hmap : (stdTiltedLaw X μ t).map id = stdTiltedLaw X μ t := Measure.map_id
  have := tendsto_charFun_inv_sqrt_mul_pow (P := stdTiltedLaw X μ t) (X := id)
    aemeasurable_id h0 h1 s
  rwa [hmap] at this

/-! ### Central Limit Theorem under the tilted measures -/

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- **CLT for tilted measures (characteristic function form):** under `tiltedMeasure`, the
characteristic function of `Zₙ` converges pointwise to that of `𝒩(0, 1)` (i.e `e^(-s²/2)`). -/
theorem Cramer.tendsto_charFun_stdPartialSum (t : ℝ) (s : ℝ) :
    Tendsto (fun n : ℕ => charFun ((tiltedMeasure X μ n t).map (stdPartialSum X μ t n)) s)
      atTop (𝓝 (Complex.exp (-s ^ 2 / 2))) := by
  refine (tendsto_charFun_stdTiltedLaw_pow h_meas h_mgf h_non_deg t s).congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    (charFun_map_stdPartialSum h_indep h_ident h_meas h_mgf h_non_deg t n s).symm

/-! ### Consequence: concentration of the empirical mean

As a consequence of the CLT, we show that given `Λ'(t) = a`, `{Sₙ/n ∈ [a, a+δ]} → 1/2}`,
which is used in the proof of the lower bound of Cramér's theorem, by demonstrating that this
is equivalent to `{Zₙ ∈ [0, δ · √(n/Λ''(t))]}` and using the convergence of `Zₙ`
to `𝒩(0, 1)`. -/

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- For `t` with `Λ'(t) = a` and any `0 ≤ M`, eventually the tilted probability that
`Zₙ ∈ [0, M]` is at least `𝒩(0,1)([0, M]) - ε`. -/
lemma Cramer.eventually_measure_stdPartialSum_mem_Icc_ge (t : ℝ) (M : ℝ) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ((gaussianReal 0 1) (Set.Icc (0 : ℝ) M)).toReal - ε ≤
      ((tiltedMeasure X μ n t).map (stdPartialSum X μ t n) (Set.Icc (0 : ℝ) M)).toReal := by
  haveI : ∀ n, IsProbabilityMeasure (tiltedMeasure X μ n t) := fun n =>
    isProbabilityMeasure_tiltedMeasure h_indep h_ident h_meas h_mgf t n
  haveI : ∀ n, IsProbabilityMeasure ((tiltedMeasure X μ n t).map (stdPartialSum X μ t n)) :=
    fun n => Measure.isProbabilityMeasure_map
      (((measurable_sum_range h_meas n).sub_const _).div_const _).aemeasurable
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  set ν_n : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(tiltedMeasure X μ n t).map (stdPartialSum X μ t n), inferInstance⟩
  set ν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  -- apply Lévy's convergence theorem
  have h_weak : Tendsto ν_n atTop (𝓝 ν) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun s => by
      have h_gauss : charFun (gaussianReal 0 1 : Measure ℝ) s =
          Complex.exp (-s ^ 2 / 2) := by rw [charFun_gaussianReal]; push_cast; ring_nf
      simpa [ν_n, ν, h_gauss] using
        tendsto_charFun_stdPartialSum h_indep h_ident h_meas h_mgf h_non_deg t s
  have h_fr : (ν : Measure ℝ) (frontier (Set.Icc (0 : ℝ) M)) = 0 := by
    rw [show (ν : Measure ℝ) = gaussianReal 0 1 from rfl, frontier_Icc hM]
    exact Set.Finite.measure_zero (by simp) _
  have h_lt : ((ν : Measure ℝ) (Set.Icc (0 : ℝ) M)).toReal - ε <
      ((ν : Measure ℝ) (Set.Icc (0 : ℝ) M)).toReal := by linarith
  simpa [ν_n, ν] using ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      h_weak h_fr)).eventually_const_le h_lt

include h_indep h_ident h_meas h_mgf h_non_deg in
/-- **Corollary of Tilted CLT:** Given `Λ'(t) = a`, for all `0 < δ` and `0 < ε`,
 `1/2 - ε ≤ tiltedMeasure(Sₙ/n ∈ [a, a+δ])` holds for all sufficiently large `n`. -/
lemma Cramer.eventually_tiltedMeasure_sum_div_mem_Icc_ge (t a δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (ht_deriv : deriv (cgf (X 0) μ) t = a) :
    ∀ᶠ n in atTop,
      (1 / 2 - ε : ℝ) ≤ ((tiltedMeasure X μ n t)
        {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ Set.Icc a (a + δ)}).toReal := by
  -- Let `v := Λ''(t)`
  set v := iteratedDeriv 2 (cgf (X 0) μ) t with hv_def
  have hv_pos : 0 < v := h_non_deg t
  haveI hℚ_prob : ∀ n, IsProbabilityMeasure (tiltedMeasure X μ n t) := fun n =>
    isProbabilityMeasure_tiltedMeasure h_indep h_ident h_meas h_mgf t n
  have hZ_meas : ∀ n, Measurable (stdPartialSum X μ t n) := fun n => by
    unfold stdPartialSum
    exact ((measurable_sum_range h_meas n).sub_const _).div_const _
  -- Pick `0 ≤ M₀` with `1/2 - ε/2 < N([0, M₀])`.
  have h_gauss_half : Tendsto (fun M : ℝ => ((gaussianReal 0 1) (Set.Icc (0 : ℝ) M)).toReal)
      atTop (𝓝 (1 / 2)) := by
    rw [show (1 : ℝ) / 2 = ((1 : ℝ≥0∞) / 2).toReal from by norm_num]
    exact (ENNReal.tendsto_toReal (by norm_num)).comp
      (tendsto_gaussianReal_Icc_mean_atTop one_ne_zero)
  obtain ⟨M₀, hM₀_lb, hM₀_nonneg⟩ :=
    ((h_gauss_half.eventually_const_lt
        (show (1/2 - ε/2 : ℝ) < 1/2 by linarith)).and (Filter.eventually_ge_atTop 0)).exists
  -- Apply `eventually_measure_stdPartialSum_mem_Icc_ge` with `M₀` and `ε/2`.
  have h_liminf := eventually_measure_stdPartialSum_mem_Icc_ge h_indep h_ident h_meas h_mgf
    h_non_deg t M₀ hM₀_nonneg (ε/2) (by linarith)
  -- `δ · √(n/v) → ∞` as `n → ∞`.
  have h_Mn_ge : ∀ᶠ n : ℕ in atTop, M₀ ≤ δ * Real.sqrt ((n : ℝ) / v) :=
    ((Real.tendsto_sqrt_atTop.comp
      (Filter.Tendsto.atTop_div_const hv_pos tendsto_natCast_atTop_atTop)).const_mul_atTop
        hδ).eventually_ge_atTop M₀
  filter_upwards [h_liminf, h_Mn_ge, Filter.eventually_gt_atTop 0]
    with n h_lim hMn_ge hn_pos
  -- `0 ≤ M₀ ≤ M_n = δ * √(n / v)`.
  set M_n := δ * Real.sqrt ((n : ℝ) / v)
  haveI : IsProbabilityMeasure ((tiltedMeasure X μ n t).map (stdPartialSum X μ t n)) :=
    Measure.isProbabilityMeasure_map (hZ_meas n).aemeasurable
  -- Rewrite the preimage of `Z([0, Mₙ])` as `{ω | Sₙ(ω)/n ∈ [a, a+δ]}`
  have h_set_eq :
      (stdPartialSum X μ t n) ⁻¹' Set.Icc (0 : ℝ) M_n =
        {ω | (∑ i ∈ Finset.range n, X i ω) / n ∈ Set.Icc a (a + δ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [sum_div_mem_Icc_iff_stdPartialSum_mem_Icc t a δ n hn_pos (h_non_deg t) ht_deriv ω]
  -- `[0, M₀] ⊆ [0, M_n]` implies `Zₙ([0, M₀]) ≤ Zₙ([0, M_n])` under `tiltedMeasure`.
  have h_toReal_mono :
      (((tiltedMeasure X μ n t).map (stdPartialSum X μ t n)) (Set.Icc (0 : ℝ) M₀)).toReal ≤
        (((tiltedMeasure X μ n t).map (stdPartialSum X μ t n)) (Set.Icc (0 : ℝ) M_n)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.Icc_subset_Icc le_rfl hMn_ge))
  -- Combine: `1/2 - ε ≤ N([0, M₀]) - ε/2 ≤ tiltedMeasure.map(Zₙ)([0, Mₙ])
  --   = tiltedMeasure(Sₙ / n ∈ [a, a+δ])`.
  rw [← h_set_eq, ← Measure.map_apply (hZ_meas n) measurableSet_Icc]
  linarith [h_lim, h_toReal_mono]

end ProbabilityTheory
