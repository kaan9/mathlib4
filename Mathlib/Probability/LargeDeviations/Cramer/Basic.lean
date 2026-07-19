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

import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Convex.Integral

/-!
# Cramér's theorem: basic definitions and infrastructure

Cramér's theorem describes the large-deviation behaviour of the empirical mean
`Sₙ / n = (X₀ + ⋯ + Xₙ₋₁) / n` of a sequence of i.i.d. real random variables `Xᵢ` with finite
moment-generating function: the tail probabilities `μ(a ≤ Sₙ / n)` decay exponentially, at a rate
given by the rate function `Cramer.rateFunction`, the Legendre transform of the
cumulant-generating function of `X₀`.

This file collects the core definitions and the shared infrastructure used to prove the two bounds
of the theorem. The upper and lower bounds are proved in `UpperBound.lean` and `LowerBound.lean`,
and the two bounds are assembled in `Theorem.lean`.

## Main definitions

* `partialSum X n`: the partial sum `Sₙ = X₀ + ⋯ + Xₙ₋₁`.
* `empiricalMean X n`: the empirical mean `Sₙ / n`.
* `Cramer.rateFunction X μ`: the Legendre transform `x ↦ ⨆ t, t * x - cgf (X 0) μ t` of the
  cumulant-generating function; this is the rate function of Cramér's theorem.
* `Cramer.upperTailRateFunction X μ`: the rate function for the upper tail `μ(a ≤ Sₙ / n)`, equal
  to `rateFunction X μ a` when `μ[X 0] ≤ a` and `0` otherwise.
* `Cramer.tiltedMeasure X μ n t`: the measure `μ` exponentially tilted by `t · Sₙ`.

## Main results

* `mgf_partialSum` and `cgf_partialSum`: the moment- and cumulant-generating functions of `Sₙ`
  factor as `mgf (partialSum X n) μ t = exp (n * cgf (X 0) μ t)` and
  `cgf (partialSum X n) μ t = n * cgf (X 0) μ t`.
* `Cramer.isProbabilityMeasure_tiltedMeasure`: the tilted measure `tiltedMeasure X μ n t` is a
  probability measure.
* `Cramer.rateFunction_eq_iSup_nonneg`: for `μ[X 0] ≤ a` the supremum defining the rate function
  is attained over `0 ≤ t`.

## Implementation notes

Throughout the development the random variables `Xᵢ` and the base measure `μ` are constrained by a
fixed set of hypotheses, introduced as `variable`s in each file:

* `h_indep`, `h_ident`, `h_meas`: the `Xᵢ` are independent, identically distributed, and
  measurable.
* `h_mgf`: `X₀` has a finite moment-generating function at every `t ∈ ℝ`; equivalently
  `cgf (X 0) μ` is finite and analytic on all of `ℝ`.
* `h_bdd`: the rate function is a *good* rate function, i.e. the supremum defining it is bounded
  above. This is **not** implied by `h_mgf` alone: for a constant random variable `X ≡ c` one has
  `cgf (X 0) μ t = t * c`, so `t * a - cgf (X 0) μ t = t * (a - c)` is unbounded above whenever
  `a ≠ c`. It is, however, derivable from `h_exposed` together with convexity of the cgf for every
  relevant `a` (those with `μ[X 0] ≤ a`); we keep it as a hypothesis to avoid that detour.
* `h_non_deg` (used from `TiltedCLT.lean` on): the cgf has strictly positive second derivative
  everywhere, i.e. `X₀` is non-degenerate. This gives strict convexity of the cgf, used both in the
  central limit theorem over the tilted measures and in the tangent-line argument for the lower
  bound.
* `h_exposed` (used from `LowerBound.lean` on): every `a` with `μ[X 0] ≤ a` is *exposed*, i.e.
  realized as `deriv (cgf (X 0) μ) t = a` for some `t`.

The pair `h_non_deg` and `h_exposed` are genuinely strong assumptions: they exclude edge cases such
as bounded-support variables, for which `deriv (cgf (X 0) μ)` is bounded and not every `a` is
exposed.

## References

The statement and its exponential-tilting proof follow Theorem 2.2.3 of
[A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*][demboZeitouni2010].
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
variable {X : ℕ → Ω → ℝ}

/-- The partial sum X₁ + ... + Xₙ. -/
def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range n, X i

/-- The empirical mean Sₙ / n. -/
noncomputable def empiricalMean (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := fun ω => partialSum X n ω / n

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

/- Assumptions for Cramér's theorem; see the module docstring for a discussion. -/
-- The random variables Xᵢ are independent.
variable (h_indep : iIndepFun X μ)
-- The random variables Xᵢ are identically distributed.
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
-- The random variables Xᵢ are measurable.
variable (h_meas : ∀ n, Measurable (X n))
-- The random variable X₀ has a finite moment generating function for all `t ∈ ℝ`.
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
-- The rate function is "good": the supremum defining it is bounded above.
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
  (measurable_partialSum h_meas n).div_const (n : ℝ)

include h_mgf in
/-- All `t ∈ ℝ` lie in the interior of the domain for which `exp(tX₀)` is integrable. -/
lemma Cramer.mem_interior_integrableExpSet (t : ℝ) :
    t ∈ interior (integrableExpSet (X 0) μ) := by
  simp [Set.eq_univ_of_forall h_mgf (s := integrableExpSet (X 0) μ)]

include h_mgf in
/-- Integrability of `X 0` follows from finiteness of the MGF on all of `ℝ`. -/
lemma Cramer.integrable_of_forall_integrable_exp : Integrable (X 0) μ :=
  integrable_of_mem_interior_integrableExpSet (Cramer.mem_interior_integrableExpSet h_mgf 0)

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
    Integrable (fun ω => Real.exp (t * partialSum X n ω)) μ :=
  h_indep.integrable_exp_mul_sum h_meas
    fun i _ => integrable_exp_mul_of_identDistrib h_ident h_mgf i t

include h_indep h_ident h_meas h_mgf in
/-- The tilted measure by `t · Sₙ` is a probability measure. -/
lemma Cramer.isProbabilityMeasure_tiltedMeasure (t : ℝ) (n : ℕ) :
    IsProbabilityMeasure (tiltedMeasure X μ n t) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_partialSum h_indep h_ident h_meas h_mgf t n)

include h_indep h_ident h_meas h_mgf in
/-- Every `t ∈ ℝ` is in the interior of the domain where `e^{t Sₙ}` is integrable. -/
lemma mem_interior_integrableExpSet_partialSum (t : ℝ) (n : ℕ) :
    t ∈ interior (integrableExpSet (partialSum X n) μ) := by
  simp [Set.eq_univ_of_forall
    (fun s => integrable_exp_mul_partialSum h_indep h_ident h_meas h_mgf s n)
    (s := integrableExpSet (partialSum X n) μ)]

include h_bdd h_mgf in
/-- For `μ[X] ≤ a`, the supremum in the rate function is achieved by non-negative `t`.
That is, `rateFunction X μ a = sup_{t ∈ ℝ⁺} (tx - Λ(t))` -/
lemma Cramer.rateFunction_eq_iSup_nonneg (a : ℝ) (h_mean : μ[X 0] ≤ a) :
    rateFunction X μ a = ⨆ t : {(x : ℝ) | 0 ≤ x}, (t : ℝ) * a - cgf (X 0) μ t := by
  have h_int := Cramer.integrable_of_forall_integrable_exp h_mgf
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
  rw [cgf, mgf_partialSum h_indep h_ident h_meas h_mgf, Real.log_exp]

end ProbabilityTheory
