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

* `Cramer.rateFunction X μ`: the Legendre transform `x ↦ ⨆ t, t * x - cgf (X 0) μ t` of the
  cumulant-generating function; this is the rate function of Cramér's theorem.
* `Cramer.upperTailRateFunction X μ`: the rate function for the upper tail `μ(a ≤ Sₙ / n)`, equal
  to `rateFunction X μ a` when `μ[X 0] ≤ a` and `0` otherwise.
* `Cramer.tiltedMeasure X μ n t`: the measure `μ` exponentially tilted by `t · Sₙ`.

## Main results

* `mgf_sum_range` and `cgf_sum_range`: the moment- and cumulant-generating functions of `Sₙ`
  factor as `mgf (∑ i ∈ Finset.range n, X i) μ t = exp (n * cgf (X 0) μ t)` and
  `cgf (∑ i ∈ Finset.range n, X i) μ t = n * cgf (X 0) μ t`.
* `Cramer.isProbabilityMeasure_tiltedMeasure`: the tilted measure `tiltedMeasure X μ n t` is a
  probability measure.
* `Cramer.rateFunction_eq_iSup_nonneg`: for `μ[X 0] ≤ a`, if the supremum defining the rate
  function is bounded above, it is attained over `0 ≤ t`.

## Implementation notes

Throughout the development the random variables `Xᵢ` and the base measure `μ` are constrained by a
fixed set of hypotheses, introduced as `variable`s in each file:

* `hindep`, `hident`, `hmeas`: the `Xᵢ` are independent, identically distributed, and
  measurable.
* `hmgf`: `X₀` has a finite moment-generating function at every `t ∈ ℝ`; equivalently
  `cgf (X 0) μ` is finite and analytic on all of `ℝ`.
* `hnondeg` (used from `TiltedCLT.lean` on): the cgf has strictly positive second derivative
  everywhere, i.e. `X₀` is non-degenerate. This is used in the central limit theorem over the
  tilted measures and, through strict monotonicity of `deriv (cgf (X 0) μ)`, to show that the
  tilting parameter is nonnegative in the lower bound. (The tangent-line argument itself needs
  only convexity of the cgf, `convexOn_cgf`, which holds unconditionally.)
* `hexposed` (used from `LowerBound.lean` on): every `a` with `μ[X 0] ≤ a` is *exposed*, i.e.
  realized as `deriv (cgf (X 0) μ) t = a` for some `t`.

The pair `hnondeg` and `hexposed` are genuinely strong assumptions: they exclude edge cases such
as bounded-support variables, for which `deriv (cgf (X 0) μ)` is bounded and not every `a` is
exposed.

No boundedness ("goodness") assumption is made on the supremum defining `rateFunction`. The
supremum can genuinely be unbounded: for a constant random variable `X ≡ c` one has
`cgf (X 0) μ t = t * c`, so `t * a - cgf (X 0) μ t = t * (a - c)` is unbounded above whenever
`a ≠ c`. Since `rateFunction` is a `Real`-valued supremum, it then takes the junk value `0` by the
`Real.iSup` convention; the upper bound handles this case directly, as the bound is trivial (the
scaled log-probabilities are nonpositive). In the lower bound, boundedness is derived from the
tangent-line argument: `hexposed` provides `t` with `deriv (cgf (X 0) μ) t = a`, and convexity of
the cgf places every `s * a - cgf (X 0) μ s` below `t * a - cgf (X 0) μ t`.

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

/-- The Legendre transform of the CGF. This is the rate function for Cramér's theorem. -/
noncomputable def Cramer.rateFunction (X : ℕ → Ω → ℝ) (μ : Measure Ω) (x : ℝ) : ℝ :=
  ⨆ t : ℝ, t * x - cgf (X 0) μ t

/-- The "Effective" Rate Function for the upper tail probability `μ(a ≤ Sₙ / n)`.
Cramér's theorem only holds when `μ[X 0] ≤ a`, so to state a general Large Deviation Principle
for all `a`, we define the rate function to be `rateFunction X μ a` for `μ[X 0] ≤ a`, and `0`
otherwise. -/
noncomputable def Cramer.upperTailRateFunction (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  if μ[X 0] ≤ a then rateFunction X μ a else 0

/-- The exponentially tilted measure, tilted by `t · Sₙ`. -/
noncomputable def Cramer.tiltedMeasure (X : ℕ → Ω → ℝ) (μ : Measure Ω) (n : ℕ)
    (t : ℝ) : Measure Ω :=
  Measure.tilted μ (fun ω => t * ∑ i ∈ Finset.range n, X i ω)

/- Assumptions for Cramér's theorem; see the module docstring for a discussion. -/
-- The random variables Xᵢ are independent.
variable (hindep : iIndepFun X μ)
-- The random variables Xᵢ are identically distributed.
variable (hident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
-- The random variables Xᵢ are measurable.
variable (hmeas : ∀ n, Measurable (X n))
-- The random variable X₀ has a finite moment generating function for all `t ∈ ℝ`.
variable (hmgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)

/-! ### Basic measurability and integrability helpers -/

include hident hmgf in
/-- The random variables Xᵢ have finite moment generating functions. -/
lemma integrable_exp_mul_of_identDistrib (i : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X i ω)) μ :=
  ((hident i).comp (measurable_const.mul measurable_id).exp).integrable_iff.mpr (hmgf t)

include hmeas in
/-- The partial sum `Sₙ` is measurable. -/
lemma measurable_sum_range (n : ℕ) : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
  Finset.measurable_sum (Finset.range n) (fun i _ => hmeas i)

include hmeas in
/-- The empirical mean `Sₙ/n` is measurable. -/
lemma measurable_sum_div (n : ℕ) : Measurable (fun ω => (∑ i ∈ Finset.range n, X i ω) / n) :=
  (measurable_sum_range hmeas n).div_const (n : ℝ)

include hmgf in
/-- All `t ∈ ℝ` lie in the interior of the domain for which `exp(tX₀)` is integrable. -/
lemma Cramer.mem_interior_integrableExpSet (t : ℝ) :
    t ∈ interior (integrableExpSet (X 0) μ) := by
  simp [Set.eq_univ_of_forall hmgf (s := integrableExpSet (X 0) μ)]

include hmgf in
/-- Integrability of `X 0` follows from finiteness of the MGF on all of `ℝ`. -/
lemma Cramer.integrable_of_forall_integrable_exp : Integrable (X 0) μ :=
  integrable_of_mem_interior_integrableExpSet (Cramer.mem_interior_integrableExpSet hmgf 0)

/-! ### Lemmas requiring `IsProbabilityMeasure` -/

variable [IsProbabilityMeasure μ]

/-- When `t < 0` and `μ[Y] ≤ a`, we have `t · a - Λ_Y(t) ≤ 0`. -/
lemma mul_sub_cgf_nonpos_of_neg (Y : Ω → ℝ) (hint : Integrable Y μ) (t a : ℝ)
    (hexp : Integrable (fun ω => Real.exp (t * Y ω)) μ) (ht : t < 0) (ha : μ[Y] ≤ a) :
    t * a - cgf Y μ t ≤ 0 := by
    -- t · a ≤ t · μ[Y] ≤ Λ(t)  (since t < 0, the first inequality flips)
  nlinarith [mul_integral_le_cgf hint hexp, mul_le_mul_of_nonpos_left ha ht.le]

include hindep hident hmeas hmgf in
/-- If each `Xᵢ` has finite MGF, then `Sₙ` also has finite MGF. -/
lemma integrable_exp_mul_sum_range (t : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range n, X i ω)) μ := by
  simpa using hindep.integrable_exp_mul_sum hmeas
    fun i _ => integrable_exp_mul_of_identDistrib hident hmgf i t

include hindep hident hmeas hmgf in
/-- The tilted measure by `t · Sₙ` is a probability measure. -/
lemma Cramer.isProbabilityMeasure_tiltedMeasure (t : ℝ) (n : ℕ) :
    IsProbabilityMeasure (tiltedMeasure X μ n t) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_sum_range hindep hident hmeas hmgf t n)

include hmgf in
/-- For `μ[X] ≤ a`, if the supremum in the rate function is bounded above, it is achieved by
non-negative `t`. That is, `rateFunction X μ a = sup_{t ∈ ℝ⁺} (tx - Λ(t))` -/
lemma Cramer.rateFunction_eq_iSup_nonneg (a : ℝ) (h_mean : μ[X 0] ≤ a)
    (hbdd : BddAbove (Set.range fun t => t * a - cgf (X 0) μ t)) :
    rateFunction X μ a = ⨆ t : {(x : ℝ) | 0 ≤ x}, (t : ℝ) * a - cgf (X 0) μ t := by
  have h_int := Cramer.integrable_of_forall_integrable_exp hmgf
  rw [rateFunction]
  have : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, by simp⟩⟩
  have h_bdd_restrict : BddAbove (Set.range fun t : {x : ℝ | 0 ≤ x} =>
      (t : ℝ) * a - cgf (X 0) μ t) :=
    let ⟨b, hb⟩ := hbdd
    ⟨b, fun _ ⟨t, ht⟩ => ht ▸ hb ⟨t.val, rfl⟩⟩
  refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun t => le_ciSup hbdd (t : ℝ))
  by_cases ht : 0 ≤ t
  -- Case 0 ≤ t: It's in the restricted set so the supremum exists by hbdd
  · exact le_ciSup h_bdd_restrict ⟨t, ht⟩
  -- Case t < 0: It's bound by the value at t=0, so the supremum is always achievable with 0 ≤ t
  · calc t * a - cgf (X 0) μ t
        ≤ 0 := mul_sub_cgf_nonpos_of_neg (X 0) h_int t a (hmgf t) (not_le.mp ht) h_mean
      _ = (0 : ℝ) * a - cgf (X 0) μ 0 := by simp [cgf_zero]
      _ ≤ _ := le_ciSup h_bdd_restrict ⟨0, by simp⟩

include hindep hident hmeas hmgf in
/-- `M_Sₙ(t) = exp(n · Λ_X₀(t))` -/
lemma mgf_sum_range (n : ℕ) (t : ℝ) :
    mgf (∑ i ∈ Finset.range n, X i) μ t = Real.exp (n * cgf (X 0) μ t) := by
  rcases n with _ | n
  · simp [cgf]
  rw [mgf_sum_of_identDistrib hmeas hindep
      (fun i _ j _ => (hident i).trans (hident j).symm)
      (Finset.mem_range.mpr n.succ_pos) t,
    Finset.card_range, cgf, mgf]
  conv_lhs => rw [← Real.exp_log (integral_exp_pos (hmgf t))]
  rw [← Real.exp_nsmul, nsmul_eq_mul]

include hindep hident hmeas hmgf in
/-- `Λ_Sₙ(t) = n · Λ_X₀(t)` -/
lemma cgf_sum_range (n : ℕ) (t : ℝ) :
    cgf (∑ i ∈ Finset.range n, X i) μ t = (n : ℝ) * cgf (X 0) μ t := by
  rw [cgf, mgf_sum_range hindep hident hmeas hmgf, Real.log_exp]

end ProbabilityTheory
