/-
Copyright (c) 2026 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Exponential tilting of finite product measures

Tilting a finite product measure by a sum of coordinate functions gives the product of the
tilted factors. This holds because the tilting density factors over the coordinates,
`exp (∑ i, f i (x i)) = ∏ i, exp (f i (x i))`, as does its normalization constant.

## Main results

* `MeasureTheory.tilted_pi`: `(Measure.pi μ).tilted (fun x ↦ ∑ i, f i (x i))` equals
  `Measure.pi (fun i ↦ (μ i).tilted (f i))`.
-/

@[expose] public section

open Real

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}

/-- Tilting a finite product measure by a sum of coordinate functions gives the product of the
tilted factors. -/
lemma tilted_pi (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, X i → ℝ) :
    (Measure.pi μ).tilted (fun x ↦ ∑ i, f i (x i)) =
      Measure.pi (fun i ↦ (μ i).tilted (f i)) := by
  have hZ : ∫ x, exp (∑ i, f i (x i)) ∂(Measure.pi μ) = ∏ i, ∫ x, exp (f i x) ∂(μ i) := by
    calc ∫ x, exp (∑ i, f i (x i)) ∂(Measure.pi μ)
        = ∫ x, ∏ i, exp (f i (x i)) ∂(Measure.pi μ) := by simp_rw [exp_sum]
      _ = ∏ i, ∫ x, exp (f i x) ∂(μ i) := integral_fintype_prod_eq_prod fun i x ↦ exp (f i x)
  have h_density : ∀ x : ∀ i, X i,
      exp (∑ i, f i (x i)) / ∫ y, exp (∑ i, f i (y i)) ∂(Measure.pi μ) =
        ∏ i, exp (f i (x i)) / ∫ y, exp (f i y) ∂(μ i) := fun x ↦ by
    rw [hZ, exp_sum, Finset.prod_div_distrib]
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [tilted_apply_eq_ofReal_integral' _ (.univ_pi hs)]
  simp_rw [h_density]
  rw [Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i x ↦ exp (f i x) / ∫ y, exp (f i y) ∂(μ i)),
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ integral_nonneg fun x ↦ by positivity]
  exact Finset.prod_congr rfl fun i _ ↦ (tilted_apply_eq_ofReal_integral' _ (hs i)).symm

end MeasureTheory
