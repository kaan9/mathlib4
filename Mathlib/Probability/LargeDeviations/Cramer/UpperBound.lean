/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramer.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Cramér's theorem: upper bound

This file proves the upper (Chernoff) bound for Cramér's theorem: the scaled log-probability that
the empirical mean `Sₙ / n` exceeds a level `a ≥ μ[X 0]` is asymptotically at most `-I(a)`, where
`I` is the rate function `Cramer.rateFunction`.

The proof applies Markov's inequality to `exp (t * Sₙ)` for each `0 ≤ t`, takes the infimum over
`t`, and uses the scaling identity `cgf (∑ i ∈ Finset.range n, X i) μ = n * cgf (X 0) μ` from
`Basic.lean`. We use `ProbabilityTheory.measure_ge_le_exp_cgf`, the Chernoff bound for the upper
tail of a real-valued random variable.

## Main results

* `Cramer.limsup_le_neg_rateFunction`: for any `a` with `μ[X 0] ≤ a`,
  `limsupₙ (1 / n) * log μ(a ≤ Sₙ / n) ≤ -rateFunction X μ a`.
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal

public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → ℝ}
variable (h_indep : iIndepFun X μ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) μ μ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) μ t)))

include h_indep h_meas h_ident h_mgf in
/-- **Chernoff bound** for the empirical mean.
`μ(a ≤ Sₙ/n) ≤ exp(-n · (t · a - Λ_X₀(t)))` for `0 ≤ t`. -/
lemma measure_sum_div_ge_le_exp (t a : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn_pos : 0 < n) :
    (μ {ω | a ≤ (∑ i ∈ Finset.range n, X i ω) / n}).toReal
      ≤ Real.exp (-(n : ℝ) * (t * a - cgf (X 0) μ t)) := by
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  rw [show { ω | a ≤ (∑ i ∈ Finset.range n, X i ω) / n } =
      { ω | (n : ℝ) * a ≤ (∑ i ∈ Finset.range n, X i) ω }
      from by ext ω; simp [le_div_iff₀ h_n_pos, mul_comm]]
  refine (measure_ge_le_exp_cgf _ ht (by
    simpa using integrable_exp_mul_sum_range h_indep h_ident h_meas h_mgf t n)).trans ?_
  rw [cgf_sum_range h_indep h_ident h_meas h_mgf n t]
  apply le_of_eq; congr 1; ring

include h_indep h_meas h_ident h_mgf h_bdd in
/-- **Cramér's theorem** (upper bound): for any `a` with `μ[X 0] ≤ a`, the scaled log probability
that the empirical mean exceeds `a` is bounded above by the negative rate function,
`limsup_{n→∞} log(μ(a ≤ Sₙ/n)) / n ≤ -rateFunction X μ a`.
This uses `ENNReal.log` to handle the case when the probability is `0` (giving `-∞`). -/
theorem Cramer.limsup_le_neg_rateFunction (a : ℝ) (h_mean : μ[X 0] ≤ a) :
    limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) *
      ENNReal.log (μ {ω | a ≤ (∑ i ∈ Finset.range n, X i ω) / n}))
        atTop ≤ (- rateFunction X μ a : EReal) := by
  unfold rateFunction
  set L := limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) *
      ENNReal.log (μ {ω | a ≤ (∑ i ∈ Finset.range n, X i ω) / n})) atTop
  set f : {x : ℝ | 0 ≤ x} → ℝ := fun t => t.val * a - cgf (X 0) μ t
  have h0 : (0 : ℝ) ∈ {x : ℝ | 0 ≤ x} := by simp
  haveI : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, h0⟩⟩
  suffices h : ∀ t : ℝ, 0 ≤ t → L ≤ (-(t * a - cgf (X 0) μ t) : EReal) by
    calc L
        ≤ sInf (Set.range fun t : {x : ℝ | 0 ≤ x} => (-(f t) : EReal)) :=
          le_csInf (Set.range_nonempty _) <| by
            rintro b ⟨t, rfl⟩; exact h t.val t.property
      _ = (-(⨆ t : {x : ℝ | 0 ≤ x}, f t) : EReal) := by
          have h_bdd' : BddAbove (Set.range f) :=
            let ⟨b, hb⟩ := h_bdd a
            ⟨b, fun _ ⟨t, ht⟩ => ht ▸ hb ⟨t.val, rfl⟩⟩
          have h_ne : (Set.range fun t : {x : ℝ | 0 ≤ x} => -f t).Nonempty :=
            ⟨-f ⟨0, h0⟩, ⟨0, h0⟩, rfl⟩
          have h_bdd_neg : BddBelow (Set.range fun t : {x : ℝ | 0 ≤ x} => -f t) := by
            obtain ⟨B, hB⟩ := h_bdd'
            exact ⟨-B, fun _ ⟨t, ht⟩ => ht ▸ neg_le_neg (hB ⟨t, rfl⟩)⟩
          have h_real : sInf (Set.range fun t : {x : ℝ | 0 ≤ x} => -f t) = -(⨆ t, f t) := by
            rw [show (⨆ t : {x : ℝ | 0 ≤ x}, f t) = sSup (Set.range f) from rfl,
              ← Real.sInf_neg, ← Set.image_neg_eq_neg, ← Set.range_comp]; rfl
          rw [show (Set.range fun t : {x : ℝ | 0 ≤ x} => (-(f t) : EReal))
                = Real.toEReal '' (Set.range fun t : {x : ℝ | 0 ≤ x} => -f t) by
              rw [← Set.range_comp]; simp [Function.comp_def, EReal.coe_neg],
            ← EReal.coe_sInf h_ne h_bdd_neg, h_real, EReal.coe_neg]
      _ = (- rateFunction X μ a : EReal) := by
          norm_cast
          exact congrArg Neg.neg (rateFunction_eq_iSup_nonneg h_mgf h_bdd a h_mean).symm
  intro t ht
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
    (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hn_pos : 0 < n := hn
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have h_ennreal : μ {ω | a ≤ (∑ i ∈ Finset.range n, X i ω) / n} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) μ t))) :=
    (ENNReal.ofReal_toReal_eq_iff.mpr (measure_ne_top _ _)).symm.le.trans
      (ENNReal.ofReal_le_ofReal
        (measure_sum_div_ge_le_exp h_indep h_ident h_meas h_mgf t a ht n hn_pos))
  have h_log_exp : ENNReal.log (ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) μ t))))
      = (((-(n : ℝ) * (t * a - cgf (X 0) μ t)) : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have h_arith : (1 : ℝ) / (n : ℝ) * (-(n : ℝ) * (t * a - cgf (X 0) μ t))
      = -(t * a - cgf (X 0) μ t) := by field_simp
  calc ((1 : ℝ) / (n : ℝ) : EReal) *
      ENNReal.log (μ {ω | a ≤ (∑ i ∈ Finset.range n, X i ω) / n})
      ≤ ((1 : ℝ) / (n : ℝ) : EReal) *
          (((-(n : ℝ) * (t * a - cgf (X 0) μ t)) : ℝ) : EReal) := by
        rw [← h_log_exp]; gcongr
    _ = (-(t * a - cgf (X 0) μ t) : EReal) := by
        simp only [← EReal.coe_mul]; exact congrArg (fun x : ℝ => (x : EReal)) h_arith

end ProbabilityTheory
