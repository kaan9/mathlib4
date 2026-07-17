/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Probability.LargeDeviations.Cramers.Basic

/-!
# Cramér's Theorem — Upper Bound

This file proves the upper (Chernoff) bound for Cramér's theorem:

- `Cramer.limsup_le_neg_rateFunction`: For any `a ≥ 𝔼[X 0]`,
  `limsup (1/n) * log ℙ(Sₙ/n ≥ a) ≤ -rateFunction X a`.

The proof applies Markov's inequality to `exp(t * Sₙ)` for each `t ≥ 0`,
takes the infimum over `t`, and uses the scaling identity `cgf(Sₙ) = n * cgf(X₀)`.

We use `ProbabilityTheory.measure_ge_le_exp_cgf` that gives the Chernoff bound for the upper
tail of a real-valued random variable.
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (X : ℕ → Ω → ℝ)
variable (h_indep : iIndepFun X ℙ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_int : Integrable (X 0) ℙ)
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) ℙ t)))

include h_indep h_meas h_ident h_mgf in
/-- **Chernoff bound** for the empirical mean.
`ℙ(Sₙ/n ≥ a) ≤ exp(-n · (t · a - Λ_X₀(t)))` for `t ≥ 0`. -/
lemma measure_empiricalMean_ge_le_exp (t a : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn_pos : 0 < n) :
  (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
    ≤ Real.exp ( - (n : ℝ) * (t * a - cgf (X 0) ℙ t)) := by
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  rw [show { ω | empiricalMean X n ω ≥ a } = { ω | partialSum X n ω ≥ (n : ℝ) * a }
      from by ext ω; simp [empiricalMean, ge_iff_le, le_div_iff₀ h_n_pos, mul_comm]]
  refine (measure_ge_le_exp_cgf _ ht
    (integrable_exp_mul_partialSum X h_indep h_ident h_meas h_mgf t n)).trans ?_
  rw [cgf_partialSum X h_indep h_ident h_meas h_mgf n t]
  apply le_of_eq; congr 1; ring

include h_indep h_meas h_ident h_mgf h_bdd h_int in
/-- **Cramér's Theorem (Upper Bound)**: For any a ≥ 𝔼[X 0], the scaled log probability that
the empirical mean exceeds a is bounded above by the negative rate function:
`limsup_{n→∞} log(ℙ(Sₙ/n ≥ a)) / n ≤ -rateFunction X a`
Uses `ENNReal.log` to properly handle the case when probability is 0 (giving -∞). -/
theorem Cramer.limsup_le_neg_rateFunction (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    limsup (fun n : ℕ =>
      ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}))
        atTop ≤ (- rateFunction X a : EReal) := by
  unfold rateFunction
  set L := limsup (fun n : ℕ =>
      ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
  set f : {x : ℝ | 0 ≤ x} → ℝ := fun t => t.val * a - cgf (X 0) ℙ t
  have h0 : (0 : ℝ) ∈ {x : ℝ | 0 ≤ x} := by simp
  haveI : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, h0⟩⟩
  suffices h : ∀ t : ℝ, 0 ≤ t → L ≤ (-(t * a - cgf (X 0) ℙ t) : EReal) by
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
      _ = (- rateFunction X a : EReal) := by
          norm_cast
          exact congrArg Neg.neg (rateFunction_eq_iSup_nonneg X h_int h_mgf h_bdd a h_mean).symm
  intro t ht
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
    (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hn_pos : 0 < n := hn
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have h_ennreal : ℙ {ω | empiricalMean X n ω ≥ a} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))) :=
    (ENNReal.ofReal_toReal_eq_iff.mpr (measure_ne_top _ _)).symm.le.trans
      (ENNReal.ofReal_le_ofReal
        (measure_empiricalMean_ge_le_exp X h_indep h_ident h_meas h_mgf t a ht n hn_pos))
  have h_log_exp : ENNReal.log (ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))))
      = (((-(n : ℝ) * (t * a - cgf (X 0) ℙ t)) : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have h_arith : (1 : ℝ) / (n : ℝ) * (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))
      = -(t * a - cgf (X 0) ℙ t) := by field_simp
  calc ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})
      ≤ ((1 : ℝ) / (n : ℝ) : EReal) *
          (((-(n : ℝ) * (t * a - cgf (X 0) ℙ t)) : ℝ) : EReal) := by
        rw [← h_log_exp]; gcongr
    _ = (-(t * a - cgf (X 0) ℙ t) : EReal) := by
        simp only [← EReal.coe_mul]; exact congrArg (fun x : ℝ => (x : EReal)) h_arith

end ProbabilityTheory
