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

- `cramer_upper_bound`: For any `a ≥ 𝔼[X 0]`, `limsup (1/n) * log ℙ(Sₙ/n ≥ a) ≤ -rateFunction X a`.

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

/-! ### Helper lemmas for the upper bound proof -/

/-- For a nonempty bounded-below set in ℝ, the infimum of its elements coerced to EReal
equals the coercion of its infimum. -/
private lemma ereal_sInf_coe_eq_coe_sInf {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    sInf ((fun (x : ℝ) => (x : EReal)) '' s) = ↑(sInf s) := by
  have h_bdd : BddBelow ((fun (x : ℝ) => (x : WithTop ℝ)) '' s) :=
    Monotone.map_bddBelow (fun _ _ h => WithTop.coe_le_coe.mpr h) hbdd
  rw [show (fun (x : ℝ) => (x : EReal)) '' s
        = (fun (y : WithTop ℝ) => (y : WithBot (WithTop ℝ))) ''
          ((fun (x : ℝ) => (x : WithTop ℝ)) '' s) from
      (Set.image_image _ (fun x : ℝ => (x : WithTop ℝ)) s).symm]
  exact (WithBot.coe_sInf' h_bdd).symm.trans (by rw [← WithTop.coe_sInf' hne hbdd]; rfl)

/-- For a bounded nonempty set in ℝ, the infimum of negations equals the negation of the supremum,
    stated in terms of coercions to EReal: `inf {↑-x | x ∈ S} = -sup {↑x | x ∈ S}` -/
private lemma ereal_sInf_neg_eq_neg_sSup {ι : Type*} (f : ι → ℝ)
    (hne : (Set.range f).Nonempty) (hbdd : BddAbove (Set.range f)) :
    sInf (Set.range fun i => (-(f i) : EReal)) = -((sSup (Set.range f) : ℝ) : EReal) := by
  obtain ⟨_, i₀, _⟩ := hne
  obtain ⟨B, hB⟩ := hbdd
  have h_ne_neg : (Set.range fun i => -f i).Nonempty := ⟨-f i₀, i₀, rfl⟩
  have h_bdd_neg : BddBelow (Set.range fun i => -f i) :=
    ⟨-B, fun _ ⟨i, hi⟩ => hi ▸ neg_le_neg (hB ⟨i, rfl⟩)⟩
  rw [show Set.range (fun i => (-(f i) : EReal)) =
        ((↑) : ℝ → EReal) '' Set.range (fun i => -f i) by
      rw [← Set.range_comp]; simp [Function.comp_def],
    ereal_sInf_coe_eq_coe_sInf h_ne_neg h_bdd_neg,
    show sInf (Set.range fun i => -f i) = -sSup (Set.range f) by
      rw [← Real.sInf_neg, ← Set.image_neg_eq_neg, ← Set.range_comp]; rfl,
    EReal.coe_neg]

include h_indep h_meas h_ident h_mgf in
/-- **Chernoff bound** for the empirical mean.
`ℙ(Sₙ/n ≥ a) ≤ exp(-n · (t · a - Λ_X₀(t)))` for `t ≥ 0`. -/
lemma prob_mean_ge_le_exp (t a : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn_pos : 0 < n) :
  (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
    ≤ Real.exp ( - (n : ℝ) * (t * a - cgf (X 0) ℙ t)) := by
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  rw [show { ω | empiricalMean X n ω ≥ a } = { ω | partialSum X n ω ≥ (n : ℝ) * a } from by
    ext ω; simp [empiricalMean, ge_iff_le, le_div_iff₀ h_n_pos, mul_comm]]
  refine (measure_ge_le_exp_cgf _ ht
    (integrable_exp_sum X h_indep h_ident h_meas h_mgf t n)).trans ?_
  rw [cgf_sum_eq_n_prod_cgf X h_indep h_ident h_meas h_mgf n t]
  apply le_of_eq; congr 1; ring

include h_indep h_meas h_ident h_mgf h_bdd h_int in
/-- **Cramér's Theorem (Upper Bound)**: For any a ≥ 𝔼[X 0], the scaled log probability that the
empirical mean exceeds a is bounded above by the negative rate function:
`limsup_{n→∞} log(ℙ(Sₙ/n ≥ a)) / n ≤ -I(a)`
Uses `ENNReal.log` to properly handle the case when probability is 0 (giving -∞). -/
theorem cramer_upper_bound (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    limsup (fun n : ℕ =>
      ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}))
        atTop ≤ (- I X a : EReal) := by
  unfold I
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
          simpa [iSup] using ereal_sInf_neg_eq_neg_sSup f ⟨_, ⟨0, h0⟩, rfl⟩ h_bdd'
      _ = (- I X a : EReal) := by
          norm_cast
          exact congrArg Neg.neg (rateFunction_eq_sup_nonneg X h_int h_mgf h_bdd a h_mean).symm
  intro t ht
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
    (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hn_pos : 0 < n := hn
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  have h_ennreal : ℙ {ω | empiricalMean X n ω ≥ a} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))) :=
    (ENNReal.ofReal_toReal_eq_iff.mpr (measure_ne_top _ _)).symm.le.trans
      (ENNReal.ofReal_le_ofReal
        (prob_mean_ge_le_exp X h_indep h_ident h_meas h_mgf t a ht n hn_pos))
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
