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
open scoped BigOperators ENNReal

@[expose] public section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable (X : ℕ → Ω → ℝ)
variable (h_indep : iIndepFun X ℙ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
variable (h_meas : ∀ n, Measurable (X n))
variable (h_int : Integrable (X 0) ℙ)
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) ℙ t)))

/-! ### Helper lemmas for the upper bound proof -/

/-- For bounded sets in ℝ, the infimum of negations equals the negation of the supremum. -/
private lemma csInf_neg_eq_neg_csSup {ι : Type*} (f : ι → ℝ) (hne : (Set.range f).Nonempty)
    (hbdd_above : BddAbove (Set.range f)) :
    sInf (Set.range fun i => -f i) = -sSup (Set.range f) := by
  have h_bdd_below : BddBelow (Set.range fun i => -f i) := by
    obtain ⟨B, hB⟩ := hbdd_above
    use -B
    intro y ⟨i, hi⟩
    rw [← hi]
    exact neg_le_neg (hB ⟨i, rfl⟩)
  have h_nonempty_neg : (Set.range fun i => -f i).Nonempty := by
    obtain ⟨x, ⟨i, hi⟩⟩ := hne
    use -x
    use i
    rw [← hi]
  apply le_antisymm
  · -- sInf {-f(i)} ≤ -sSup {f(i)}
    suffices sSup (Set.range f) ≤ -sInf (Set.range fun i => -f i) by linarith
    apply csSup_le hne
    intro b ⟨i, hi⟩
    rw [← hi]
    have : sInf (Set.range fun j => -f j) ≤ -f i := csInf_le h_bdd_below ⟨i, rfl⟩
    linarith
  · -- -sSup {f(i)} ≤ sInf {-f(i)}
    apply le_csInf h_nonempty_neg
    intro b ⟨i, hi⟩
    rw [← hi]
    exact neg_le_neg (le_csSup hbdd_above ⟨i, rfl⟩)

/-- For a nonempty bounded-below set in ℝ, the infimum of its elements coerced to EReal
equals the coercion of its infimum. -/
private lemma ereal_sInf_coe_eq_coe_sInf {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    sInf ((fun (x : ℝ) => (x : EReal)) '' s) = ↑(sInf s) := by
  -- Show that the lifting `ℝ → EReal` equals the composition of first lifting `ℝ → {ℝ, ⊤}`,
  -- then lifting `{ℝ, ⊤} → EReal`.
  have h_image : (fun (x : ℝ) => (x : EReal)) '' s =
      (fun (y : WithTop ℝ) => (y : WithBot (WithTop ℝ))) ''
        ((fun (x : ℝ) => (x : WithTop ℝ)) '' s) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · intro ⟨x, hx, hz⟩
      use (x : WithTop ℝ)
      constructor
      · use x, hx
      · exact hz
    · intro ⟨y, ⟨x, hx, hy⟩, hz⟩
      use x, hx
      rw [← hz, ← hy]
      rfl
  rw [h_image]
  -- Apply coe_sInf' twice, once for lifting to `{ℝ, ⊤}`, then again for lifting to `EReal`.
  have h_bdd_withTop : BddBelow ((fun (x : ℝ) => (x : WithTop ℝ)) '' s) :=
    Monotone.map_bddBelow (fun _ _ h => WithTop.coe_le_coe.mpr h) hbdd
  calc sInf ((fun (y : WithTop ℝ) => (y : WithBot (WithTop ℝ))) ''
        ((fun (x : ℝ) => (x : WithTop ℝ)) '' s))
      = (↑(sInf ((fun (x : ℝ) => (x : WithTop ℝ)) '' s)) : WithBot (WithTop ℝ)) :=
          (WithBot.coe_sInf' h_bdd_withTop).symm
    _ = (↑(↑(sInf s) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
          congr 1
          exact (WithTop.coe_sInf' hne hbdd).symm
    _ = ↑(sInf s) := rfl

/-- For a bounded nonempty set in ℝ, the infimum of negations equals the negation of the supremum,
    stated in terms of coercions to EReal: `inf {↑-x | x ∈ S} = -sup {↑x | x ∈ S}` -/
private lemma ereal_sInf_neg_eq_neg_sSup {ι : Type*} (f : ι → ℝ)
    (hne : (Set.range f).Nonempty) (hbdd : BddAbove (Set.range f)) :
    sInf (Set.range fun i => (-(f i) : EReal)) = -((sSup (Set.range f) : ℝ) : EReal) := by
  -- The range of negations is bounded below and nonempty
  have h_bdd_neg : BddBelow (Set.range fun i => -f i) := by
    obtain ⟨B, hB⟩ := hbdd
    use -B
    intro y ⟨i, hi⟩
    rw [← hi]
    exact neg_le_neg (hB ⟨i, rfl⟩)
  have h_ne_neg : (Set.range fun i => -f i).Nonempty := by
    obtain ⟨x, ⟨i, hi⟩⟩ := hne
    use -x, i
    rw [← hi]
  -- Get the result for the non-coerced case
  have h_real := csInf_neg_eq_neg_csSup f hne hbdd
  -- Show that the set of coerced negations equals the image under coe
  have h_set_eq : Set.range (fun i => (-(f i) : EReal)) =
      (fun (a : ℝ) => ↑a) '' Set.range (fun i => -f i) := by
    ext x
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · intro ⟨i, hi⟩
      use -f i, ⟨i, rfl⟩
      rw [← hi]; rfl
    · intro ⟨y, ⟨i, hi⟩, hx⟩
      use i
      rw [← hx, ← hi, EReal.coe_neg]
  -- Conclude by applying above derivations
  rw [h_set_eq, ereal_sInf_coe_eq_coe_sInf h_ne_neg h_bdd_neg, h_real, EReal.coe_neg]

include h_indep h_meas h_ident h_mgf in
/-- **Chernoff bound** for the empirical mean.
`ℙ(Sₙ/n ≥ a) ≤ exp(-n · (t · a - Λ_X₀(t)))` for `t ≥ 0`. -/
lemma prob_mean_ge_le_exp (t a : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn_pos : 0 < n) :
  (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
    ≤ Real.exp ( - (n : ℝ) * (t * a - cgf (X 0) ℙ t)) := by
  have h_n_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have h_set_eq : { ω | empiricalMean X n ω ≥ a } =
          { ω | partialSum X n ω ≥ (n : ℝ) * a } := by
    ext ω
    simp only [Set.mem_setOf_eq, empiricalMean, partialSum, ge_iff_le]
    constructor
    · intro h
      have h1 : a * (n : ℝ) ≤ partialSum X n ω := by
        exact (le_div_iff₀ h_n_pos).mp h
      rwa [mul_comm] at h1
    · intro h
      have h1 : a * (n : ℝ) ≤ partialSum X n ω := by rwa [mul_comm]
      exact (le_div_iff₀ h_n_pos).mpr h1
  have hinteg : Integrable (fun ω => Real.exp (t * partialSum X n ω)) ℙ :=
    integrable_exp_sum X h_indep h_ident h_meas h_mgf t n
  -- Apply standard Chernoff bound to `Sₙ` with threshold `n · a`
  have chernoff := ProbabilityTheory.measure_ge_le_exp_cgf ((n : ℝ) * a) (ht) (hinteg)
  -- Rewrite CGF of `Sₙ` in terms of CGF of `X₁` by independence and simplify
  calc
    (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
        = (ℙ {ω | partialSum X n ω ≥ (n : ℝ) * a}).toReal := by rw [h_set_eq]
    _ ≤ Real.exp (-t * ((n : ℝ) * a) + cgf (partialSum X n) ℙ t) := by
      exact chernoff
    _ = Real.exp ( (n : ℝ) * ( - t * a + cgf (X 0) ℙ t) ) := by
      rw [cgf_sum_eq_n_prod_cgf X h_indep h_ident h_meas h_mgf n t]; ring_nf
    _ = Real.exp ( - (n : ℝ) * ( t * a - cgf (X 0) ℙ t) ) := by
      ring_nf

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
  -- Show that for each `t ≥ 0`, `limsup ≤ -(t * a - cgf t)`.
  -- Then taking the infimum over `t` yields `limsup ≤ -rateFunction a`.
  suffices h : ∀ t : ℝ, 0 ≤ t →
    limsup (fun n : ℕ =>
      ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}))
        atTop ≤ (-(t * a - cgf (X 0) ℙ t) : EReal) by
    calc limsup (fun n : ℕ =>
          ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
        ≤ sInf (Set.range fun t : {x : ℝ | 0 ≤ x} =>
            (-(t.val * a - cgf (X 0) ℙ t) : EReal)) := by
          apply le_csInf
          · have : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, by simp⟩⟩
            exact Set.range_nonempty _
          · intro b ⟨t, ht⟩
            rw [← ht]
            exact h t.val t.property
      _ = (-(⨆ t : {x : ℝ | 0 ≤ x}, t.val * a - cgf (X 0) ℙ t) : EReal) := by
          have h_bdd_restrict :
              BddAbove (Set.range fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t) := by
            obtain ⟨b, hb⟩ := h_bdd a
            use b
            intro y ⟨t, ht⟩
            rw [← ht]
            exact hb ⟨t.val, rfl⟩
          have h_nonempty :
              (Set.range fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t).Nonempty := by
            use 0 * a - cgf (X 0) ℙ 0
            use ⟨0, by simp⟩
          simp only [iSup]
          exact ereal_sInf_neg_eq_neg_sSup
            (fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t) h_nonempty h_bdd_restrict
      _ = (- I X a : EReal) := by
          congr 1
          norm_cast
          exact (@rateFunction_eq_sup_nonneg _ _ X h_int h_mgf h_bdd _ a  h_mean).symm
  intro t ht
  -- For each `n > 0`, use the Chernoff bound: `ℙ(Sₙ/n ≥ a) ≤ exp(-n(ta - Λ(t)))`.
  have h_event : ∀ n : ℕ, 0 < n →
    (ℙ {ω | empiricalMean X n ω ≥ a}).toReal ≤
      Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)) := by
    intro n hn
    exact prob_mean_ge_le_exp X h_indep h_ident h_meas h_mgf t a ht n hn
  -- Scale correctly in `EReal` using explicit `ENNReal.log` (so that `log 0 = -∞`).
  have h_scaled : ∀ n : ℕ, 0 < n →
    ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}) ≤
      (-(t * a - cgf (X 0) ℙ t) : EReal) := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h_exp := h_event n hn
    -- Convert bound into ENNReal.log on both sides
    have h_ennreal : (ℙ {ω | empiricalMean X n ω ≥ a}) ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))) := by
      rw [← ENNReal.ofReal_toReal_eq_iff.mpr (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h_exp
    have h_log : ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}) ≤
        ENNReal.log (ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)))) :=
      ENNReal.log_le_log h_ennreal
    -- Simplify log(exp(x))
    -- we use the property that exp(x) is non-negative to justify eliminating the ENNReal.ofReal
    have h_log_exp : ENNReal.log (ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)))) =
        (-(n : ℝ) * (t * a - cgf (X 0) ℙ t) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _)]
      rw [Real.log_exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))]
      rfl
    -- Simplify `n⁻¹ (-n (ta - Λ(t)))`
    have h_arith : ((1 : ℝ) / (n : ℝ)) * (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)) =
        -(t * a - cgf (X 0) ℙ t) := by
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
      field_simp [hn_ne]
    trans ((1 : ℝ) / (n : ℝ) : EReal) * (-(n : ℝ) * (t * a - cgf (X 0) ℙ t) : EReal)
    · rw [← h_log_exp]
      gcongr
    · simp only [← EReal.coe_mul]
      exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) h_arith)
  apply Filter.limsup_le_of_le
  · -- IsCoboundedUnder: bounded below by -∞ (always true for EReal)
    exact isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
  · -- The bound holds eventually
    apply Filter.eventually_atTop.mpr
    use 1
    intro n hn
    exact h_scaled n hn
