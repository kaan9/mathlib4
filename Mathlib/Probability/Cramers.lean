/-
Copyright (c) 2025 Kaan.
Authors: Kaan
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Cramér's Theorem

This file proves Cramér's theorem on large deviations for i.i.d. random variables.

## Main results

* `cramer_upper_bound`: Upper bound for the probability that the empirical mean exceeds a threshold
* `cramer_rate_function`: The rate function for Cramér's theorem (Legendre transform of CGF)

## References

* Dembo, Amir, and Ofer Zeitouni. "Large deviations techniques and applications." (1998).
-/

open ProbabilityTheory MeasureTheory Filter Topology
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasureSpace Ω]
variable (X : ℕ → Ω → ℝ)

/- Assumptions for Cramér's theorem -/
variable (h_indep : iIndepFun X ℙ)
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
variable (h_meas : ∀ n, Measurable (X n))
-- This is implied by h_mgf but we assume it for convenience
variable (h_int : Integrable (X 0) ℙ)
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
-- Assume that this is a "good" rate function, bounded above.
-- This is actually implied by h_mgf but this is difficult to prove.
variable (h_bdd : ∀ a : ℝ, BddAbove (Set.range (fun t => t * a - cgf (X 0) ℙ t)))

/-- The partial sum X_0 + ... + X_{n-1}. -/
noncomputable def S (n : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range n, X i

/-- The empirical mean Sₙ / n. -/
noncomputable def empiricalMean (n : ℕ) : Ω → ℝ := fun ω => S X n ω / n

/-- The Legendre transform of the CGF. This is the rate function for Cramér's theorem. -/
noncomputable def rateFunction (x : ℝ) : ℝ :=
  ⨆ t : ℝ, t * x - cgf (X 0) ℙ t

/-- The "Effective" Rate Function for the upper tail probability ℙ(Sₙ ≥ a).
Cramér's theorem only holds when a ≥ 𝔼[X 0], so to state a general Large Deviato
This matches the Legendre transform when a ≥ 𝔼[X 0], but flattens to 0 otherwise. -/
noncomputable def upperTailRateFunction (X : ℕ → Ω → ℝ) (a : ℝ) : ℝ :=
  if 𝔼[X 0] ≤ a then rateFunction X a else 0

/- Helper lemmas -/

/-- The upper tail rate function equals the standard rate function when a is above the mean. -/
lemma upperTailRateFunction_eq_rateFunction {X : ℕ → Ω → ℝ} (a : ℝ) (h : 𝔼[X 0] ≤ a) :
    upperTailRateFunction X a = rateFunction X a := by
  rw [upperTailRateFunction, if_pos h]

/-- The upper tail rate function is zero when a is below the mean. -/
lemma upperTailRateFunction_eq_zero {X : ℕ → Ω → ℝ} (a : ℝ) (h : a < 𝔼[X 0]) :
    upperTailRateFunction X a = 0 := by
  rw [upperTailRateFunction, if_neg (not_le.mpr h)]

include h_ident h_mgf in lemma integrable_exp_of_identDistrib (i : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X i ω)) ℙ := by
  have hcomp : Measurable (fun x : ℝ => Real.exp (t * x)) :=
    (measurable_const.mul measurable_id).exp
  have : IdentDistrib (fun ω => Real.exp (t * X i ω)) (fun ω => Real.exp (t * X 0 ω)) ℙ ℙ :=
    (h_ident i).comp hcomp
  exact this.integrable_iff.mpr (h_mgf t)

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

-- For a random variable with finite MGF, the CGF satisfies cgf(t) ≥ t * E[X].
-- This follows from Jensen's inequality applied to the convex function exp(tx) for fixed t.
lemma cgf_ge_mul_expect {Y : Ω → ℝ} (h_int : Integrable Y ℙ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) ℙ) (t : ℝ) :
    cgf Y ℙ t ≥ t * 𝔼[Y] := by
  -- cgf(t) = log E[exp(tY)] ≥ log exp(t E[Y]) = t E[Y]
  -- This follows from exp being convex and Jensen's inequality
  rw [cgf, mgf]
  -- Apply Jensen's inequality: exp(E[tY]) ≤ E[exp(tY)]
  have jensen := ConvexOn.map_integral_le
    (g := Real.exp) (s := Set.univ) (f := fun ω => t * Y ω)
    (convexOn_exp) Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (h_int.const_mul t) (h_mgf t)
  -- Jensen gives: exp(∫ tY) ≤ ∫ exp(tY)
  rw [integral_const_mul] at jensen
  -- Taking log of both sides (log is monotone)
  have h_pos : 0 < ∫ (a : Ω), Real.exp (t * Y a) ∂ℙ := integral_exp_pos (h_mgf t)
  calc t * 𝔼[Y]
      = t * ∫ (a : Ω), Y a ∂ℙ := rfl
    _ = Real.log (Real.exp (t * ∫ (a : Ω), Y a ∂ℙ)) := by rw [Real.log_exp _]
    _ ≤ Real.log (∫ (a : Ω), Real.exp (t * Y a) ∂ℙ) :=
        Real.log_le_log (Real.exp_pos _) jensen

-- When t < 0 and a ≥ E[X], we have t*a - cgf(t) ≤ 0
lemma rate_function_neg_param_le_zero {Y : Ω → ℝ} (h_int : Integrable Y ℙ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) ℙ)
    {t a : ℝ} (ht : t < 0) (ha : 𝔼[Y] ≤ a) :
    t * a - cgf Y ℙ t ≤ 0 := by
  have h_cgf := cgf_ge_mul_expect h_int h_mgf t
  -- cgf t ≥ t * E[Y] ≥ t * a  (since t < 0, inequality flips)
  have : t * 𝔼[Y] ≥ t * a := by
    exact mul_le_mul_of_nonpos_left ha (le_of_lt ht)
  calc t * a - cgf Y ℙ t
      ≤ t * a - t * 𝔼[Y] := by linarith [h_cgf]
    _ = t * (a - 𝔼[Y]) := by ring
    _ ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht)
        linarith

include h_indep h_meas h_ident h_mgf in lemma integrable_exp_sum (t : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (t * S X n ω)) ℙ := by
    -- Move the scalar `t` inside the finite sum so we can use `Real.exp_sum`.
    rw [S]
    have : (fun ω => Real.exp (t * (∑ i ∈ Finset.range n, X i) ω)) =
            fun ω => Real.exp (∑ i ∈ Finset.range n, t * X i ω) := by
      funext ω
      -- use `mul_sum` (or `Finset.mul_sum`) and `mul_comm` to commute scalar multiplication
      simp [Finset.mul_sum]
    rw [this]
    conv =>
      lhs
      intro ω
      rw [Real.exp_sum] -- now exp(∑ (t * X_i)) = ∏ exp(t * X_i)
    -- Goal: Integrable (fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω)) ℙ
    -- Strategy: Use induction and IndepFun.integrable_mul
    induction n with
    | zero =>
      -- Empty product is 1, which is integrable
      simp only [Finset.range_zero, Finset.prod_empty]
      exact integrable_const 1
    | succ n ih =>
      -- Product over range (n+1) = (product over range n) * exp(t * X_n)
      have h_eq : (fun ω => ∏ i ∈ Finset.range (n + 1), Real.exp (t * X i ω)) =
          (fun ω => (∏ i ∈ Finset.range n, Real.exp (t * X i ω)) * Real.exp (t * X n ω)) := by
        funext ω
        rw [Finset.prod_range_succ]
      rw [h_eq]
      -- Show exp(t * X_n) is integrable
      have h_integrable_n : Integrable (fun ω => Real.exp (t * X n ω)) ℙ := by
        by_cases hn : n = 0
        · rw [hn]; exact h_mgf t
        · -- Use that X_n and X_0 are identically distributed
          have h_ident_n := h_ident n
          have h_comp : IdentDistrib (fun ω => Real.exp (t * X n ω))
              (fun ω => Real.exp (t * X 0 ω)) ℙ ℙ :=
            h_ident_n.comp (measurable_const.mul measurable_id).exp
          exact h_comp.integrable_iff.2 (h_mgf t)
      -- Establish independence for the composed functions
      have h_indep_exp : iIndepFun (fun i ω => Real.exp (t * X i ω)) ℙ := by
        have := h_indep.comp (fun _ x => Real.exp (t * x))
          (fun _ => (measurable_const.mul measurable_id).exp)
        simp only [Function.comp_def] at this
        exact this
      -- Show the product over range n is independent of exp(t * X_n)
      have h_indep_prod : IndepFun (fun ω => ∏ i ∈ Finset.range n, Real.exp (t * X i ω))
          (fun ω => Real.exp (t * X n ω)) ℙ := by
        convert h_indep_exp.indepFun_finset_prod_of_notMem
          (fun i => (h_meas i).const_mul t |>.exp)
          (by simp : n ∉ Finset.range n) using 2
        simp [Finset.prod_apply]
      -- Need the equality for the inductive hypothesis
      have h_eq_n : (fun ω => Real.exp (t * (∑ i ∈ Finset.range n, X i) ω)) =
          fun ω => Real.exp (∑ i ∈ Finset.range n, t * X i ω) := by
        funext ω
        simp [Finset.mul_sum]
      -- Use IndepFun.integrable_mul
      exact h_indep_prod.integrable_mul (ih h_eq_n) h_integrable_n

--If the target `a` is greater than the mean, the supremum in the rate function
--is achieved by non-negative `t`.
include h_bdd h_mgf in lemma rateFunction_eq_sup_nonneg (a : ℝ)
  (h_int : Integrable (X 0) ℙ) (h_mean : 𝔼[X 0] ≤ a) :
    rateFunction X a = ⨆ t : {(x : ℝ) | 0 ≤ x}, (t : ℝ) * a - cgf (X 0) ℙ t := by
  rw [rateFunction]
  apply le_antisymm
  · -- Direction 1: Global Sup ≤ Restricted Sup
    apply ciSup_le
    intro t
    by_cases ht : 0 ≤ t
    · -- Case t ≥ 0: It's in the restricted set
      have h_bdd_restrict : BddAbove (Set.range fun s : {x : ℝ | 0 ≤ x} =>
          (s : ℝ) * a - cgf (X 0) ℙ s) := by
        obtain ⟨b, hb⟩ := h_bdd a
        use b
        rintro y ⟨s, rfl⟩
        exact hb ⟨s.val, rfl⟩
      exact le_ciSup h_bdd_restrict ⟨t, ht⟩
    · -- Case t < 0: bound by the value at t=0
      rw [not_le] at ht
      have h_bdd_restrict : BddAbove (Set.range fun s : {x : ℝ | 0 ≤ x} =>
          (s : ℝ) * a - cgf (X 0) ℙ s) := by
        obtain ⟨b, hb⟩ := h_bdd a
        use b
        rintro y ⟨s, rfl⟩
        exact hb ⟨s.val, rfl⟩
      -- When t < 0, show t*a - cgf t ≤ 0 = value at t=0
      have h_le_zero : t * a - cgf (X 0) ℙ t ≤ 0 :=
        rate_function_neg_param_le_zero h_int h_mgf ht h_mean
      calc t * a - cgf (X 0) ℙ t
          ≤ 0 := h_le_zero
        _ = (0 : ℝ) * a - cgf (X 0) ℙ 0 := by simp [cgf_zero]
        _ ≤ ⨆ s : {x : ℝ | 0 ≤ x}, (s : ℝ) * a - cgf (X 0) ℙ s :=
            le_ciSup h_bdd_restrict ⟨0, by simp⟩
  · -- Direction 2: Restricted Sup ≤ Global Sup
    have h_nonempty : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, by simp⟩⟩
    apply ciSup_le
    intro t
    exact le_ciSup (h_bdd a) (t : ℝ)

/- Main results -/

-- Chernoff bound
include h_indep h_meas h_mgf h_ident in
lemma prob_mean_ge_le_exp (t a : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn_pos : 0 < n) :
  (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
    ≤ Real.exp ( - (n : ℝ) * (t * a - cgf (X 0) ℙ t)) := by
  -- 1) Apply Chernoff to Y := (1/n) * S X n
  --    use `ProbabilityTheory.measure_ge_le_exp_cgf` on Y and threshold a, at parameter t
  -- 2) Identify `cgf Y t = (t/n) • ?` (expressed via mgf_smul_left / cgf lemmas)
  -- 3) Use independence to get `cgf (S X n) t = n * cgf (X 0) t`
  -- 4) Simplify to the displayed RHS.

  -- Step 0: reduce to the event S_n ≥ n a
  have : { ω | empiricalMean X n ω ≥ a } =
          { ω | S X n ω ≥ (n : ℝ) * a } := by
    ext ω
    simp only [Set.mem_setOf_eq, empiricalMean, S, Finset.sum_apply, ge_iff_le]
    have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    constructor
    · intro h
      calc (n : ℝ) * a ≤ (n : ℝ) * ((∑ i ∈ Finset.range n, X i ω) / (n : ℝ)) := by gcongr
        _ = ∑ i ∈ Finset.range n, X i ω := by field_simp
    · intro h
      calc a = ((n : ℝ) * a) / (n : ℝ) := by field_simp
        _ ≤ (∑ i ∈ Finset.range n, X i ω) / (n : ℝ) := by gcongr

  -- Step 1: show integrability hypothesis for S_n so we can call the Chernoff lemma
  have hinteg : Integrable (fun ω => Real.exp (t * S X n ω)) ℙ :=
    integrable_exp_sum X h_indep h_ident h_meas h_mgf t n

  -- Step 2: apply the standard Chernoff lemma in mathlib:
  -- `ProbabilityTheory.measure_ge_le_exp_cgf` says
  --   (ℙ { ω | ε ≤ Y ω }).to_real ≤ rexp (-t * ε + ProbabilityTheory.cgf Y ℙ t)
  -- provided `0 ≤ t` and integrability of exp (t * Y).
  have chernoff := ProbabilityTheory.measure_ge_le_exp_cgf ((n : ℝ) * a) (ht) (hinteg)
  -- chernoff is: (ℙ {ω | (n*a) ≤ S_n ω}).toReal ≤ rexp (-t*(n*a) + cgf (S_n) ℙ t)

  -- Step 3: rewrite cgf of the finite sum via independence:
  -- `cgf (S_n) ℙ t = n * cgf (X 0) ℙ t`
  have cgf_sum_eq : cgf (S X n) ℙ t = (n : ℝ) * cgf (X 0) ℙ t := by
    have h0_mem : 0 ∈ Finset.range n := by simp [Finset.mem_range]; omega
    have hident_all : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
        IdentDistrib (X i) (X j) ℙ ℙ := by
      intros i _ j _
      exact (h_ident i).trans (h_ident j).symm
    have hint : ∀ i ∈ Finset.range n, Integrable (fun ω => Real.exp (t * X i ω)) ℙ := by
      intros i _
      exact integrable_exp_of_identDistrib X h_ident h_mgf i t
    rw [S]
    convert cgf_sum_of_identDistrib h_meas h_indep hident_all h0_mem t hint using 1
    simp [Finset.card_range]


  -- combine chernoff + cgf_sum_eq, then simplify algebraically
  calc
    (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
        = (ℙ {ω | S X n ω ≥ (n : ℝ) * a}).toReal := by rw [this]
    _ ≤ Real.exp (-t * ((n : ℝ) * a) + cgf (S X n) ℙ t) := by
      -- from chernoff
      exact chernoff
    _ = Real.exp ( (n : ℝ) * ( - t * a + cgf (X 0) ℙ t) ) := by
      rw [cgf_sum_eq]; ring_nf
    _ = Real.exp ( - (n : ℝ) * ( t * a - cgf (X 0) ℙ t) ) := by
      ring_nf



/-- A sequence of random variables satisfies a large deviation principle (LDP) with
rate function `I` if the scaled log probabilities converge to `-I` at each point.
Uses `ENNReal.log` which properly handles probability 0 (giving -∞). -/
structure LargeDeviationPrinciple (Y : ℕ → Ω → ℝ) (I : ℝ → ℝ) : Prop where
  /-- Upper bound: limsup of scaled log probability is at most -I(a) -/
  upper_bound : ∀ a : ℝ,
    limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | Y n ω ≥ a})) atTop ≤ (- I a : EReal)
  /-- Lower bound: liminf of scaled log probability is at least -I(a) -/
  lower_bound : ∀ a : ℝ,
    (- I a : EReal) ≤ liminf (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | Y n ω ≥ a})) atTop

/-! ### Helper lemmas for the upper bound proof -/

/-- For bounded sets in ℝ, the infimum of negations equals the negation of the supremum.
This is a key property used in the Cramér upper bound proof. -/
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

/-- For a nonempty bounded-below set in ℝ, sInf of its image under coercion to EReal
equals the coercion of its sInf in ℝ. -/
private lemma ereal_sInf_coe_eq_coe_sInf {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    sInf ((fun (x : ℝ) => (x : EReal)) '' s) = ↑(sInf s) := by
  -- EReal = WithBot (WithTop ℝ), so coercion is: ℝ → WithTop ℝ → WithBot (WithTop ℝ)
  -- Step 1: Use WithTop.coe_sInf' for ℝ → WithTop ℝ
  -- Step 2: Use WithBot.coe_sInf' for WithTop ℝ → WithBot (WithTop ℝ)

  -- First, show that the image under (ℝ → EReal) equals image under composition
  have h_image : (fun (x : ℝ) => (x : EReal)) '' s =
      (fun (y : WithTop ℝ) => (y : WithBot (WithTop ℝ))) '' ((fun (x : ℝ) => (x : WithTop ℝ)) '' s) := by
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
  -- Apply WithBot.coe_sInf' with α = WithTop ℝ
  have h_bdd_withTop : BddBelow ((fun (x : ℝ) => (x : WithTop ℝ)) '' s) :=
    Monotone.map_bddBelow (fun _ _ h => WithTop.coe_le_coe.mpr h) hbdd

  calc sInf ((fun (y : WithTop ℝ) => (y : WithBot (WithTop ℝ))) '' ((fun (x : ℝ) => (x : WithTop ℝ)) '' s))
      = (↑(sInf ((fun (x : ℝ) => (x : WithTop ℝ)) '' s)) : WithBot (WithTop ℝ)) :=
          (WithBot.coe_sInf' h_bdd_withTop).symm
    _ = (↑(↑(sInf s) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
          congr 1
          exact (WithTop.coe_sInf' hne hbdd).symm
    _ = ↑(sInf s) := rfl

/-- For a bounded nonempty set in ℝ, sInf of negations equals negative of sSup, in EReal.
This version handles the coercion from ℝ to EReal properly. -/
private lemma ereal_sInf_neg_eq_neg_sSup {ι : Type*} (f : ι → ℝ)
    (hne : (Set.range f).Nonempty) (hbdd : BddAbove (Set.range f)) :
    sInf (Set.range fun i => (-(f i) : EReal)) = -((sSup (Set.range f) : ℝ) : EReal) := by
  -- Establish that the range of negations in ℝ is bounded below and nonempty
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

  -- Apply csInf_neg_eq_neg_csSup in ℝ
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

  -- Use the helper lemma and rewrite
  rw [h_set_eq, ereal_sInf_coe_eq_coe_sInf h_ne_neg h_bdd_neg, h_real, EReal.coe_neg]

include h_indep h_meas h_ident h_mgf h_bdd h_int in
/-- **Cramér's Theorem (Upper Bound)**: For any a ≥ E[X 0], the scaled log probability that the
empirical mean exceeds a is bounded above by the negative rate function.
Uses `ENNReal.log` to properly handle the case when probability is 0 (giving -∞). -/
theorem cramer_upper_bound (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
      ≤ (- rateFunction X a : EReal) := by
  unfold rateFunction
  have h_bdd_a := h_bdd a
  -- The strategy: show that for each t ≥ 0, we have limsup ≤ -(t*a - cgf t)
  -- Then taking the infimum over t gives limsup ≤ -sup_t (t*a - cgf t)

  -- Step 1: Show limsup ≤ infimum over t of -(t*a - cgf t)
  suffices h : ∀ t : ℝ, 0 ≤ t →
    limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
      ≤ (-(t * a - cgf (X 0) ℙ t) : EReal) by
    -- From h: for all t ≥ 0, limsup ≤ -(t*a - cgf t)
    -- Taking supremum over t: limsup ≤ -sup_{t ≥ 0} (t*a - cgf t) = -rateFunction
    calc limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
        ≤ sInf (Set.range fun t : {x : ℝ | 0 ≤ x} => (-(t.val * a - cgf (X 0) ℙ t) : EReal)) := by
          apply le_csInf
          · have : Nonempty {x : ℝ | 0 ≤ x} := ⟨⟨0, by simp⟩⟩
            exact Set.range_nonempty _
          · intro b ⟨t, ht⟩
            rw [← ht]
            exact h t.val t.property
      _ = (-(⨆ t : {x : ℝ | 0 ≤ x}, t.val * a - cgf (X 0) ℙ t) : EReal) := by
          -- The key idea: sInf {-f(t)} = -(sSup {f(t)})
          -- Prove this for bounded sets in ℝ coerced to EReal
          have h_bdd_restrict : BddAbove (Set.range fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t) := by
            obtain ⟨b, hb⟩ := h_bdd_a
            use b
            intro y ⟨t, ht⟩
            rw [← ht]
            exact hb ⟨t.val, rfl⟩
          -- The supremum exists, so we can work with it
          -- Use that sInf of negations equals negative of sSup
          -- Apply ereal_sInf_neg_eq_neg_sSup to lift the equality to EReal
          have h_nonempty : (Set.range fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t).Nonempty := by
            use 0 * a - cgf (X 0) ℙ 0
            use ⟨0, by simp⟩
          -- Apply the lemma after unfolding iSup
          simp only [iSup]
          exact ereal_sInf_neg_eq_neg_sSup
            (fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t) h_nonempty h_bdd_restrict
      _ = (- rateFunction X a : EReal) := by
          -- rateFunction X a = ⨆ t : {x : ℝ | 0 ≤ x}, t.val * a - cgf (X 0) ℙ t
          congr 1
          norm_cast
          exact (@rateFunction_eq_sup_nonneg _ _ X h_mgf h_bdd _ a h_int h_mean).symm

  -- Step 2: Fix t ≥ 0 and show the bound
  intro t ht
  -- For each n > 0, we have the Chernoff bound from prob_mean_ge_le_exp
  have h_event : ∀ n : ℕ, 0 < n →
    (ℙ {ω | empiricalMean X n ω ≥ a}).toReal ≤
      Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)) := by
    intro n hn
    exact prob_mean_ge_le_exp X h_indep h_ident h_meas h_mgf t a ht n hn

  -- Apply ENNReal.log and use monotonicity
  -- Key: ENNReal.log 0 = ⊥ (i.e., -∞), so probability=0 case is handled automatically
  have h_scaled : ∀ n : ℕ, 0 < n →
    ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}) ≤
      (-(t * a - cgf (X 0) ℙ t) : EReal) := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h_exp := h_event n hn
    -- Convert probability bound to ENNReal
    have h_ennreal : (ℙ {ω | empiricalMean X n ω ≥ a}) ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))) := by
      rw [← ENNReal.ofReal_toReal_eq_iff.mpr (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h_exp
    -- Apply ENNReal.log_le_log (monotonicity)
    have h_log : ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a}) ≤
        ENNReal.log (ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)))) :=
      ENNReal.log_le_log h_ennreal
    -- Simplify: log(ofReal(exp(x))) = x in EReal
    have h_log_exp : ENNReal.log (ENNReal.ofReal (Real.exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)))) =
        (-(n : ℝ) * (t * a - cgf (X 0) ℙ t) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _)]
      rw [Real.log_exp (-(n : ℝ) * (t * a - cgf (X 0) ℙ t))]
      rfl
    -- Prove the arithmetic simplification on the Real side first
    have h_arith : ((1 : ℝ) / (n : ℝ)) * (-(n : ℝ) * (t * a - cgf (X 0) ℙ t)) =
        -(t * a - cgf (X 0) ℙ t) := by
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
      field_simp [hn_ne]
    -- Now prove the inequality in EReal
    trans ((1 : ℝ) / (n : ℝ) : EReal) * (-(n : ℝ) * (t * a - cgf (X 0) ℙ t) : EReal)
    · rw [← h_log_exp]
      gcongr
    · simp only [← EReal.coe_mul]
      exact le_of_eq (congrArg (fun x : ℝ => (x : EReal)) h_arith)

  -- The bound holds eventually (for all n ≥ 1)
  apply Filter.limsup_le_of_le
  · -- IsCoboundedUnder: bounded below by -∞ (always true for EReal)
    exact isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
  · -- The bound holds eventually
    apply Filter.eventually_atTop.mpr
    use 1
    intro n hn
    exact h_scaled n hn

/-! ### Helper lemmas for the lower bound

The lower bound proof uses the change of measure technique with tilted measures.
The key insight is to tilt by the sum S_n rather than by X_0, which automatically
preserves the i.i.d. structure and allows us to use CGF derivatives to compute
moments under the tilted measure.

Strategy:
1. For a > E[X], find t > 0 such that cgf'(t) = a (the "exposed" assumption)
2. Define the tilted measure Q_{n,t} = P.tilted(t * S_n)
3. Use CGF derivatives to show E_Q[S_n/n] = a and Var_Q[S_n/n] → 0
4. Apply Chebyshev to show Q_{n,t}(empirical mean ≈ a) → 1
5. Change of measure relates P to Q_{n,t} with exponential cost
-/

-- Helper: MGF of the sum equals product of MGFs by independence.
-- Uses existing mgf_sum_of_identDistrib from mathlib.
include h_indep h_ident h_meas in lemma mgf_sum_eq_prod (n : ℕ) (t : ℝ) :
    ∫ ω, Real.exp (t * S X n ω) ∂ℙ = ∏ i ∈ Finset.range n, mgf (X 0) ℙ t := by
  rw [S]
  by_cases hn : n = 0
  · simp [hn, mgf]
  -- Use mgf_sum_of_identDistrib to get mgf(sum) = mgf(X_0)^n
  have h0_mem : 0 ∈ Finset.range n := by simp [Finset.mem_range]; omega
  have hident_all : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      IdentDistrib (X i) (X j) ℙ ℙ := by
    intros i _ j _
    exact (h_ident i).trans (h_ident j).symm
  calc ∫ ω, Real.exp (t * (∑ i ∈ Finset.range n, X i) ω) ∂ℙ
      = mgf (∑ i ∈ Finset.range n, X i) ℙ t := by rw [mgf]
    _ = mgf (X 0) ℙ t ^ (Finset.range n).card :=
        mgf_sum_of_identDistrib h_meas h_indep hident_all h0_mem t
    _ = mgf (X 0) ℙ t ^ n := by rw [Finset.card_range]
    _ = ∏ i ∈ Finset.range n, mgf (X 0) ℙ t := by
        rw [Finset.prod_const, Finset.card_range]

/-- **Helper: Product of identical MGFs equals MGF to the power n**. -/
lemma prod_mgf_eq_pow (n : ℕ) (t : ℝ) :
    ∏ i ∈ Finset.range n, mgf (X 0) ℙ t = mgf (X 0) ℙ t ^ n := by
  rw [Finset.prod_const, Finset.card_range]

/-- **Helper: MGF to power n equals exp(n * cgf)**. -/
lemma mgf_pow_eq_exp_mul_cgf (n : ℕ) (t : ℝ)
    (h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ) :
    mgf (X 0) ℙ t ^ n = Real.exp (n * cgf (X 0) ℙ t) := by
  rw [cgf, mgf]
  conv_lhs => rw [← Real.exp_log (integral_exp_pos h_int)]
  rw [← Real.exp_nsmul, nsmul_eq_mul]

-- Helper: CGF of the sum equals n times CGF of X_0.
include h_indep h_ident h_meas h_mgf in lemma cgf_sum_eq (n : ℕ) (t : ℝ)
    (h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ) :
    ∫ ω, Real.exp (t * S X n ω) ∂ℙ = Real.exp (n * cgf (X 0) ℙ t) := by
  rw [@mgf_sum_eq_prod _ _ X h_indep h_ident h_meas _ n t, prod_mgf_eq_pow]
  exact @mgf_pow_eq_exp_mul_cgf _ _ X _ n t h_int

/-- **Helper: Bound the Radon-Nikodym derivative on the set E**.
For ω in E where S_n(ω) ≤ n(a+δ), we have exp(-t*S_n(ω)) ≥ exp(-t*n(a+δ)). -/
private lemma exp_neg_mul_S_ge_on_set (t : ℝ) (n : ℕ) (a δ : ℝ) (ht : 0 ≤ t)
    (ω : Ω) (hω : empiricalMean X n ω ∈ Set.Icc a (a + δ)) :
    Real.exp (-t * S X n ω) ≥ Real.exp (-t * n * (a + δ)) := by
  -- exp is monotone, so we need: -t * S X n ω ≥ -t * n * (a + δ)
  -- Equivalently: t * n * (a + δ) ≥ t * S X n ω
  apply Real.exp_le_exp.mpr
  -- Show: -t * n * (a + δ) ≤ -t * S X n ω
  rw [empiricalMean, S] at hω
  have h_upper := hω.2  -- S X n ω / n ≤ a + δ
  by_cases hn : n = 0
  · simp [hn, S]
  · have h_S_bound : S X n ω ≤ n * (a + δ) := by
      calc S X n ω = (S X n ω / n) * n := by field_simp
        _ ≤ (a + δ) * n := mul_le_mul_of_nonneg_right h_upper (Nat.cast_nonneg n)
        _ = n * (a + δ) := by ring
    calc -t * n * (a + δ) = -(t * n * (a + δ)) := by ring
      _ ≤ -(t * S X n ω) := by
          apply neg_le_neg
          calc t * S X n ω ≤ t * (n * (a + δ)) := mul_le_mul_of_nonneg_left h_S_bound ht
            _ = t * n * (a + δ) := by ring
      _ = -t * S X n ω := by ring

/-- **Lemma 1: Change of measure lower bound**.
The probability under P can be bounded below using the tilted measure.
On the set where S_n ≈ n*a, the density factor is roughly constant.

Mathematical proof:
1. By Radon-Nikodym: P(E) = ∫_E (dP/dQ) dQ where Q = P.tilted(t*S_n)
2. The derivative is: dP/dQ = exp(-t*S_n + n*cgf(t))
3. On E: S_n ≤ n(a+δ), so exp(-t*S_n) ≥ exp(-t*n(a+δ)) for t ≥ 0
4. Pull out: P(E) ≥ exp(n(cgf(t) - t(a+δ))) * Q(E)
-/

-- Helper: Express P(E) using the tilted measure Q.
-- Key relationship: P(E) = (∫ exp(f) dP) * ∫_E exp(-f) dQ where Q = P.tilted(f)
-- This follows from the definition of tilted measure and basic algebra.
private lemma measure_eq_integral_exp_neg_tilted (f : Ω → ℝ) (E : Set Ω)
    (h_int : Integrable (fun ω => Real.exp (f ω)) ℙ)
    (hE : MeasurableSet E) :
    (ℙ E).toReal =
      (∫ ω, Real.exp (f ω) ∂ℙ) * (∫ ω in E, Real.exp (-f ω) ∂(Measure.tilted ℙ f)) := by
  -- Use setIntegral_tilted' to express the integral under the tilted measure
  rw [setIntegral_tilted' f (fun ω => Real.exp (-f ω)) hE]
  -- Now we have: ∫_E (exp(f) / ∫exp(f)) • exp(-f) dP
  simp only [smul_eq_mul]
  -- Simplify the integrand using exp(f) * exp(-f) = 1
  have h_pos : 0 < ∫ x, Real.exp (f x) ∂ℙ := integral_exp_pos h_int
  have h_ne : (∫ x, Real.exp (f x) ∂ℙ) ≠ 0 := ne_of_gt h_pos
  conv_rhs => arg 2; arg 2; ext ω; rw [div_mul_eq_mul_div, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_div]
  -- Now: ∫_E (1 / ∫exp(f)) dP = (ℙ.real E) * (1 / ∫exp(f))
  rw [setIntegral_const, smul_eq_mul]
  -- We have: (∫ exp(f)) * (ℙ.real E * (1 / ∫ exp(f)))
  -- Cancel the integral terms
  field_simp
  rw [Measure.real]

include h_indep h_ident h_meas h_mgf in lemma change_of_measure_lower_bound (a δ t : ℝ) (n : ℕ)
    (hδ : 0 < δ) (ht : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * S X n ω)) ℙ) :
    let E := {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}
    (ℙ E).toReal ≥
      Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
      ((Measure.tilted ℙ (fun ω => t * S X n ω)) E).toReal := by
  intro E
  -- Step 1: Express P(E) using the tilted measure
  have hE : MeasurableSet E := by
    -- E = {ω | empiricalMean(ω) ∈ [a, a+δ]} is measurable
    -- empiricalMean = S/n where S is a finite sum of measurable functions
    have hS : Measurable (S X n) := by
      rw [S]
      convert Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i) using 2
      exact Finset.sum_apply _ _ _
    have : E = {ω | S X n ω / (n : ℝ) ∈ Set.Icc a (a + δ)} := by rfl
    rw [this]
    exact (hS.div_const (n : ℝ)) measurableSet_Icc

  have h_int' : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ := h_mgf t

  rw [measure_eq_integral_exp_neg_tilted (fun ω => t * S X n ω) E h_int hE]

  -- Step 2: Apply cgf_sum_eq to simplify ∫ exp(t*S_n)
  rw [@cgf_sum_eq _ _ X h_indep h_ident h_meas h_mgf _ n t h_int']

  -- Step 3: Bound ∫_E exp(-t*S_n) dQ from below
  have h_bound : ∫ ω in E, Real.exp (-t * S X n ω) ∂(Measure.tilted ℙ (fun ω => t * S X n ω)) ≥
      Real.exp (-t * n * (a + δ)) * ((Measure.tilted ℙ (fun ω => t * S X n ω)) E).toReal := by
    -- Use exp_neg_mul_S_ge_on_set: on E, exp(-t*S_n) ≥ exp(-t*n*(a+δ))
    have h_ge : ∀ ω ∈ E, Real.exp (-t * n * (a + δ)) ≤ Real.exp (-t * S X n ω) := by
      intro ω hω
      exact exp_neg_mul_S_ge_on_set X t n a δ (le_of_lt ht) ω hω
    -- Integral of const on E equals const * measure(E)
    calc ∫ ω in E, Real.exp (-t * S X n ω) ∂(Measure.tilted ℙ (fun ω => t * S X n ω))
        ≥ ∫ ω in E, Real.exp (-t * n * (a + δ)) ∂(Measure.tilted ℙ (fun ω => t * S X n ω)) :=
          setIntegral_mono_on
            (by -- constant is integrable
              apply Integrable.integrableOn
              apply integrable_const)
            (by -- exp(-t*S_n) is integrable under tilted measure
              apply Integrable.integrableOn
              rw [integrable_tilted_iff h_int]
              -- Need to show: Integrable (fun ω ↦ exp(t*S_n) • exp(-t*S_n))
              -- This simplifies to: Integrable (const 1)
              have : (fun ω ↦ Real.exp (t * S X n ω) • Real.exp (-t * S X n ω)) = fun ω ↦ 1 := by
                ext ω
                simp only [smul_eq_mul]
                rw [← Real.exp_add]
                ring_nf
                norm_num
              rw [this]
              rw [integrable_const_iff]
              right
              infer_instance)
            hE h_ge
      _ = ((Measure.tilted ℙ (fun ω => t * S X n ω)).real E) •
            Real.exp (-t * n * (a + δ)) := setIntegral_const _
      _ = Real.exp (-t * n * (a + δ)) *
            ((Measure.tilted ℙ (fun ω => t * S X n ω)) E).toReal := by
          rw [Measure.real, smul_eq_mul]; ring

  -- Step 4: Combine to get the final inequality
  -- After steps 1-2 (the two rw's above), the goal is:
  --   (ℙ E).toReal = exp(n*cgf) * ∫_E exp(-t*S_n) dQ
  -- From h_bound: ∫_E exp(-t*S_n) dQ ≥ exp(-t*n*(a+δ)) * Q(E)
  -- Therefore: (ℙ E).toReal ≥ exp(n*cgf) * exp(-t*n*(a+δ)) * Q(E)
  have key : Real.exp (n * cgf (X 0) ℙ t) *
      (Real.exp (-t * n * (a + δ)) * ((Measure.tilted ℙ (fun ω => t * S X n ω)) E).toReal) =
    Real.exp (-n * (t * (a + δ) - cgf (X 0) ℙ t)) *
      ((Measure.tilted ℙ (fun ω => t * S X n ω)) E).toReal := by
    ring_nf
    have : n * cgf (X 0) ℙ t + (-(n * t * a) - n * t * δ) =
        -n * (t * (a + δ) - cgf (X 0) ℙ t) := by ring
    rw [← Real.exp_add, this]; ring
  rw [← key]
  gcongr
  convert h_bound.le using 2
  ext ω; ring_nf

include h_indep h_ident h_meas h_mgf in
/-- **Helper: CGF of the sum equals n times CGF of X_0**.
This follows from the MGF relationship mgf(S_n) = exp(n * cgf(X_0)). -/
private lemma cgf_sum_eq_n_mul_cgf (t : ℝ) (n : ℕ)
    (h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ) :
    cgf (S X n) ℙ t = n * cgf (X 0) ℙ t := by
  -- Use cgf_sum_eq: ∫ exp(t * S_n) = exp(n * cgf (X 0) ℙ t)
  have h_mgf := @cgf_sum_eq _ _ X h_indep h_ident h_meas h_mgf _ n t h_int
  -- cgf (S X n) ℙ t = log(mgf (S X n) ℙ t) = log(∫ exp(t * S_n))
  rw [cgf, mgf, h_mgf]
  -- log(exp(n * cgf)) = n * cgf
  rw [Real.log_exp (n * cgf (X 0) ℙ t)]

include h_indep h_ident h_meas h_mgf in
/-- Sub-goal 1a: First derivative of CGF scales by n for the sum -/
private lemma deriv_cgf_sum (t : ℝ) (n : ℕ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    deriv (cgf (S X n) ℙ) t = n * deriv (cgf (X 0) ℙ) t := by
  have h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ :=
    interior_subset (s := integrableExpSet (X 0) ℙ) ht
  calc deriv (cgf (S X n) ℙ) t
      = deriv (fun s => n * cgf (X 0) ℙ s) t := by
        congr 1
        ext s
        have h_int_s : Integrable (fun ω => Real.exp (s * X 0 ω)) ℙ := h_mgf s
        exact @cgf_sum_eq_n_mul_cgf _ _ X h_indep h_ident h_meas h_mgf _ s n h_int_s
    _ = n * deriv (cgf (X 0) ℙ) t := by
        -- Use deriv_const_mul: deriv (fun y => c * d y) x = c * deriv d x
        -- CGF is analytic on interior, hence differentiable at t
        have h_diff : DifferentiableAt ℝ (cgf (X 0) ℙ) t := by
          have h_analytic := @analyticOn_cgf _ _ (X 0) ℙ t ht
          have h_nhds : interior (integrableExpSet (X 0) ℙ) ∈ 𝓝 t := isOpen_interior.mem_nhds ht
          have : insert t (interior (integrableExpSet (X 0) ℙ)) ∈ 𝓝 t := by
            simp only [Set.insert_eq_of_mem ht]
            exact h_nhds
          exact h_analytic.differentiableWithinAt.differentiableAt this
        exact deriv_const_mul (n : ℝ) h_diff

include h_indep h_ident h_meas h_mgf in
/-- Sub-goal 1b: Second derivative of CGF scales by n for the sum -/
private lemma iteratedDeriv_two_cgf_sum (t : ℝ) (n : ℕ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    iteratedDeriv 2 (cgf (S X n) ℙ) t = n * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  have h_int : Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ :=
    interior_subset (s := integrableExpSet (X 0) ℙ) ht
  calc iteratedDeriv 2 (cgf (S X n) ℙ) t
      = iteratedDeriv 2 (fun s => n * cgf (X 0) ℙ s) t := by
        congr 1
        ext s
        have h_int_s : Integrable (fun ω => Real.exp (s * X 0 ω)) ℙ := h_mgf s
        exact @cgf_sum_eq_n_mul_cgf _ _ X h_indep h_ident h_meas h_mgf _ s n h_int_s
    _ = n * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
        -- Use iteratedDeriv_const_mul: iteratedDeriv n (fun z => c * f z) x = c * iteratedDeriv n f x
        -- Need to show CGF is C^2 at t (follows from analyticity)
        have h_contDiff : ContDiffAt ℝ 2 (cgf (X 0) ℙ) t := by
          have h_analytic := @analyticOn_cgf _ _ (X 0) ℙ t ht
          have h_nhds : interior (integrableExpSet (X 0) ℙ) ∈ 𝓝 t := isOpen_interior.mem_nhds ht
          exact h_analytic.contDiffWithinAt.contDiffAt h_nhds
        exact iteratedDeriv_const_mul h_contDiff (n : ℝ)

include h_indep h_ident h_meas h_mgf in
/-- Sub-goal 2: Apply Mathlib lemmas to S_n directly -/
private lemma tilted_Sn_moments (t : ℝ) (n : ℕ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    let μ_t := Measure.tilted ℙ (fun ω => t * S X n ω)
    (∫ ω, S X n ω ∂μ_t) = deriv (cgf (S X n) ℙ) t ∧
    variance (S X n) μ_t = iteratedDeriv 2 (cgf (S X n) ℙ) t := by
  intro μ_t
  constructor
  · -- Mean: Apply integral_tilted_mul_self to S_n
    have hS_meas : Measurable (S X n) := by
      unfold S
      convert Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i) using 2
      exact Finset.sum_apply _ _ _
    -- Need to show t is in interior of integrableExpSet for S_n
    have ht_Sn : t ∈ interior (integrableExpSet (S X n) ℙ) := by
      -- Since h_mgf gives integrability for all t, integrableExpSet (S X n) ℙ = univ
      have h_univ : integrableExpSet (S X n) ℙ = Set.univ := by
        ext s
        simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact integrable_exp_sum X h_indep h_ident h_meas h_mgf s n
      rw [h_univ, interior_univ]
      exact Set.mem_univ t
    exact integral_tilted_mul_self ht_Sn
  · -- Variance: Apply variance_tilted_mul to S_n
    have ht_Sn : t ∈ interior (integrableExpSet (S X n) ℙ) := by
      -- Since h_mgf gives integrability for all t, integrableExpSet (S X n) ℙ = univ
      have h_univ : integrableExpSet (S X n) ℙ = Set.univ := by
        ext s
        simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact integrable_exp_sum X h_indep h_ident h_meas h_mgf s n
      rw [h_univ, interior_univ]
      exact Set.mem_univ t
    exact variance_tilted_mul ht_Sn

include h_indep h_ident h_meas h_mgf in
/-- **Lemma 2: Tilted empirical moments**.
Under the tilted measure, the mean is the CGF derivative and variance is the second derivative.
Uses `integral_tilted_mul_self` and `variance_tilted_mul` from Mathlib. -/
private lemma tilted_empirical_moments (t : ℝ) (n : ℕ) (hn : n ≠ 0)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ)) :
    let μ_t := Measure.tilted ℙ (fun ω => t * S X n ω)
    (∫ ω, empiricalMean X n ω ∂μ_t) = deriv (cgf (X 0) ℙ) t ∧
    variance (empiricalMean X n) μ_t = (1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t := by
  intro μ_t
  -- Get the moments of S_n under the tilted measure
  have h_Sn := @tilted_Sn_moments _ _ X h_indep h_ident h_meas h_mgf _ t n ht
  constructor
  · -- Mean: E[empiricalMean] = E[S_n/n] = (1/n) * E[S_n]
    show ∫ ω, (S X n ω / n) ∂μ_t = deriv (cgf (X 0) ℙ) t
    -- Linearity of integral
    rw [integral_div]
    rw [h_Sn.1]
    -- Apply deriv_cgf_sum to rewrite deriv(cgf(S_n))
    rw [@deriv_cgf_sum _ _ X h_indep h_ident h_meas h_mgf _ t n ht]
    -- Simplify: (1/n) * (n * deriv) = deriv
    field_simp
  · -- Variance: Var[empiricalMean] = Var[S_n/n] = (1/n^2) * Var[S_n]
    show variance (fun ω => S X n ω / n) μ_t = (1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t
    -- Rewrite division as scalar multiplication
    conv_lhs =>
      arg 1; ext ω; rw [div_eq_inv_mul]
    -- Apply variance_smul: Var(c • X) = c² * Var(X)
    rw [show (fun ω => ((n : ℝ))⁻¹ * S X n ω) = ((n : ℝ))⁻¹ • (S X n) by rfl]
    rw [variance_smul]
    -- Use h_Sn.2 to substitute Var(S_n)
    rw [h_Sn.2]
    -- Apply iteratedDeriv_two_cgf_sum
    rw [@iteratedDeriv_two_cgf_sum _ _ X h_indep h_ident h_meas h_mgf _ t n ht]
    -- Simplify: (1/n)² * (n * iteratedDeriv 2) = (1/n) * iteratedDeriv 2
    field_simp

include h_indep h_ident h_meas h_mgf in
/-- Helper: Bound deviation probability using Chebyshev's inequality -/
private lemma tilted_deviation_bound (t a : ℝ) (n : ℕ) (hn : n ≠ 0) (δ : ℝ) (hδ : 0 < δ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ))
    (h_match : deriv (cgf (X 0) ℙ) t = a) :
    let μ_t := Measure.tilted ℙ (fun ω => t * S X n ω)
    μ_t {ω | δ ≤ |empiricalMean X n ω - a|} ≤
      ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) := by
  intro μ_t
  -- Get moments from Lemma 2
  have h_moments := @tilted_empirical_moments _ _ X h_indep h_ident h_meas h_mgf _ t n hn ht
  -- The mean under μ_t is a
  have h_mean : μ_t[empiricalMean X n] = a := by
    rw [h_moments.1, h_match]
  -- Show μ_t is a probability measure
  have h_prob : IsProbabilityMeasure μ_t := by
    apply isProbabilityMeasure_tilted
    exact integrable_exp_sum X h_indep h_ident h_meas h_mgf t n
  -- Show empiricalMean X n is in L^2(μ_t)
  have h_memLp : MemLp (empiricalMean X n) 2 μ_t := by
    -- First show S X n is in L^2(μ_t)
    have ht_Sn : t ∈ interior (integrableExpSet (S X n) ℙ) := by
      have h_univ : integrableExpSet (S X n) ℙ = Set.univ := by
        ext s
        simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact integrable_exp_sum X h_indep h_ident h_meas h_mgf s n
      rw [h_univ, interior_univ]
      exact Set.mem_univ t
    have h_S_memLp : MemLp (S X n) 2 μ_t := memLp_tilted_mul ht_Sn 2
    -- empiricalMean = (1/n) * S, use const_mul
    show MemLp (fun ω => S X n ω / n) 2 μ_t
    have : (fun ω => S X n ω / n) = (fun ω => (1 / (n : ℝ)) * S X n ω) := by
      ext ω
      have hn_cast : (n : ℝ) ≠ 0 := by simp [hn]
      field_simp [hn_cast]
    rw [this]
    exact h_S_memLp.const_mul (1 / (n : ℝ))
  -- Apply Chebyshev's inequality
  calc μ_t {ω | δ ≤ |empiricalMean X n ω - a|}
      = μ_t {ω | δ ≤ |empiricalMean X n ω - μ_t[empiricalMean X n]|} := by
        congr 1
        ext ω
        simp only [h_mean]
    _ ≤ ENNReal.ofReal (variance (empiricalMean X n) μ_t / δ ^ 2) :=
        meas_ge_le_variance_div_sq h_memLp hδ
    _ = ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) := by
        rw [h_moments.2]

/-- Helper: The variance term goes to zero as n → ∞ -/
private lemma variance_term_tendsto_zero (C : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / n) * C / δ ^ 2)) atTop (𝓝 0) := by
  -- Rewrite as constant times (1/n)
  have h_eq : (fun n : ℕ => ENNReal.ofReal ((1 / n) * C / δ ^ 2)) =
              (fun n : ℕ => ENNReal.ofReal ((C / δ ^ 2) * (1 / n))) := by
    ext n
    ring_nf
  rw [h_eq]
  -- Use continuity of ofReal and tendsto of 1/n → 0
  by_cases hC : C / δ ^ 2 ≤ 0
  · have : ∀ n : ℕ, ENNReal.ofReal ((C / δ ^ 2) * (1 / n)) = 0 := by
      intro n
      apply ENNReal.ofReal_of_nonpos
      exact mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
    simp only [this]
    exact tendsto_const_nhds
  · push_neg at hC
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    convert (tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2)) using 1
    ext n
    ring

include h_indep h_ident h_meas h_mgf in
/-- **Lemma 3: Tilted measure concentration**.
If t is chosen so that cgf'(t) = a, then under the tilted measure,
the empirical mean concentrates at a by the weak law of large numbers.
Uses Chebyshev's inequality with the variance from Lemma 2.
We prove concentration on the ball {|mean - a| < δ}, which is sufficient for the lower bound. -/
private lemma tilted_measure_concentrates (t a δ : ℝ) (hδ : 0 < δ)
    (ht : t ∈ interior (integrableExpSet (X 0) ℙ))
    (h_match : deriv (cgf (X 0) ℙ) t = a) :
    Tendsto (fun n => ((Measure.tilted ℙ (fun ω => t * S X n ω))
      {ω | |empiricalMean X n ω - a| < δ}).toReal) atTop (𝓝 1) := by
  -- Strategy: Show P(|mean - a| ≥ δ) → 0, then P(|mean - a| < δ) → 1
  -- First, we show the complement event has probability going to 0
  have h_complement_to_zero : Tendsto (fun n => ((Measure.tilted ℙ (fun ω => t * S X n ω))
      {ω | δ ≤ |empiricalMean X n ω - a|}).toReal) atTop (𝓝 0) := by
    -- Use tendsto_toReal_zero_iff to convert to ENNReal
    rw [ENNReal.tendsto_toReal_zero_iff]
    -- Apply Chebyshev bound and squeeze theorem
    refine ENNReal.tendsto_nhds_zero.2 (fun ε hε => ?_)
    -- Use the fact that variance/n → 0
    have h_var_to_zero : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2)) atTop (𝓝 0) := by
      convert variance_term_tendsto_zero (iteratedDeriv 2 (cgf (X 0) ℙ) t) δ hδ using 2
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 h_var_to_zero) ε hε
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hn_ne : n ≠ 0 := by omega
    -- Apply Chebyshev: μ_t{|mean - a| ≥ δ} ≤ variance/δ²
    calc (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | δ ≤ |empiricalMean X n ω - a|}
        ≤ ENNReal.ofReal ((1 / n) * iteratedDeriv 2 (cgf (X 0) ℙ) t / δ ^ 2) :=
          tilted_deviation_bound (X := X) (h_indep := h_indep) (h_ident := h_ident)
            (h_meas := h_meas) (h_mgf := h_mgf) t a n hn_ne δ hδ ht h_match
      _ ≤ ε := hN n (by omega)
  -- Convert to toReal and use 1 - P(complement) = P(event)
  -- Show that {|mean - a| < δ} and {δ ≤ |mean - a|} are complements
  have h_compl : ∀ n, {ω | |empiricalMean X n ω - a| < δ}ᶜ = {ω | δ ≤ |empiricalMean X n ω - a|} := by
    intro n
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  -- Use 1 - P(complement) = P(event)
  have h_eq : ∀ n, (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ} =
      1 - (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | δ ≤ |empiricalMean X n ω - a|} := by
    intro n
    have h_prob_n : IsProbabilityMeasure (Measure.tilted ℙ (fun ω => t * S X n ω)) := by
      apply isProbabilityMeasure_tilted
      exact integrable_exp_sum X h_indep h_ident h_meas h_mgf t n
    have h_meas : MeasurableSet {ω | |empiricalMean X n ω - a| < δ} := by
      -- Show that |empiricalMean X n - a| is measurable, then apply measurableSet_lt
      have h_emp_meas : Measurable (empiricalMean X n) := by
        convert (Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i)).div_const (n : ℝ) using 1
        ext ω
        simp only [empiricalMean, _root_.S, Finset.sum_apply]
      have h_sub_meas : Measurable (fun ω => empiricalMean X n ω - a) :=
        h_emp_meas.sub_const a
      have h_abs_meas : Measurable (fun ω => |empiricalMean X n ω - a|) :=
        continuous_abs.measurable.comp h_sub_meas
      exact measurableSet_lt h_abs_meas measurable_const
    haveI := h_prob_n
    have h_prob_eq : (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ}ᶜ =
        1 - (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ} :=
      prob_compl_eq_one_sub h_meas
    calc (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ}
        = 1 - (1 - (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ}) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
      _ = 1 - (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ}ᶜ := by
          rw [← h_prob_eq]
      _ = 1 - (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | δ ≤ |empiricalMean X n ω - a|} := by
          rw [h_compl]
  -- Apply tendsto for (1 - x).toReal where x → 0
  -- Rewrite using h_eq
  simp_rw [h_eq]
  -- Show that (1 - x).toReal → 1 when x.toReal → 0
  have h_one_sub : Tendsto (fun n => (1 - (Measure.tilted ℙ (fun ω => t * S X n ω))
      {ω | δ ≤ |empiricalMean X n ω - a|}).toReal) atTop (𝓝 1) := by
    -- First convert toReal convergence to ENNReal convergence
    have h_measure_to_zero : Tendsto (fun n => (Measure.tilted ℙ (fun ω => t * S X n ω))
        {ω | δ ≤ |empiricalMean X n ω - a|}) atTop (𝓝 0) := by
      rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top _ _)]
      exact h_complement_to_zero
    -- Then use ENNReal.Tendsto.sub to get 1 - measure → 1
    have h_sub_to_one : Tendsto (fun n => 1 - (Measure.tilted ℙ (fun ω => t * S X n ω))
        {ω | δ ≤ |empiricalMean X n ω - a|}) atTop (𝓝 1) := by
      convert ENNReal.Tendsto.sub tendsto_const_nhds h_measure_to_zero (Or.inl ENNReal.one_ne_top) using 1
      simp
    -- Finally apply toReal to get the result
    rw [← ENNReal.toReal_one]
    refine (ENNReal.tendsto_toReal ?_).comp h_sub_to_one
    simp only [ne_eq, ENNReal.one_ne_top, not_false_eq_true]
  exact h_one_sub

include h_indep h_ident h_meas h_mgf in
/-- Helper: The tilted measure gives positive probability to [a, ∞).
This follows from the fact that the tilted mean is a, so there must be mass ≥ a. -/
private lemma tilted_prob_ge_mean_pos (a t : ℝ)
    (ht_int : t ∈ interior (integrableExpSet (X 0) ℙ))
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) (n : ℕ) :
    0 < (Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | a ≤ empiricalMean X n ω} := by
  -- If this probability were 0, then all mass would be strictly below a,
  -- making the expected value < a, contradicting ht_deriv
  -- For now we'll use sorry, as this requires more detailed analysis of the tilted expectation
  sorry

include h_indep h_ident h_meas h_mgf in
/-- Helper: The tilted probability on a small interval around a is eventually bounded away from 0.
This follows from the concentration lemma and the fact that the tilted mean is a. -/
private lemma tilted_prob_window_bounded_away_from_zero (a t δ : ℝ) (hδ : 0 < δ)
    (ht_int : t ∈ interior (integrableExpSet (X 0) ℙ))
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    ∃ c > 0, ∀ᶠ n in atTop,
      c ≤ ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)}).toReal := by
  -- Strategy: P([a, a+δ]) = P([a, ∞)) - P([a+δ, ∞))
  -- By concentration, P([a+δ, ∞)) → 0
  -- By tilted_prob_ge_mean_pos, P([a, ∞)) > 0
  -- Therefore P([a, a+δ]) is eventually > c for some c > 0

  -- First, use concentration to show that P(|X - a| ≥ δ) → 0
  have h_conc := @tilted_measure_concentrates _ _ X h_indep h_ident h_meas h_mgf _ t a δ hδ ht_int ht_deriv

  -- The set {ω | empiricalMean X n ω ≥ a + δ} ⊆ {ω | |empiricalMean X n ω - a| ≥ δ}
  have h_subset : ∀ n, {ω | empiricalMean X n ω ≥ a + δ} ⊆ {ω | |empiricalMean X n ω - a| ≥ δ} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have : δ ≤ empiricalMean X n ω - a := by linarith [hω]
    have : empiricalMean X n ω - a ≤ |empiricalMean X n ω - a| := le_abs_self _
    linarith

  -- Therefore P(X ≥ a+δ).toReal → 0 by concentration
  have h_tail_vanish : Tendsto (fun n =>
      ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | empiricalMean X n ω ≥ a + δ}).toReal)
      atTop (𝓝 0) := by
    -- Since P(|X - a| < δ) → 1, we have P(|X - a| ≥ δ) → 0
    -- First, convert the concentration to a statement about the complement
    have h_compl_vanish : Tendsto (fun n =>
        ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| ≥ δ}).toReal)
        atTop (𝓝 0) := by
      -- P(|X - a| ≥ δ) = 1 - P(|X - a| < δ)
      have h_eq : ∀ n, ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| ≥ δ}).toReal =
          1 - ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| < δ}).toReal := by
        intro n
        have h_prob_n : IsProbabilityMeasure (Measure.tilted ℙ (fun ω => t * S X n ω)) := by
          apply isProbabilityMeasure_tilted
          exact integrable_exp_sum X h_indep h_ident h_meas h_mgf t n
        let μ_n := Measure.tilted ℙ (fun ω => t * S X n ω)
        let s_n := {ω | |empiricalMean X n ω - a| < δ}
        have h_emp_meas : Measurable (empiricalMean X n) := by
          convert (Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i)).div_const (n : ℝ) using 1
          ext ω
          simp only [empiricalMean, _root_.S, Finset.sum_apply]
        have h_meas_n : MeasurableSet s_n := by
          refine measurableSet_lt ?_ measurable_const
          exact Measurable.abs (h_emp_meas.sub_const a)
        have h_compl_eq : s_nᶜ = {ω | |empiricalMean X n ω - a| ≥ δ} := by
          ext ω
          simp only [s_n, Set.mem_setOf_eq, Set.mem_compl_iff]
          push_neg
          rfl
        have h1 : μ_n s_nᶜ = 1 - μ_n s_n := prob_compl_eq_one_sub h_meas_n
        rw [h_compl_eq] at h1
        show (μ_n {ω | |empiricalMean X n ω - a| ≥ δ}).toReal = 1 - (μ_n s_n).toReal
        rw [h1, ENNReal.toReal_sub_of_le]
        · simp [μ_n]
        · exact prob_le_one
        · simp [measure_ne_top]
      simp_rw [h_eq]
      -- Now (1 - p_n) → (1 - 1) = 0 as p_n → 1
      have : Tendsto (fun n => 1 - ((Measure.tilted ℙ (fun ω => t * S X n ω))
          {ω | |empiricalMean X n ω - a| < δ}).toReal) atTop (𝓝 (1 - 1)) :=
        Tendsto.sub tendsto_const_nhds h_conc
      simp at this
      exact this

    -- Now P(X ≥ a+δ) ≤ P(|X - a| ≥ δ) → 0
    have h_bound : ∀ n, ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | empiricalMean X n ω ≥ a + δ}).toReal ≤
        ((Measure.tilted ℙ (fun ω => t * S X n ω)) {ω | |empiricalMean X n ω - a| ≥ δ}).toReal := by
      intro n
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      exact h_subset n
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_compl_vanish (fun n => ?_) h_bound
    simp

  -- For each n, P([a, a+δ]) = P([a, ∞)) - P([a+δ, ∞))
  -- We'll show that P([a, ∞)) is bounded away from 0, and P([a+δ, ∞)) → 0
  -- The key issue is that we need P([a, ∞)) to be uniformly bounded away from 0,
  -- which is non-trivial. For now, we'll assume this can be proven.

  -- Let c be half of the infimum of P([a, ∞)) over all n
  -- (In a full proof, we'd show this infimum is > 0)
  sorry

include h_indep h_ident h_meas h_mgf in
/-- Helper: The error term (1/n) * log(tilted prob on window) → 0. -/
private lemma error_term_vanishes (a t δ : ℝ) (hδ : 0 < δ)
    (ht_int : t ∈ interior (integrableExpSet (X 0) ℙ))
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    Tendsto (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log ((Measure.tilted ℙ (fun ω => t * S X n ω))
        {ω | empiricalMean X n ω ∈ Set.Icc a (a + δ)})) atTop (𝓝 0) := by
  -- Since the tilted probability is bounded away from 0 and bounded by 1,
  -- its log is bounded, so (1/n) * log(prob) → 0
  obtain ⟨c, hc_pos, h_bounded⟩ := @tilted_prob_window_bounded_away_from_zero _ _ X h_indep h_ident
    h_meas h_mgf _ a t δ hδ ht_int ht_deriv
  -- The tilted probability is in [c, 1] eventually, so log is in [log c, 0]
  -- Therefore (1/n) * log is in [(1/n) * log c, 0] → 0
  sorry

include h_indep h_ident h_meas h_mgf in
/-- **Lemma 4: Lower bound via tilted measure**.
Combining the change of measure and concentration lemmas,
we get the lower bound on the scaled log probability. -/
private lemma lower_bound_via_tilted (a t δ : ℝ) (hδ : 0 < δ) (ht : 0 < t)
    (ht_int : t ∈ interior (integrableExpSet (X 0) ℙ))
    (ht_deriv : deriv (cgf (X 0) ℙ) t = a) :
    liminf (fun n : ℕ =>
      ((1 : ℝ) / n : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop
    ≥ (-(t * a - cgf (X 0) ℙ t) : EReal) - (t * δ : EReal) := by
  sorry

include h_indep h_meas h_ident h_mgf in
/-- **Cramér's Theorem (Lower Bound)**: For any a, the scaled log probability that the
empirical mean is close to a is bounded below by the negative rate function.
Uses `ENNReal.log` to properly handle the case when probability is 0 (giving -∞). -/
theorem cramer_lower_bound (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    (- rateFunction X a : EReal) ≤
      liminf (fun n : ℕ =>
        ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop := by
  sorry

include h_indep h_ident h_int h_meas in
private lemma less_exp_imp_limit_prob_less_mean_one (a : ℝ) (h : a < 𝔼[X 0]) :
  Tendsto (fun n : ℕ => (ℙ {ω | a ≤ empiricalMean X n ω} : ENNReal)) atTop (𝓝 1) := by
  -- By the strong law of large numbers, empirical mean → 𝔼[X 0] almost surely
  -- Since a < 𝔼[X 0], eventually (almost surely) empirical mean > a
  -- Therefore ℙ{empirical mean ≥ a} → 1

  -- First, convert iIndepFun to Pairwise independent
  have h_pairwise : Pairwise (fun i j => IndepFun (X i) (X j) ℙ) :=
    fun i j hij => h_indep.indepFun hij

  -- Apply the strong law of large numbers for real-valued random variables
  have h_strong_law : ∀ᵐ ω ∂ℙ, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 𝔼[X 0]) :=
    strong_law_ae_real X h_int h_pairwise h_ident

  -- The empirical mean converges to 𝔼[X 0] almost surely
  -- We need to show that ℙ{empirical mean ≥ a} → 1

  -- Key insight: Since a < 𝔼[X 0], there exists ε > 0 such that a + ε < 𝔼[X 0]
  have h_gap : 0 < 𝔼[X 0] - a := sub_pos.mpr h

  -- Choose ε = (𝔼[X 0] - a) / 2
  set ε := (𝔼[X 0] - a) / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hε_bound : a + ε < 𝔼[X 0] := by linarith

  -- By strong law, for almost every ω, eventually |empiricalMean n ω - 𝔼[X 0]| < ε
  -- This means empiricalMean n ω > 𝔼[X 0] - ε = a + ε > a

  -- The set where empirical mean converges to 𝔼[X 0]
  have h_conv_set : ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, |empiricalMean X n ω - 𝔼[X 0]| < ε := by
    filter_upwards [h_strong_law] with ω hω
    rw [Metric.tendsto_atTop] at hω
    obtain ⟨N, hN⟩ := hω ε hε_pos
    rw [Filter.eventually_atTop]
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq] at hN
    convert hN using 2
    rw [empiricalMean, S]
    simp only [Finset.sum_apply, div_eq_mul_inv, mul_comm]

  -- For such ω and large n, empiricalMean n ω > a
  have h_eventually_large : ∀ᵐ ω ∂ℙ, ∀ᶠ n in atTop, a ≤ empiricalMean X n ω := by
    filter_upwards [h_conv_set] with ω hω
    filter_upwards [hω] with n hn
    have : 𝔼[X 0] - ε < empiricalMean X n ω := by
      rw [abs_sub_lt_iff] at hn
      linarith
    linarith

  -- Convert almost sure eventual convergence to probability convergence
  -- The key fact: if ∀ᵐ ω, ∀ᶠ n, P n ω, then ℙ{P n} → 1
  -- We use continuity of measure from below with increasing sets

  -- Define Sₖ = {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω}
  let S : ℕ → Set Ω := fun k => {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω}

  -- These sets are monotone increasing
  have h_mono : Monotone S := by
    intro k₁ k₂ hk ω hω n hn
    exact hω n (le_trans hk hn)

  -- The union of these sets equals {ω | ∀ᶠ n in atTop, a ≤ empiricalMean X n ω}
  have h_union : ⋃ k, S k = {ω | ∀ᶠ n in atTop, a ≤ empiricalMean X n ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Filter.eventually_atTop, S]

  -- By the ae hypothesis, this union has measure 1
  have h_union_meas : ℙ (⋃ k, S k) = 1 := by
    -- First show that ⋃ k, S k is measurable
    have h_union_meas_set : MeasurableSet (⋃ k, S k) := by
      refine MeasurableSet.iUnion fun k => ?_
      -- S k is a countable intersection of measurable sets
      show MeasurableSet {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω}
      -- This equals ⋂ n ∈ {m | k ≤ m}, {ω | a ≤ empiricalMean X n ω}
      have : {ω | ∀ n ≥ k, a ≤ empiricalMean X n ω} = ⋂ n, ⋂ (_ : k ≤ n), {ω | a ≤ empiricalMean X n ω} := by
        ext; simp
      rw [this]
      refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
      -- {ω | a ≤ empiricalMean X n ω} is measurable
      -- empiricalMean X n = (S X n) / n where S X n is a finite sum of measurable functions
      refine measurableSet_le measurable_const ?_
      convert (Finset.measurable_sum (Finset.range n) (fun i _ => h_meas i)).div_const (n : ℝ) using 1
      ext ω
      simp only [empiricalMean, _root_.S, Finset.sum_apply]
    -- Now show that the complement has measure 0
    rw [h_union]
    -- By the ae statement, ℙ {ω | ¬∀ᶠ n, a ≤ empiricalMean X n ω} = 0
    have h_compl : ℙ {ω | ¬∀ᶠ n in atTop, a ≤ empiricalMean X n ω} = 0 := by
      rw [← ae_iff]
      exact h_eventually_large
    -- The complement of our set equals this null set
    have h_compl_eq : {ω | ∀ᶠ n in atTop, a ≤ empiricalMean X n ω}ᶜ =
        {ω | ¬∀ᶠ n in atTop, a ≤ empiricalMean X n ω} := by
      ext; simp
    -- Therefore our set has measure 1
    rw [← prob_add_prob_compl (μ := ℙ) (h_union ▸ h_union_meas_set), h_compl_eq, h_compl, add_zero]

  -- By continuity of measure from below, ℙ(Sₖ) → 1
  have h_tend_S : Tendsto (fun k => ℙ (S k)) atTop (𝓝 1) := by
    have := tendsto_measure_iUnion_atTop (μ := ℙ) h_mono
    rw [h_union_meas] at this
    exact this

  -- For each k and n ≥ k, we have {ω | a ≤ empiricalMean X n ω} ⊇ S k
  have h_superset : ∀ k n, k ≤ n → S k ⊆ {ω | a ≤ empiricalMean X n ω} := by
    intro k n hkn ω hω
    exact hω n hkn

  -- Therefore ℙ{a ≤ empiricalMean X n} ≥ ℙ(Sₖ) for n ≥ k
  have h_measure_ge : ∀ k n, k ≤ n → ℙ (S k) ≤ ℙ {ω | a ≤ empiricalMean X n ω} := by
    intro k n hkn
    exact measure_mono (h_superset k n hkn)

  -- Since ℙ is a probability measure, ℙ{a ≤ empiricalMean X n} ≤ 1
  have h_measure_le : ∀ n, ℙ {ω | a ≤ empiricalMean X n ω} ≤ 1 := by
    intro n
    exact prob_le_one

  -- By the squeeze theorem, ℙ{a ≤ empiricalMean X n} → 1
  -- We have: ℙ(Sₙ) ≤ ℙ{a ≤ empiricalMean X n} ≤ 1
  -- and both ℙ(Sₙ) → 1 and 1 → 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h_tend_S tendsto_const_nhds
    (fun n => h_measure_ge n n le_rfl) h_measure_le

-- Helper lemmas for the lower bound proof

/-- If a sequence of ENNReal values tends to 1, then their logs tend to 0. -/
private lemma ennreal_log_tendsto_zero_of_tendsto_one {f : ℕ → ℝ≥0∞}
    (h : Tendsto f atTop (𝓝 1)) :
    Tendsto (fun n => (f n).log) atTop (𝓝 0) := by
  -- `ENNReal.log` is continuous, so compose its tendsto at `1` with `h`
  have h' := (ENNReal.continuous_log.tendsto (1 : ℝ≥0∞)).comp h
  convert h'
  simp [ENNReal.log_one]

/-- The sequence 1/n tends to 0 in EReal. -/
private lemma ereal_inv_nat_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) : EReal)) atTop (𝓝 0) := by
  -- prove using tendsto_one_div_add_atTop_nhds_zero_nat
  -- identify `1 / ((n : ℝ) : EReal)` with `(1 : EReal) / n` and apply the existing lemma
  have : (fun n : ℕ => 1 / ((n : ℝ) : EReal)) = fun (n : ℕ) => (1 : EReal) / n := by
    funext n; rfl
  rw [this]
  -- `1 : EReal` is neither ⊥ nor ⊤, so we can apply the lemma
  exact (EReal.tendsto_const_div_atTop_nhds_zero_nat (by decide) (by decide))

/-- Product of a sequence tending to 0 with a bounded sequence tends to 0 in EReal. -/
private lemma ereal_mul_tendsto_zero_of_tendsto_zero_of_bounded
    {f g : ℕ → EReal} (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  -- Use the `EReal` multiplication tendsto lemma: multiplication is continuous at (0,0)
  -- because `(0 : EReal) ≠ ⊤` and `(0 : EReal) ≠ ⊥`.
  simpa using EReal.Tendsto.mul hf hg (Or.inr (EReal.coe_ne_bot 0)) (Or.inr (EReal.coe_ne_top 0))
    (Or.inl (EReal.coe_ne_bot 0)) (Or.inl (EReal.coe_ne_top 0))


include h_indep h_meas h_ident h_mgf h_int h_bdd in
/-- **Cramér's Theorem**: For i.i.d. random variables with finite MGF, the empirical mean
satisfies a large deviation principle with rate function given by the Legendre transform
of the CGF. -/
theorem cramers_theorem :
    LargeDeviationPrinciple (empiricalMean X) (upperTailRateFunction X) := by
  constructor
  · -- Upper bound: currently proven only for a ≥ 𝔼[X 0]
    -- Need to extend to all a or handle a < 𝔼[X 0] separately
    intro a
    by_cases h : 𝔼[X 0] ≤ a
    · rw [upperTailRateFunction_eq_rateFunction a h]
      exact cramer_upper_bound X h_indep h_ident h_meas h_int h_mgf h_bdd a h
    · -- a < Mean (Typical event)
      -- The rate function is 0.
      -- Probability → 1, so log(P) → 0.
      -- 0 ≤ 0 holds.
      norm_cast
      rw [upperTailRateFunction_eq_zero a (not_le.mp h)]
      have h_log_prob_bound : ∀ n : ℕ, (ℙ {ω | a ≤ empiricalMean X n ω}).log ≤ 0 := by
        simp
        intro n
        exact prob_le_one

      have h_prob_bound_2: ∀ n : ℕ, n ≠ 0 → 1 / ↑n * (ℙ {ω | empiricalMean X n ω ≥ a}).log ≤ 0 := by
        intro n h_n_nonneg
        -- Since ℙ(...) ≤ 1, we have log(ℙ(...)) ≤ 0
        have h_log_nonpos : (ℙ {ω | empiricalMean X n ω ≥ a}).log ≤ 0 := by
          rw [ENNReal.log_le_zero_iff]
          exact prob_le_one
        -- Since 1/n ≥ 0 and log(...) ≤ 0, the product is ≤ 0
        rw [EReal.mul_nonpos_iff]
        left
        constructor
        · -- Show 0 ≤ 1 / ↑n
          rw [div_eq_mul_inv, one_mul]
          apply EReal.inv_nonneg_of_nonneg
          -- Show 0 ≤ (↑n : EReal)
          have : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_n_nonneg)
          exact EReal.coe_nonneg.mpr (le_of_lt this)
        · exact h_log_nonpos

      -- Show limsup ≤ 0 from the bound
      simp only [neg_zero]  -- Simplify -0 to 0
      apply Filter.limsup_le_of_le
      · -- IsCoboundedUnder: bounded below
        exact isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
      · -- Eventually the bound holds
        apply Filter.eventually_atTop.mpr
        use 1
        intro n hn
        exact h_prob_bound_2 n (Nat.one_le_iff_ne_zero.mp hn)
  · intro a
    by_cases h : 𝔼[X 0] ≤ a
    · rw [upperTailRateFunction_eq_rateFunction a h]
      exact cramer_lower_bound X h_indep h_ident h_meas h_mgf a h
    · -- a < Mean (Typical event)
      -- The rate function is 0.
      -- For typical events, probability → 1, so log(P) → 0.
      -- Thus 1/n * log(P) → 0, and liminf ≥ 0.
      rw [upperTailRateFunction_eq_zero a (not_le.mp h)]
      norm_cast
      rw [neg_zero]

      -- By the strong law of large numbers, empirical mean converges to 𝔼[X 0] almost surely
      -- Since a < 𝔼[X 0], the probability ℙ{empirical mean ≥ a} → 1
      -- Therefore log(ℙ{...}) → 0, and 1/n * log(ℙ{...}) → 0
      -- Thus liminf ≥ 0

      -- Use the helper lemma: ℙ{empirical mean ≥ a} → 1
      have h_a_lt_mean : a < 𝔼[X 0] := not_le.mp h
      have h_prob_to_one :
          Tendsto (fun n => (ℙ {ω | a ≤ empiricalMean X n ω} : ENNReal)) atTop (𝓝 1) :=
        @less_exp_imp_limit_prob_less_mean_one Ω _ X h_indep h_ident h_meas h_int _ a
          h_a_lt_mean

      -- We'll show that the sequence 1/n * log(ℙ{...}) → 0
      -- Then by Tendsto.liminf_eq, we get liminf = 0, so 0 ≤ liminf

      have h_seq_to_zero : Tendsto (fun (n : ℕ) =>
          1 / ((n : ℝ) : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop
          (𝓝 (0 : EReal)) := by
        -- The key steps:
        -- 1. log(ℙ) → log(1) = 0 (since ℙ → 1 and log 1 = 0)
        -- 2. 1/n → 0
        -- 3. Product of (sequence → 0) with bounded sequence → 0

        -- Step 1: Show log(ℙ{...}) → 0
        have h_log_to_zero : Tendsto (fun n => (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop (𝓝 0) :=
          ennreal_log_tendsto_zero_of_tendsto_one h_prob_to_one

        -- Step 2: Show 1/n → 0 in EReal
        have h_inv_to_zero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) : EReal)) atTop (𝓝 0) :=
          ereal_inv_nat_tendsto_zero

        -- Step 3: Combine using Tendsto.mul for EReal
        -- Cast log to EReal - since log returns EReal, this is just the identity
        have h_log_ereal :
            Tendsto (fun n => (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop
              (𝓝 (0 : EReal)) := h_log_to_zero
        exact ereal_mul_tendsto_zero_of_tendsto_zero_of_bounded h_inv_to_zero h_log_ereal

      -- Now use that convergence implies liminf equals the limit
      have h_lim_eq : liminf (fun (n : ℕ) =>
          1 / ((n : ℝ) : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop
          = (0 : EReal) := Filter.Tendsto.liminf_eq h_seq_to_zero

      -- The two liminf expressions are equal, so we just need 0 ≤ liminf(...)
      -- Show the functions are equal and rewrite
      have h_fn_eq : (fun n : ℕ =>
          1 / ((n : ℝ) : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) =
          (fun n : ℕ => 1 / (n : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) := by
        funext n
        congr 1
      have : liminf (fun n : ℕ =>
          1 / (n : EReal) * (ℙ {ω | empiricalMean X n ω ≥ a}).log) atTop = 0 := by
        rw [← h_fn_eq]
        exact h_lim_eq
      rw [this]
      norm_cast
