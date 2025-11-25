/-
Copyright (c) 2025 Kaan.
Authors: Kaan
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.SpecificLimits.Basic

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
-- This is implied by h_mgf but assume it for convenience for now
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
          rw [show sInf (Set.range fun t : {x : ℝ | 0 ≤ x} => (-(t.val * a - cgf (X 0) ℙ t) : EReal)) =
                   (sInf (Set.range fun t : {x : ℝ | 0 ≤ x} => -(t.val * a - cgf (X 0) ℙ t)) : EReal) by
                rfl]
          norm_cast

          -- Use that sInf of negations equals negative of sSup
          -- Apply csInf_neg_eq_neg_csSup with f(t) = t.val * a - cgf (X 0) ℙ t
          have h_nonempty : (Set.range fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t).Nonempty := by
            use 0 * a - cgf (X 0) ℙ 0
            use ⟨0, by simp⟩
          have h_eq_real : sInf (Set.range fun t : {x : ℝ | 0 ≤ x} => -(t.val * a - cgf (X 0) ℙ t)) =
                            -sSup (Set.range fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t) := by
            exact csInf_neg_eq_neg_csSup (fun t : {x : ℝ | 0 ≤ x} => t.val * a - cgf (X 0) ℙ t) h_nonempty h_bdd_restrict
          -- The key remaining step: show that coercion from ℝ to EReal commutes with sInf/sSup
          -- for bounded sets. This requires showing:
          --   (sInf S : EReal) = sInf ((↑) '' S)
          -- This is true because coercion is a monotone embedding, but proving it requires
          -- either finding the right mathlib lemma or proving it from scratch using properties
          -- of order-preserving maps and complete lattices.
          rw [iSup] at *
          sorry  -- Need: coercion ℝ → EReal commutes with sInf for bounded sets
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

include h_indep h_meas h_ident h_mgf in
/-- **Cramér's Theorem (Lower Bound)**: For any a, the scaled log probability that the
empirical mean is close to a is bounded below by the negative rate function.
Uses `ENNReal.log` to properly handle the case when probability is 0 (giving -∞). -/
theorem cramer_lower_bound (a : ℝ) (h_mean : 𝔼[X 0] ≤ a) :
    (- rateFunction X a : EReal) ≤
      liminf (fun n : ℕ =>
        ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | empiricalMean X n ω ≥ a})) atTop := by
  sorry


private lemma test (n : ℕ) (a : EReal) (h_n_nonneg : n ≠ 0) : (n : ENNReal)⁻¹ * a ≤ 0 → a ≤ 0 := by
  intro h
  -- Use contraposition: if 0 < a, then 0 < (n : ENNReal)⁻¹ * a
  by_contra h_not
  push_neg at h_not
  -- h_not : 0 < a
  -- h : ↑((n : ENNReal)⁻¹) * a ≤ 0 in EReal

  -- Step 1: Show 0 < (n : ENNReal)⁻¹ in ENNReal
  have hn_ennreal_inv_pos : 0 < (n : ENNReal)⁻¹ := by
    rw [ENNReal.inv_pos]
    exact ENNReal.natCast_ne_top n

  -- Step 2: Coerce to EReal: 0 < ↑((n : ENNReal)⁻¹)
  have hn_ereal_inv_pos : (0 : EReal) < ↑((n : ENNReal)⁻¹) := by
    exact EReal.coe_ennreal_pos.mpr hn_ennreal_inv_pos

  -- Step 3: Multiply positive numbers
  have : (0 : EReal) < ↑((n : ENNReal)⁻¹) * a := by
    exact EReal.mul_pos hn_ereal_inv_pos h_not

  -- Step 4: Contradiction with h
  exact absurd h (not_le.mpr this)

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
  sorry

/-- The sequence 1/n tends to 0 in EReal. -/
private lemma ereal_inv_nat_tendsto_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) : EReal)) atTop (𝓝 0) := by
  -- prove using tendsto_one_div_add_atTop_nhds_zero_nat
  sorry

/-- Product of a sequence tending to 0 with a bounded sequence tends to 0 in EReal. -/
private lemma ereal_mul_tendsto_zero_of_tendsto_zero_of_bounded
    {f g : ℕ → EReal} (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  sorry

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
