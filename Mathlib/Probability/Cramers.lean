/-
Copyright (c) 2025 Kaan.
Authors: Kaan
-/
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic

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
variable (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)

/-- The partial sum X_0 + ... + X_{n-1}. -/
noncomputable def S (n : ℕ) : Ω → ℝ := ∑ i ∈ Finset.range n, X i

/-- The empirical mean S_n / n. -/
noncomputable def empiricalMean (n : ℕ) : Ω → ℝ := fun ω => S X n ω / n

/-- The Legendre transform of the CGF. This is the rate function for Cramér's theorem. -/
noncomputable def rateFunction (x : ℝ) : ℝ :=
  ⨆ t : ℝ, t * x - cgf (X 0) ℙ t

/- Helper lemmas -/

lemma integrable_exp_of_identDistrib
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
    (i : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X i ω)) ℙ := by
  have hcomp : Measurable (fun x : ℝ => Real.exp (t * x)) :=
    (measurable_const.mul measurable_id).exp
  have : IdentDistrib (fun ω => Real.exp (t * X i ω)) (fun ω => Real.exp (t * X 0 ω)) ℙ ℙ :=
    (h_ident i).comp hcomp
  exact this.integrable_iff.mpr (h_mgf t)

variable [IsProbabilityMeasure (ℙ : Measure Ω)]

lemma integrable_exp_sum
    (h_indep : iIndepFun X ℙ)
    (h_meas : ∀ n, Measurable (X n))
    (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ)
    (h_mgf : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) ℙ)
    (t : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (t * S X n ω)) ℙ := by
  sorry  -- TODO: prove using independence

/- Main results -/

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
    integrable_exp_sum X h_indep h_meas h_ident h_mgf t n

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
rate function `I` if the scaled log probabilities converge to `-I` at each point. -/
structure LargeDeviationPrinciple (Y : ℕ → Ω → ℝ) (I : ℝ → ℝ) : Prop where
  /-- Upper bound: limsup of scaled log probability is at most -I(a) -/
  upper_bound : ∀ a : ℝ,
    limsup (fun n => (1 : ℝ) / n * Real.log (ℙ {ω | Y n ω ≥ a}).toReal) atTop ≤ - I a
  /-- Lower bound: liminf of scaled log probability is at least -I(a) -/
  lower_bound : ∀ a : ℝ,
    - I a ≤ liminf (fun n => (1 : ℝ) / n * Real.log (ℙ {ω | Y n ω ≥ a}).toReal) atTop

include h_indep h_meas h_ident h_mgf in
/-- **Cramér's Theorem (Upper Bound)**: For any a, the scaled log probability that the
empirical mean exceeds a is bounded above by the negative rate function. -/
theorem cramer_upper_bound (a : ℝ) :
    limsup (fun n : ℕ => (1 : ℝ) / n * Real.log (ℙ {ω | empiricalMean X n ω ≥ a}).toReal) atTop
      ≤ - rateFunction X a := by
  -- Use prob_mean_ge_le_exp with t = 0 to get an upper bound
  unfold rateFunction
  -- Apply the bound from prob_mean_ge_le_exp with t = 0
  have : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n * Real.log (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
      ≤ -(0 * a - cgf (X 0) ℙ 0) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn_pos
    have hbound := @prob_mean_ge_le_exp _ _ X h_indep h_ident h_meas h_mgf _
        0 a (le_refl (0 : ℝ)) n hn_pos
    -- From ℙ{...} ≤ exp(-n*(0*a - cgf 0)), take logs and divide by n
    by_cases hprob : (ℙ {ω | empiricalMean X n ω ≥ a}).toReal ≤ 0
    · -- If probability is ≤ 0, the bound holds since log is negative
      sorry
    · -- If probability > 0, take logs
      push_neg at hprob
      have hlog : Real.log (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
          ≤ Real.log (Real.exp (- (n : ℝ) * (0 * a - cgf (X 0) ℙ 0))) := by
        exact Real.log_le_log hprob hbound
      rw [Real.log_exp] at hlog
      have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      calc (1 : ℝ) / n * Real.log (ℙ {ω | empiricalMean X n ω ≥ a}).toReal
          ≤ (1 : ℝ) / n * (- (n : ℝ) * (0 * a - cgf (X 0) ℙ 0)) := by gcongr
        _ = -(0 * a - cgf (X 0) ℙ 0) := by field_simp
  -- TODO: Complete the proof by showing limsup ≤ -(0*a - cgf 0) ≤ -rateFunction
  -- The key ingredients are:
  -- 1. limsup_le_of_le to convert eventual bounds to limsup bounds
  -- 2. Show -(0*a - cgf 0) = cgf 0 ≤ ⨆ t, (t*a - cgf t) for appropriate choice of t
  sorry

include h_indep h_meas h_ident h_mgf in
/-- **Cramér's Theorem (Lower Bound)**: For any a, the scaled log probability that the
empirical mean is close to a is bounded below by the negative rate function. -/
theorem cramer_lower_bound (a : ℝ) :
    - rateFunction X a ≤
      liminf (fun n : ℕ =>
        (1 : ℝ) / n * Real.log (ℙ {ω | empiricalMean X n ω ≥ a}).toReal) atTop := by
  sorry

include h_indep h_meas h_ident h_mgf in
/-- **Cramér's Theorem**: For i.i.d. random variables with finite MGF, the empirical mean
satisfies a large deviation principle with rate function given by the Legendre transform
of the CGF. -/
theorem cramers_theorem :
    LargeDeviationPrinciple (empiricalMean X) (rateFunction X) := by
  constructor
  · exact cramer_upper_bound X h_indep h_ident h_meas h_mgf
  · exact cramer_lower_bound X h_indep h_ident h_meas h_mgf
