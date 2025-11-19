module

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Function

open ProbabilityTheory MeasureTheory Filter Topology ENNReal
open scoped BigOperators

-- 1. The sample space (Ω), equipped with a measure space structure.
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- 2. Setup the variables
-- We assume the codomain is ℝ and it has the Borel sigma algebra (automatic with imports)
variable (X : ℕ → Ω → ℝ)

-- 3. Assumptions
-- It is often helpful to group these into a structure or keep them as variables
variable (h_indep : iIndepFun X ℙ)  -- family mutually independent
variable (h_ident : ∀ n, IdentDistrib (X n) (X 0) ℙ ℙ) -- identically distributed
variable (h_meas : ∀ n, Measurable (X n))
  -- TODO: prob no need for this yet, we'll use the lemmas measure_*_exp_cgf pointwise
  -- Assumption: The moment generating function (MGF) exists everywhere.
  -- (h_mgf_finite : ∀ t : ℝ, ∫ ω, Real.exp (t * (X 0) ω) ∂ℙ < ∞.toReal)
-- TODO h_mgf_finite is I _think_ equivalent this, can we replace this with that (or even
-- better the aforementioned lemmas)
variable (h_mgf : ∀ n : ℕ, ∀ s : ℝ, ∀ i ∈ Finset.range n,
  Integrable (fun ω => Real.exp (s * (X i) ω)) ℙ)

/-- The partial sum X_0 + ... + X_{n-1}.
    Note: We use range n, which sums 0 to n-1. This aligns with 0-indexing. -/
noncomputable def S (n : ℕ) : Ω -> ℝ := ∑ i ∈ Finset.range n, X i

/-- The empirical mean S_n / n. -/
noncomputable def empiricalMean (n : ℕ) : Ω -> ℝ := fun ω => (S X n ω) / n
local notation "X̄" => empiricalMean

-- The Cumulant Generating Function (CGF) of the random variable X 0.
-- Essentially, log E[exp (t * X_i)] for any of the X_i (iid)
noncomputable def ψ (t : ℝ) : ℝ := cgf (X 0) ℙ t

/-
Convex conjugate on ℝ (two variants):
  • `convexConjugate f x = ⨆ θ, θ*x - f θ`
  • `convexConjugateOn I f x = csSup ((fun θ => θ*x - f θ) '' I)`
The second is convenient when f is meaningful only on a set I (e.g., log-MGF on a nbhd of 0).
-/
/-- Unrestricted convex conjugate on ℝ (via `iSup` over the parameter). -/
noncomputable def convexConjugate (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨆ θ : ℝ, θ * x - f θ

/-- Domain-restricted convex conjugate. Uses `csSup` so we’ll require
    nonemptiness + boundedness when we *use* it. -/
noncomputable def convexConjugateOn (I : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun θ => θ * x - f θ) '' I)


-- The Rate Function.
-- This is I(a) := inf_λ (ψ(λ) - aλ) which comes from the Chernoff bound on ℙ(Sₙ > an)
noncomputable def I (x : ℝ) : ℝ := convexConjugate (ψ X) x

-- A simplified statement of Cramér's Theorem (The Upper Bound for a point)
theorem cramers_theorem_upper_bounMd_point (a : ℝ) (hx : 𝔼[X 0] < a) :
  -- The limit superior of (1/n) * log(P(Sₙ/n ≥ a)) is at most -I(a)).
  limsup (fun n => (1 : ℝ) / n * Real.log (ℙ {ω | empiricalMean X n ω ≥ a}).toReal) atTop
    ≤ -I X a :=
by
  sorry


/-- A family of random variables `(Y n)` satisfies a large deviation principle with
rate function `I` if for all Borel sets `A` we have the standard LDP bounds:
- liminf ≥ -inf over interior
- limsup ≤ -inf over closure. -/
structure LargeDeviationPrinciple
  (Y : ℕ → Ω → ℝ) (I : ℝ → ℝ) : Prop where
(liminf_bound :
  ∀ (A : Set ℝ), MeasurableSet A →
    - ⨅ x ∈ interior A, I x ≤
      liminf (fun n ↦ (1 : ℝ)/n * Real.log (ℙ {ω | Y n ω ∈ A}).toReal) atTop)
(limsup_bound :
  ∀ (A : Set ℝ), MeasurableSet A →
      limsup (fun n ↦ (1 : ℝ)/n * Real.log (ℙ {ω | Y n ω ∈ A}).toReal) atTop ≤
    - ⨅ x ∈ closure A, I x)



/-- **Cramér’s Theorem (sketch)**:
For i.i.d. real-valued random variables with law `μ`,
the empirical mean satisfies a large deviation principle with rate
function `rateFunction μ X`. -/
theorem CramersTheorem :
  LargeDeviationPrinciple (empiricalMean X) (I X) := sorry

-- --- helper lemma: integrability of exp (t * S n)
-- We will require (or prove) integrability of exp(t * S n).
-- Strategy: show ∫ exp(t * S n) = ∏_{i<n} ∫ exp(t * X_i) using independence,
-- hence finite if each mgf(X_i, t) < ∞.
lemma integrable_exp_sum_of_mgf_finite (t : ℝ) (n : ℕ) :
  Integrable (fun ω => Real.exp (t * S X n ω)) ℙ := by
  -- math explanation:
  --   exp(t * S_n) = ∏_{i<n} exp(t * X_i). Use independence to factor the integral,
  --   and finiteness follows from the product of finite integrals.
  --
  -- Lean steps (sketch):
  -- 1. rewrite `Real.exp (t * S_n ω)` as `∏ i, Real.exp (t * X i ω)` pointwise;
  -- 2. use the independence/integration API (e.g. `iIndepFun.indepFun_finset₀` +
  --    `setIntegral_prod` / `setIntegral_finset_prod` style lemmas) to obtain
  --    `∫ (ω), ∏ i, Real.exp (t * X i ω) ∂ℙ = ∏ i, ∫ (ω), Real.exp (t * X i ω) ∂ℙ`;
  -- 3. then `Integrable` holds because the RHS is a finite product of finite numbers.
  --
  -- Actual implementation: use the Independence · Integration lemmas documented in mathlib.
  admit

-- Key analytic estimate (Chernoff upper tail for the empirical mean)
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
    integrable_exp_sum_of_mgf_finite X t n

  -- Step 2: apply the standard Chernoff lemma in mathlib:
  -- `ProbabilityTheory.measure_ge_le_exp_cgf` says
  --   (ℙ { ω | ε ≤ Y ω }).to_real ≤ rexp (-t * ε + ProbabilityTheory.cgf Y ℙ t)
  -- provided `0 ≤ t` and integrability of exp (t * Y).
  have chernoff := ProbabilityTheory.measure_ge_le_exp_cgf ((n : ℝ) * a) (ht) (hinteg)
  -- chernoff is: (ℙ {ω | (n*a) ≤ S_n ω}).toReal ≤ rexp (-t*(n*a) + cgf (S_n) ℙ t)

  -- Step 3: rewrite cgf of the finite sum via independence:
  -- `cgf (S_n) ℙ t = n * cgf (X 0) ℙ t`
  have cgf_sum_eq : cgf (S X n) ℙ t = (n : ℝ) * cgf (X 0) ℙ t := by
    -- We need to handle the case n = 0 separately
    by_cases hn : n = 0
    · -- If n = 0, both sides are 0
      simp [hn, S, cgf]
    · -- If n ≠ 0, use cgf_sum_of_identDistrib
      have h0_mem : 0 ∈ Finset.range n := by
        simp [Finset.mem_range]
        omega
      -- Build the IdentDistrib hypothesis for all pairs in range n
      have hident_all : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
          IdentDistrib (X i) (X j) ℙ ℙ := by
        intros i _ j _
        exact (h_ident i).trans (h_ident j).symm
      -- Apply cgf_sum_of_identDistrib
      rw [S]
      convert cgf_sum_of_identDistrib h_meas h_indep hident_all h0_mem t (h_mgf n t) using 1
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



lemma limsup_upper_halfline (a : ℝ) :
  Filter.limsup (fun n : ℕ =>
      (1 : ℝ) / (n : ℝ) * Real.log ((ℙ {ω | empiricalMean X n ω ∈ Set.Ioi a}).toReal)) atTop
  ≤ - convexConjugate (fun t => cgf (X 0) ℙ t) a := by
  -- Convert `{… ∈ Ioi a}` to `{… ≥ a}`.
  -- Use `prob_mean_ge_le_exp` to bound each n by `exp(- n * (t*a - ψ t))`.
  -- Take `Real.log`, divide by n, take `limsup`, and then optimize over t≥0.
  -- Conclude with the definition of the convex conjugate.
  sorry

lemma cramer_upper_bound_closed
  (F : Set ℝ) (hF : IsClosed F) :
  Filter.limsup (fun n : ℕ =>
      (1 : ℝ) / (n : ℝ) * Real.log ((ℙ {ω | empiricalMean X n ω ∈ F}).toReal)) atTop
  ≤ - ⨅ x ∈ F, convexConjugate (fun t => cgf (X 0) ℙ t) x := by
  -- Reduce F to intersections of half-lines and use `limsup_upper_halfline`.
  -- Then pass to infimum over x∈F.
  sorry

