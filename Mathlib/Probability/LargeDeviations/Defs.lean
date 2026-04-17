/-
Copyright (c) 2025 Kaan Erdoğmuş. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Erdoğmuş
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Probability.Notation

/-!
# Large Deviation Principles

This file defines the `LargeDeviationPrinciple` for sequences of random variables.

A large deviation principle (LDP) characterizes the rate at which the probability of
tail events decay. Formally, we say that a sequence of random variables `(Yₙ)` satisfies
an LDP with rate function `I` if for every `a` the limsup (resp. liminf) of
`(1/n) * log ℙ(Yₙ ≥ a)` is at most (resp. at least) `-I(a)`.

## Main definitions
- `LargeDeviationPrinciple`: A Prop-valued structure containing the upper and lower bound

## Notes
The definition splits the upper and lower bounds so that each side can be proven separately.

This statement is given for sequences of real-valued random variables. However, this
could be further generalized to be in terms of Borel-measurable sets in Polish spaces.

## References
* <https://en.wikipedia.org/wiki/Large_deviation_theory>
* <https://en.wikipedia.org/wiki/Cramér%27s_theorem_(large_deviations)>
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasureSpace Ω]

/-- A sequence of real-valued random variables `(Yₙ)` satisfies a **Large Deviation
Principle** with rate function `I : ℝ → ℝ` if for every `a` the limsup (resp. liminf)
of the scaled log-tail probability `(1/n) * log ℙ(Yₙ ≥ a)` is at most (resp. at least)
`-I(a)`.
The sub-goals are defined in terms of the extended real numbers to account for events
with probability 0.
-/
structure LargeDeviationPrinciple (Y : ℕ → Ω → ℝ) (I : ℝ → ℝ) : Prop where
  /-- Upper bound: limsup_n (1/n) log ℙ(Yₙ ≥ a) ≤ -I(a) -/
  upperBound : ∀ a : ℝ,
    limsup (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | Y n ω ≥ a}))
      atTop ≤ (- I a : EReal)
  /-- Lower bound: liminf_n (1/n) log ℙ(Yₙ ≥ a) ≥ -I(a) -/
  lowerBound : ∀ a : ℝ,
    (- I a : EReal) ≤
      liminf (fun n : ℕ => ((1 : ℝ) / (n : ℝ) : EReal) * ENNReal.log (ℙ {ω | Y n ω ≥ a}))
        atTop

end ProbabilityTheory
