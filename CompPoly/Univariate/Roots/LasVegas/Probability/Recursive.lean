/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.Basic

/-!
# Recursive Fallback Model for Las Vegas Splitting

Abstract binomial-tail bound for the planned full-recursion fallback analysis:
the recursion model packages the independence and root-product hypotheses, and
the tail theorem bounds the fallback probability by a binomial tail.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/--
Binomial-tail expression used by the planned full-recursion fallback bound.
`Finset.range (degree - 1)` indexes `0, ..., degree - 2`.
-/
noncomputable def binomialFallbackTail (attempts degree : Nat) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ attempts *
    ((Finset.range (degree - 1)).sum fun j ↦ (Nat.choose attempts j : ℝ≥0∞))

/-- A cutoff meets the binomial-tail target for field cardinality `q`. -/
def binomialTailCutoffPredicate (q degree attempts : Nat) : Prop :=
  binomialFallbackTail attempts degree ≤ (q : ℝ≥0∞)⁻¹

/--
Model predicate for the planned recursive splitter: it packages the future
independence and root-product hypotheses needed for the binomial fallback tail.
-/
def RecursiveFallbackProbabilityModel {Ω : Type*}
    (process : PMF Ω) (fallbackEvent : Set Ω)
    (attempts degree : Nat) : Prop :=
  ∃ badRankEvent : Nat → Set Ω,
    fallbackEvent ⊆ ⋃ j, badRankEvent j ∧
      (∀ j, j ∉ Finset.range (degree - 1) →
        eventProbability process (badRankEvent j) = 0) ∧
        (∀ j, j ∈ Finset.range (degree - 1) →
          eventProbability process (badRankEvent j) ≤
            ((2 : ℝ≥0∞)⁻¹) ^ attempts * (Nat.choose attempts j : ℝ≥0∞))

/--
Target theorem for the full recursive splitter: under the independence and
root-product hypotheses represented by the future recursion model, fallback is
bounded by the binomial tail.
-/
theorem recursiveFallback_probability_le_binomialTail {Ω : Type*}
    (process : PMF Ω) (fallbackEvent : Set Ω)
    (attempts degree : Nat)
    (hmodel : RecursiveFallbackProbabilityModel process fallbackEvent attempts degree) :
    eventProbability process fallbackEvent ≤ binomialFallbackTail attempts degree := by
  rcases hmodel with ⟨badRankEvent, hcover, hzero, hbound⟩
  let half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹
  calc
    eventProbability process fallbackEvent
        ≤ eventProbability process (⋃ j, badRankEvent j) := by
          simpa [eventProbability] using process.toOuterMeasure.mono hcover
    _ ≤ ∑' j, eventProbability process (badRankEvent j) := by
          simpa [eventProbability] using
            (MeasureTheory.measure_iUnion_le (μ := process.toOuterMeasure) badRankEvent)
    _ ≤ ∑' j : Nat,
          if j ∈ Finset.range (degree - 1) then
            half ^ attempts * (Nat.choose attempts j : ℝ≥0∞)
          else
            0 := by
          apply ENNReal.tsum_le_tsum
          intro j
          by_cases hj : j ∈ Finset.range (degree - 1)
          · simpa [half, hj] using hbound j hj
          · simp [hj, hzero j hj]
    _ = binomialFallbackTail attempts degree := by
          unfold binomialFallbackTail
          rw [tsum_eq_sum (s := Finset.range (degree - 1))]
          · trans (Finset.range (degree - 1)).sum
                (fun j ↦ half ^ attempts * (Nat.choose attempts j : ℝ≥0∞))
            · apply Finset.sum_congr rfl
              intro j hj
              simp [hj]
            · simp [half, Finset.mul_sum]
          · intro j hj
            simp [hj]

end FiniteField

end Roots

end CPolynomial

end CompPoly
