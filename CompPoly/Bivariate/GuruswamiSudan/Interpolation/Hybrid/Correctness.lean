/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.ApproximantBasis.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Hybrid.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast

/-!
# Correctness of Hybrid Guruswami-Sudan Interpolation

The hybrid's fuel/fallback dispatch affects performance only: its result
always coincides with the result of one of the two verified backends
(`hybridPositiveInterpolate_eq_lee_or_approximant`). Soundness and
completeness of `hybridInterpContext` follow by case analysis from the
corresponding backend theorems.

The only reduction-level fact needed is determinism of the fueled
Mulders-Storjohann loop (`muldersStorjohannReduceWithFuel_eq_of_no_conflict`):
when the budgeted probe ends without a shifted leading conflict, it stopped at
the same matrix as the full reduction, so the kept Lee branch is literally the
Lee-O'Sullivan backend run with the fast reducer context.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace Hybrid

open PolynomialMatrix
open PolynomialMatrix.Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

omit [Nontrivial F] in
/-- When the budgeted probe ends conflict-free it equals the full fast
reduction. -/
private theorem hybrid_probe_eq_reduceFast
    {fuel : Nat} {basis : PolynomialMatrix F} {shift : Array Nat}
    (hWF : WellFormed basis)
    (hconf : cachedLeadingConflict?
      (rowLeadingPositions
        (muldersStorjohannReduceWithFuelFast fuel basis shift) shift) = none) :
    muldersStorjohannReduceWithFuelFast fuel basis shift =
      muldersStorjohannReduceFast basis shift := by
  rw [muldersStorjohannReduceWithFuelFast_eq, muldersStorjohannReduceFast_eq,
    muldersStorjohannReduce]
  apply muldersStorjohannReduceWithFuel_eq_of_no_conflict
  · rw [cachedLeadingConflict?_eq, muldersStorjohannReduceWithFuelFast_eq] at hconf
    exact hconf
  · have hno := muldersStorjohannReduce_no_conflict basis shift hWF
    rw [muldersStorjohannReduce] at hno
    exact hno

/-- The hybrid branch result always coincides with one of the two verified
backends. -/
theorem hybridPositiveInterpolate_eq_lee_or_approximant
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (budget : GSInterpParams → Nat)
    (points : Array (F × F)) (params : GSInterpParams) :
    hybridPositiveInterpolate V E solver budget points params =
        LeeOSullivan.leeOSullivanPositiveInterpolate V E
          (muldersStorjohannFastReducerContext F) points params ∨
      hybridPositiveInterpolate V E solver budget points params =
        ApproximantBasis.approximantBasisPositiveInterpolate V E solver
          points params := by
  by_cases hdist : distinctXCoordinatesBool points
  · simp only [hybridPositiveInterpolate, hdist, if_true]
    split
    case h_1 _ hconf =>
      right
      rfl
    case h_2 _ hconf =>
      left
      rw [hybrid_probe_eq_reduceFast
        (LeeOSullivan.leeOSullivanBasisRowsWithRG_wellFormed _ _ params) hconf]
      simp only [LeeOSullivan.leeOSullivanPositiveInterpolate, hdist, if_true,
        muldersStorjohannFastReducerContext]
      rfl
  · left
    rw [hybridPositiveInterpolate, if_neg hdist,
      LeeOSullivan.leeOSullivanPositiveInterpolate, if_neg hdist]

/-- The hybrid result always coincides with one of the two verified
backends. -/
theorem hybridInterpolate_eq_lee_or_approximant
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (budget : GSInterpParams → Nat)
    (points : Array (F × F)) (params : GSInterpParams) :
    hybridInterpolate V E solver budget points params =
        LeeOSullivan.leeOSullivanInterpolate V E
          (muldersStorjohannFastReducerContext F) points params ∨
      hybridInterpolate V E solver budget points params =
        ApproximantBasis.approximantBasisInterpolate V E solver points params := by
  by_cases hlow : params.messageDegree ≤ 1
  · left
    simp only [hybridInterpolate, LeeOSullivan.leeOSullivanInterpolate, hlow,
      if_true]
  · simp only [hybridInterpolate, LeeOSullivan.leeOSullivanInterpolate,
      ApproximantBasis.approximantBasisInterpolate, hlow, if_false]
    exact hybridPositiveInterpolate_eq_lee_or_approximant V E solver budget
      points params

/-- Public hybrid interpolation backend context: adaptive Lee-O'Sullivan
reduction under a step budget with an approximant-basis fallback. -/
def hybridInterpContext
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (solver : ModularSolutionBasisContext F)
    (budget : GSInterpParams → Nat) : GSInterpContext F where
  interpolate := hybridInterpolate V E solver budget
  sound := by
    intro points params Q h
    rcases hybridInterpolate_eq_lee_or_approximant V E solver budget points
        params with heq | heq
    · exact LeeOSullivan.leeOSullivanInterpolate_sound V E
        (muldersStorjohannFastReducerContext F) (heq ▸ h)
    · exact ApproximantBasis.approximantBasisInterpolate_sound V E solver
        (heq ▸ h)
  complete := by
    intro points params hdistinct hexists
    rcases hybridInterpolate_eq_lee_or_approximant V E solver budget points
        params with heq | heq
    · rw [heq]
      exact LeeOSullivan.leeOSullivanInterpolate_complete V E
        (muldersStorjohannFastReducerContext F) hdistinct hexists
    · rw [heq]
      exact ApproximantBasis.approximantBasisInterpolate_complete V E solver
        points params hdistinct hexists

end Hybrid

end GuruswamiSudan

end CompPoly
