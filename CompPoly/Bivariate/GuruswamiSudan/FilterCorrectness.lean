/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness

/-!
# Guruswami-Sudan Candidate Filter Correctness

Correctness and completeness lemmas for generic packed filtering over algebraic
`gsCore` outputs.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Boolean distance filtering agrees with the executable mismatch count. -/
theorem passesCandidateDistance_iff {F : Type*} [Semiring F] [BEq F]
    {points : Array (Prod F F)} {radius : Nat} {p : CPolynomial F} :
    passesCandidateDistance points radius p = true ↔
      candidateMismatchCount points p ≤ radius := by
  unfold passesCandidateDistance
  exact decide_eq_true_iff

/-- Membership in `gsFilteredCore` is membership in `gsCore` plus the packed
distance predicate. -/
theorem mem_gsFilteredCore_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpContext : GSInterpContext F} {rootContext : GSRootContext F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F} :
    p ∈ (gsFilteredCore points interpContext rootContext params radius).toList ↔
      p ∈ (gsCore points interpContext rootContext params).toList ∧
        passesCandidateDistance points radius p = true := by
  unfold gsFilteredCore
  simp

/-- Every filtered candidate is a sound algebraic core output and is within the
packed mismatch radius. -/
theorem gsFilteredCore_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpContext : GSInterpContext F} {rootContext : GSRootContext F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F}
    (hp : p ∈ (gsFilteredCore points interpContext rootContext params radius).toList) :
    exists Q,
      interpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius := by
  rcases (mem_gsFilteredCore_iff
      (interpContext := interpContext) (rootContext := rootContext)
      (params := params) (radius := radius) (p := p)).1 hp with
    ⟨hcore, hpass⟩
  rcases gsCore_sound (interpContext := interpContext)
      (rootContext := rootContext) (params := params) hcore with
    ⟨Q, hQ, hvalid, hdeg, hroot⟩
  exact ⟨Q, hQ, hvalid, hdeg, hroot, passesCandidateDistance_iff.mp hpass⟩

/-- Filtered-core completeness for candidates that root every valid
interpolation witness and pass the packed distance filter. -/
theorem gsFilteredCore_complete_of_roots_all_valid_witnesses {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpContext : GSInterpContext F} {rootContext : GSRootContext F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F}
    (hInterpExists : exists Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hrootAll :
      ∀ Q,
        ValidInterpolationWitness points params Q →
          CBivariate.composeY Q p = 0)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points interpContext rootContext params radius).toList := by
  rw [mem_gsFilteredCore_iff]
  exact ⟨gsCore_complete_of_roots_all_valid_witnesses
    (rootContext := rootContext) hInterpExists hpdeg hrootAll, hpass⟩

/-- Packed-point semantic completeness for the filtered GS core. -/
theorem gsFilteredCore_complete_of_enough_matches {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpContext : GSInterpContext F} {rootContext : GSRootContext F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F}
    (hInterpExists : exists Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches :
      params.weightedDegreeBound <
        params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points interpContext rootContext params radius).toList := by
  rw [mem_gsFilteredCore_iff]
  exact ⟨gsCore_complete_of_enough_matches (rootContext := rootContext)
    hInterpExists hpdeg hdistinct hmatches, hpass⟩

end GuruswamiSudan

end CompPoly
