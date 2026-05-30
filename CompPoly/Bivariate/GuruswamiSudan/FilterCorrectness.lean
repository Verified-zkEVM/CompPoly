/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness

/-!
# Guruswami-Sudan Candidate Filter Correctness

Correctness and completeness lemmas for the generic packed filtering layer above
the algebraic `gsCore`.
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
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F} :
    p ∈ (gsFilteredCore points interpBackend rootBackend params radius).toList ↔
      p ∈ (gsCore points interpBackend rootBackend params).toList ∧
        passesCandidateDistance points radius p = true := by
  unfold gsFilteredCore
  simp

/-- Every filtered candidate is a sound algebraic core output and is within the
packed mismatch radius. -/
theorem gsFilteredCore_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F}
    (hp : p ∈ (gsFilteredCore points interpBackend rootBackend params radius).toList) :
    exists Q,
      interpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius := by
  rcases (mem_gsFilteredCore_iff
      (interpBackend := interpBackend) (rootBackend := rootBackend)
      (params := params) (radius := radius) (p := p)).1 hp with
    ⟨hcore, hpass⟩
  rcases gsCore_sound (interpBackend := interpBackend)
      (rootBackend := rootBackend) (params := params) hcore with
    ⟨Q, hQ, hvalid, hdeg, hroot⟩
  exact ⟨Q, hQ, hvalid, hdeg, hroot, passesCandidateDistance_iff.mp hpass⟩

/-- Filtered-core completeness for candidates that root every valid
interpolation witness and pass the packed distance filter. -/
theorem gsFilteredCore_complete_of_roots_all_valid_witnesses {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F}
    (hInterpExists : exists Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hrootAll :
      ∀ Q,
        ValidInterpolationWitness points params Q →
          CBivariate.composeY Q p = 0)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points interpBackend rootBackend params radius).toList := by
  rw [mem_gsFilteredCore_iff]
  exact ⟨gsCore_complete_of_roots_all_valid_witnesses
    (rootBackend := rootBackend) hInterpExists hpdeg hrootAll, hpass⟩

/-- Packed-point semantic completeness for the filtered GS core. -/
theorem gsFilteredCore_complete_of_enough_matches {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams} {radius : Nat}
    {p : CPolynomial F}
    (hInterpExists : exists Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches :
      params.weightedDegreeBound <
        params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points interpBackend rootBackend params radius).toList := by
  rw [mem_gsFilteredCore_iff]
  exact ⟨gsCore_complete_of_enough_matches (rootBackend := rootBackend)
    hInterpExists hpdeg hdistinct hmatches, hpass⟩

end GuruswamiSudan

end CompPoly
