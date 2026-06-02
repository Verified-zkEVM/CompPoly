/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.FilterCorrectness

/-!
# Guruswami-Sudan Executable Decoder

Top-level executable API for the packed CompPoly Guruswami-Sudan decoder.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Backend-parametric filtered core exposed as a reusable executable context.

The context packages an executable filtered decoder together with its CompPoly
soundness and completeness contracts. -/
structure GSFilteredCoreContext
    (F : Type*) [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] where
  run :
    Array (F × F) →
    GSInterpParams →
    Nat →
    Array (CPolynomial F)
  sound :
    ∀ {points params radius p},
      p ∈ (run points params radius).toList →
        ∃ Q,
          ValidInterpolationWitness points params Q ∧
            degreeLt p params.messageDegree ∧
              CBivariate.composeY Q p = 0 ∧
                candidateMismatchCount points p ≤ radius
  complete :
    ∀ {points params radius p},
      (∃ Q, ValidInterpolationWitness points params Q) →
      DistinctXCoordinates points →
      degreeLt p params.messageDegree →
      params.weightedDegreeBound <
        params.multiplicity * matchingPointCount points p →
      passesCandidateDistance points radius p = true →
        p ∈ (run points params radius).toList

/-- Filtered-core context assembled from CompPoly interpolation and root backends. -/
def filteredCoreContextOfBackends
    {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (interp : GSInterpBackend F)
    (roots : GSRootBackend F) :
    GSFilteredCoreContext F where
  run := fun points params radius =>
    gsFilteredCore points interp roots params radius
  sound := by
    intro points params radius p hp
    rcases gsFilteredCore_sound
        (interpBackend := interp) (rootBackend := roots)
        (params := params) (radius := radius) hp with
      ⟨Q, _hQ, hvalid, hdeg, hroot, hdist⟩
    exact ⟨Q, hvalid, hdeg, hroot, hdist⟩
  complete := by
    intro points params radius p hInterpExists hdistinct hpdeg hmatches hpass
    apply gsFilteredCore_complete_of_enough_matches
        (interpBackend := interp) (rootBackend := roots)
    · exact hInterpExists
    · exact hpdeg
    · exact hdistinct
    · exact hmatches
    · exact hpass

/-- Packed received word accepted by the executable decoder. -/
structure GSReceivedWord (F : Type*) where
  points : Array (F × F)
deriving Repr

/-- Runtime length of a packed received word. -/
def GSReceivedWord.length {F : Type*} (w : GSReceivedWord F) : Nat :=
  w.points.size

/-- Explicit executable parameters for the parameterized decoder. -/
structure GSExecParams where
  interp : GSInterpParams
  radius : Nat
deriving Repr, BEq, DecidableEq

/-- Computable executable decoder with caller-supplied parameters. -/
def decodeWithParams
    {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F)
    (params : GSExecParams)
    (w : GSReceivedWord F) :
    Array (CPolynomial F) :=
  ctx.run w.points params.interp params.radius

/-- Parameter selector for the selector-backed executable decoder. -/
structure GSParamSelector where
  choose : Nat → Nat → Nat → Option GSExecParams

/-- Selector-backed executable decoder with parameters selected from `(k, w.length, e)`. -/
def decode
    {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ctx : GSFilteredCoreContext F)
    (selector : GSParamSelector)
    (k e : Nat)
    (w : GSReceivedWord F) :
    Array (CPolynomial F) :=
  match selector.choose k w.length e with
  | none => #[]
  | some params => decodeWithParams ctx params w

end GuruswamiSudan

end CompPoly
