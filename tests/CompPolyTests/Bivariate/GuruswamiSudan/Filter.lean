/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Filter
import Mathlib.Algebra.Field.ZMod

/-!
# Guruswami-Sudan Filter Tests

Focused executable checks for packed candidate mismatch filtering.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Filter

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def points : Array (Prod F3 F3) :=
  #[(0, 0), (1, 1), (2, 0)]

private def pX : CPolynomial F3 :=
  CPolynomial.monomial 1 1

#guard candidateMismatchCount points pX == 1

#guard matchingPointCount points pX == 2

#guard passesCandidateDistance points 1 pX

#guard !passesCandidateDistance points 0 pX

private def params : GSInterpParams :=
  { messageDegree := 2, multiplicity := 1, weightedDegreeBound := 2 }

private def corePoints : Array (Prod F3 F3) :=
  #[(0, 0), (1, 1)]

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private theorem f3Elements_complete : ContainsAllFieldElements f3Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def fieldRoots : FieldRootBackend F3 :=
  enumeratingFieldRootBackend F3 f3Elements f3Elements_complete

private def rootBackend : GSRootBackend F3 :=
  rothRuckensteinRootBackend F3 fieldRoots

#guard gsFilteredCore corePoints (denseInterpBackend F3) rootBackend params 0 ==
  (gsCore corePoints (denseInterpBackend F3) rootBackend params).filter
    (passesCandidateDistance corePoints 0)

end GuruswamiSudan.Filter

end CompPolyTests
