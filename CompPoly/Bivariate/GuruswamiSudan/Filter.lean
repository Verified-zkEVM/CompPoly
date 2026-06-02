/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Core

/-!
# Guruswami-Sudan Candidate Filtering

Generic packed-point filtering for algebraic `gsCore` outputs.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Number of packed points where `p(x)` differs from the supplied `y`. -/
def candidateMismatchCount {F : Type*} [Semiring F] [BEq F]
    (points : Array (Prod F F)) (p : CPolynomial F) : Nat :=
  points.foldl
    (fun count point ↦
      if CPolynomial.eval point.1 p == point.2 then count else count + 1)
    0

/-- Number of packed points where `p(x)` matches the supplied `y`. -/
def matchingPointCount {F : Type*} [Semiring F] [BEq F]
    (points : Array (Prod F F)) (p : CPolynomial F) : Nat :=
  points.foldl
    (fun count point ↦
      if CPolynomial.eval point.1 p == point.2 then count + 1 else count)
    0

/-- Boolean distance predicate for packed candidate filtering. -/
def passesCandidateDistance {F : Type*} [Semiring F] [BEq F]
    (points : Array (Prod F F)) (radius : Nat) (p : CPolynomial F) : Bool :=
  decide (candidateMismatchCount points p ≤ radius)

/-- Packed input points have no duplicate `x`-coordinates. -/
def DistinctXCoordinates {F : Type*} (points : Array (Prod F F)) : Prop :=
  (points.toList.map fun point ↦ point.1).Nodup

/-- Run the algebraic GS core and keep only candidates within the packed
mismatch radius. -/
def gsFilteredCore {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (points : Array (Prod F F))
    (interpContext : GSInterpContext F)
    (rootContext : GSRootContext F)
    (params : GSInterpParams)
    (radius : Nat) : Array (CPolynomial F) :=
  (gsCore points interpContext rootContext params).filter
    (passesCandidateDistance points radius)

end GuruswamiSudan

end CompPoly
