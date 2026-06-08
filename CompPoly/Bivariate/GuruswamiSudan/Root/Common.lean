/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots

/-!
# Common Guruswami-Sudan Root Helpers

Executable helpers shared by bounded bivariate root backends.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- The coefficient of `Y^j` in `Q(0, Y)`, as a polynomial in the next root
coefficient. -/
def initialCoefficientPolynomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) : CPolynomial F :=
  (List.range Q.val.size).foldl
    (fun out y ↦ out + CPolynomial.monomial y (CBivariate.coeff Q 0 y))
    0

/-- Executable final check for the GS root condition. -/
def isRootYDegreeLtBool {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (Q : CBivariate F) (k : Nat) (p : CPolynomial F) : Bool :=
  degreeLtBool p k && CBivariate.composeYHorner Q p == 0

/-- Filter a candidate family to exact bounded-degree roots. -/
def rootsYDegreeLtFromCandidates {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (candidates : Array (CPolynomial F)) (Q : CBivariate F) (k : Nat) :
    Array (CPolynomial F) :=
  candidates.filter fun p ↦ isRootYDegreeLtBool Q k p

/-- Extend one candidate prefix by one coefficient at `X^depth`. -/
def extendPrefix {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (pref : CPolynomial F) (depth : Nat) (coeff : F) : CPolynomial F :=
  pref + CPolynomial.monomial depth coeff

/-- Truncate a polynomial to its first `n` coefficients. -/
def polynomialPrefix {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n : Nat) : CPolynomial R :=
  CPolynomial.truncate p n

/-- Query a field-root backend only for nonzero equations.

A zero equation imposes no restriction on the next coefficient. Enumerating all
field elements is unsuitable for large fields, so bounded-root backends use
residual normalization to avoid zero equations for nonzero bivariate inputs.
-/
def rootsInFieldForNonzeroEquation {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (fieldRoots : FieldRootContext F) (p : CPolynomial F) : Array F :=
  if p == 0 then #[] else fieldRoots.rootsInField p

end GuruswamiSudan

end CompPoly
