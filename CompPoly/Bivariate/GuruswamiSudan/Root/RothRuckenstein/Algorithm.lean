/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Common

/-!
# Roth-Ruckenstein-Style Root Finding

Executable bounded-degree roots for `CBivariate F` using recursive coefficient
reconstruction and an explicit univariate field-root backend, following the
Roth-Ruckenstein root-search step [RR00].

## References

* [Roth, R. M., and Ruckenstein, G., *Efficient decoding of Reed-Solomon codes
    beyond half the minimum distance*][RR00]
-/

namespace CompPoly

namespace GuruswamiSudan

open CBivariate

/-- Substitute `Y = a + X * Y` into a bivariate polynomial. -/
def substituteYRootPlusXY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a : F) : CBivariate F :=
  Id.run do
    let mut out : CBivariate F := default
    for y in [0:Q.val.size] do
      let coeffY := Q.val.coeff y
      for x in [0:coeffY.val.size] do
        let coeff := coeffY.coeff x
        for t in [0:y + 1] do
          out := out +
            CBivariate.monomialXY (x + t) t
              (coeff * (Nat.choose y t : F) * a ^ (y - t))
    pure out

/-- One residual step in the transformed Roth-Ruckenstein recursion. -/
def transformedRothRuckensteinResidual {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a : F) : CBivariate F :=
  CBivariate.stripXAdicFactor (substituteYRootPlusXY Q a)

/-- The linear coefficient of the next recursive root equation after depth zero. -/
def nextCoefficientSlope {F : Type*} [Field F]
    (Q : CBivariate F) (pref : CPolynomial F) : F :=
  (List.range' 1 Q.val.size).foldl
    (fun acc (y : Nat) ↦
      acc + (y : F) * CBivariate.coeff Q 0 y * pref.coeff 0 ^ (y - 1))
    0

/-- Polynomial equation for the next coefficient in the prefix recursion. -/
def nextCoefficientPolynomial {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (pref : CPolynomial F) (depth : Nat) : CPolynomial F :=
  if depth = 0 then
    initialCoefficientPolynomial Q
  else
    CPolynomial.ofArray
      #[CBivariate.composeYCoeff Q pref depth, nextCoefficientSlope Q pref]

/-- Ordered recursive candidate extensions using a field-root backend.

This direct coefficient-equation helper does not expand zero equations. The
residual-transform Roth-Ruckenstein backend uses residual normalization before
field-root queries.
-/
def rootPrefixExtensionsWithFieldRootContext {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (depth : Nat)
    (prefixes : Array (CPolynomial F)) : List (CPolynomial F) :=
  prefixes.toList.flatMap fun pref ↦
    (rootsInFieldForNonzeroEquation fieldRoots
      (nextCoefficientPolynomial Q pref depth)).toList.map
      fun coeff ↦ extendPrefix pref depth coeff

/-- Candidate prefixes after choosing coefficients through depth `< k` in the
direct coefficient-equation recursion. Zero equations are not expanded. -/
def rothRuckensteinRootPrefixes {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) : Nat → Array (CPolynomial F)
  | 0 => #[0]
  | depth + 1 =>
      (rootPrefixExtensionsWithFieldRootContext fieldRoots Q depth
        (rothRuckensteinRootPrefixes fieldRoots Q depth)).toArray

/-- Residual-transform Roth-Ruckenstein prefixes with explicit recursion fuel. -/
def transformedRothRuckensteinRootPrefixesWithFuel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) :
    Nat → CBivariate F → Nat → CPolynomial F → Array (CPolynomial F)
  | 0, _Q, _depth, pref => #[pref]
  | fuel + 1, Q, depth, pref =>
      let Qnorm := CBivariate.stripXAdicFactor Q
      if Qnorm == (0 : CBivariate F) then
        #[]
      else
        (rootsInFieldForNonzeroEquation fieldRoots
            (initialCoefficientPolynomial Qnorm)).foldl
          (fun out coeff ↦
            out ++
              transformedRothRuckensteinRootPrefixesWithFuel fieldRoots fuel
                (transformedRothRuckensteinResidual Qnorm coeff)
                (depth + 1) (extendPrefix pref depth coeff))
          #[]

/-- Candidate prefixes from the residual-transform recursion through precision `X^k`. -/
def transformedRothRuckensteinRootPrefixes {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : Nat) :
    Array (CPolynomial F) :=
  transformedRothRuckensteinRootPrefixesWithFuel fieldRoots k Q 0 default

/-- Residual-transform Roth-Ruckenstein bounded-degree roots. -/
def transformedRothRuckensteinRootsYDegreeLt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : Nat) :
    Array (CPolynomial F) :=
  (transformedRothRuckensteinRootPrefixes fieldRoots Q k).filter fun p ↦
    isRootYDegreeLtBool Q k p

/-- Roth-Ruckenstein bounded-degree roots.

The public backend uses the residual-transform recursion, which strips common
`X`-adic factors before each field-root query. Zero univariate equations are
excluded from the field-root dependency for nonzero bivariate inputs.
-/
def rothRuckensteinRootsYDegreeLt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) (Q : CBivariate F) (k : Nat) :
    Array (CPolynomial F) :=
  transformedRothRuckensteinRootsYDegreeLt fieldRoots Q k

end GuruswamiSudan

end CompPoly
