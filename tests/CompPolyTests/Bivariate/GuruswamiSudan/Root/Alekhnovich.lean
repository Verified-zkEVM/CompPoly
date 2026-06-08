/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Alekhnovich Root Tests

Regression coverage for the Alekhnovich bounded bivariate root backend.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.GuruswamiSudan

namespace GuruswamiSudan.Root.Alekhnovich

private def stringContainsNeedle (haystack needle : String) : Bool :=
  1 < (haystack.splitOn needle).length

#eval show IO Unit from do
  let source ← IO.FS.readFile
    "CompPoly/Bivariate/GuruswamiSudan/Root/Alekhnovich/Algorithm.lean"
  let forbidden := #[
    "Root.RothRuckenstein.Algorithm",
    "transformedRothRuckensteinRootPrefixes",
    "transformedRothRuckensteinRootsYDegreeLt",
    "rothRuckensteinRootPrefixes",
    "rothRuckensteinRootsYDegreeLt"
  ]
  for needle in forbidden do
    if stringContainsNeedle source needle then
      throw <| IO.userError s!"forbidden Roth fallback reference in Alekhnovich: {needle}"

abbrev F3 := ZMod 3
abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

instance : Fact (Nat.Prime 5) :=
  ⟨by decide⟩

private def f3Elements : Array F3 :=
  #[0, 1, 2]

private theorem f3Elements_complete : ContainsAllFieldElements f3Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def fieldRoots : FieldRootContext F3 :=
  enumeratingFieldRootContext F3 f3Elements f3Elements_complete

private def f5Elements : Array F5 :=
  #[0, 1, 2, 3, 4]

private theorem f5Elements_complete : ContainsAllFieldElements f5Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def f5FieldRoots : FieldRootContext F5 :=
  enumeratingFieldRootContext F5 f5Elements f5Elements_complete

private def qYMinusX : CBivariate F3 :=
  CBivariate.Y + CBivariate.monomialXY 1 0 2

private def pX : CPolynomial F3 :=
  CPolynomial.monomial 1 1

private def emptyRootPrefixF3 : RootPrefix F3 :=
  { prefixPoly := 0, precision := 0 }

private def qXTimesYMinusX : CBivariate F3 :=
  CBivariate.monomialXY 1 1 1 + CBivariate.monomialXY 1 0 2

private def pOne : CPolynomial F3 :=
  CPolynomial.C 1

#guard pX ∈ (alekhnovichRootsYDegreeLt fieldRoots qYMinusX 2).toList
#guard pX ∈
  (finishAlekhnovichPrefixWithAlekhnovich fieldRoots qYMinusX 2
    emptyRootPrefixF3).toList
#guard pOne ∈ (alekhnovichRootsYDegreeLt fieldRoots qXTimesYMinusX 2).toList
#guard (alekhnovichRootsYDegreeLt fieldRoots (0 : CBivariate F3) 2).isEmpty

private def pXPlusOne : CPolynomial F5 :=
  CPolynomial.ofArray #[(1 : F5), 1]

private def pTwoXPlusTwo : CPolynomial F5 :=
  CPolynomial.ofArray #[(2 : F5), 2]

private def qTwoLinearYFactors : CBivariate F5 :=
  CBivariate.linearYDivisor pXPlusOne * CBivariate.linearYDivisor pTwoXPlusTwo

private def twoLinearAlekhnovichRoots : Array (CPolynomial F5) :=
  alekhnovichRootsYDegreeLt f5FieldRoots qTwoLinearYFactors 2

#guard pXPlusOne ∈ twoLinearAlekhnovichRoots.toList
#guard pTwoXPlusTwo ∈ twoLinearAlekhnovichRoots.toList

private def repeatedRootQ : CBivariate F5 :=
  CBivariate.linearYDivisor pXPlusOne * CBivariate.linearYDivisor pXPlusOne

private def repeatedAlekhnovichRoots : Array (CPolynomial F5) :=
  alekhnovichRootsYDegreeLt f5FieldRoots repeatedRootQ 2

#guard repeatedAlekhnovichRoots.size == 1
#guard pXPlusOne ∈ repeatedAlekhnovichRoots.toList

private def noRootQ : CBivariate F3 :=
  CBivariate.Y * CBivariate.Y + CBivariate.CC 1

#guard (alekhnovichRootsYDegreeLt fieldRoots noRootQ 2).isEmpty

private def samePolynomialSet {F : Type*} [Zero F] [BEq F]
    (xs ys : Array (CPolynomial F)) : Bool :=
  xs.all (fun p ↦ ys.contains p) && ys.all (fun p ↦ xs.contains p)

#guard samePolynomialSet
  (alekhnovichRootsYDegreeLt f5FieldRoots qTwoLinearYFactors 2)
  (rothRuckensteinRootsYDegreeLt f5FieldRoots qTwoLinearYFactors 2)

#guard samePolynomialSet
  (alekhnovichRootsYDegreeLt f5FieldRoots repeatedRootQ 2)
  (rothRuckensteinRootsYDegreeLt f5FieldRoots repeatedRootQ 2)

end GuruswamiSudan.Root.Alekhnovich

end CompPolyTests
