/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Enumeration
import Mathlib.Algebra.Field.ZMod

/-!
# Exhaustive Enumeration Root Tests

Executable coverage for lazy finite-field enumeration adapters over small
prime fields.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

namespace Univariate.Roots.Enumeration

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

private def f3Enumeration : FieldEnumeration F3 :=
  fieldEnumerationOfArray f3Elements f3Elements_complete

private def f3RootsPolynomial : CPolynomial F3 :=
  CPolynomial.linearFactor (0 : F3) * CPolynomial.linearFactor (2 : F3)

private def f3Roots : Array F3 :=
  rootsInFieldByEnumeration f3Enumeration f3RootsPolynomial

#guard f3Roots == #[(0 : F3), (2 : F3)]

private def f5Elements : Array F5 :=
  #[0, 1, 2, 3, 4]

private theorem f5Elements_complete : ContainsAllFieldElements f5Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def f5Enumeration : FieldEnumeration F5 :=
  fieldEnumerationOfArray f5Elements f5Elements_complete

private def f5RootsPolynomial : CPolynomial F5 :=
  CPolynomial.linearFactor (1 : F5) *
    CPolynomial.linearFactor (4 : F5) *
      CPolynomial.linearFactor (4 : F5)

private def f5Roots : Array F5 :=
  rootsInFieldByEnumeration f5Enumeration f5RootsPolynomial

#guard f5Roots == #[(1 : F5), (4 : F5)]

private def f5EnumerationSplitter : LinearFactorProductSplitter F5 :=
  enumeratingLinearFactorProductSplitter f5Enumeration

private def f5EnumerationFactors : Array (CPolynomial F5) :=
  f5EnumerationSplitter.splitLinearFactors 5 f5RootsPolynomial

#guard (CPolynomial.rootsFromLinearFactors f5RootsPolynomial f5EnumerationFactors).contains (1 : F5)
#guard (CPolynomial.rootsFromLinearFactors f5RootsPolynomial f5EnumerationFactors).contains (4 : F5)

end Univariate.Roots.Enumeration

end CompPolyTests
