/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas
import Mathlib.Algebra.Field.ZMod

/-!
# Las Vegas Univariate Root Tests

Deterministic probe coverage for the phase-1 odd-field Las Vegas splitter.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

namespace Univariate.Roots.LasVegas

abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 5) :=
  ⟨by decide⟩

private def f5Ctx : FiniteFieldContext F5 where
  q := 5
  finite := by infer_instance
  card_eq := by
    simp [F5, Nat.card_eq_fintype_card, ZMod.card]
  frobenius_fixed := by decide

private def f5Elements : Array F5 :=
  #[0, 1, 2, 3, 4]

private theorem f5Elements_complete : ContainsAllFieldElements f5Elements := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def f5Enumeration : FieldEnumeration F5 :=
  fieldEnumerationOfArray f5Elements f5Elements_complete

private def xProbe : ProbeFamily F5 where
  probe _q _factor _attempt := CPolynomial.X

private def constantOneProbe : ProbeFamily F5 where
  probe _q _factor _attempt := CPolynomial.C (1 : F5)

private def failThenXProbe : ProbeFamily F5 where
  probe _q _factor attempt :=
    if attempt = 0 then CPolynomial.C (1 : F5) else CPolynomial.X

private def lvSplitter (cfg : LasVegasConfig) (probes : ProbeFamily F5) :
    LinearFactorProductSplitter F5 :=
  lasVegasLinearFactorProductSplitterWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    f5Ctx f5Enumeration cfg probes

private def hasExactlyRoots (roots expected : Array F5) : Bool :=
  roots.size == expected.size && expected.all fun a ↦ roots.contains a

private def twoRootProduct : CPolynomial F5 :=
  CPolynomial.linearFactor (1 : F5) * CPolynomial.linearFactor (2 : F5)

private def immediateFactors : Array (CPolynomial F5) :=
  (lvSplitter { cutoff := 3 } xProbe).splitLinearFactors 5 twoRootProduct

private def immediateRoots : Array F5 :=
  CPolynomial.rootsFromLinearFactors twoRootProduct immediateFactors

#guard hasExactlyRoots immediateRoots #[(1 : F5), (2 : F5)]

private def failThenSplitFactors : Array (CPolynomial F5) :=
  (lvSplitter { cutoff := 3 } failThenXProbe).splitLinearFactors 5 twoRootProduct

private def failThenSplitRoots : Array F5 :=
  CPolynomial.rootsFromLinearFactors twoRootProduct failThenSplitFactors

#guard hasExactlyRoots failThenSplitRoots #[(1 : F5), (2 : F5)]

private def cutoffFallbackFactors : Array (CPolynomial F5) :=
  (lvSplitter { cutoff := 0 } constantOneProbe).splitLinearFactors 5 twoRootProduct

private def cutoffFallbackRoots : Array F5 :=
  CPolynomial.rootsFromLinearFactors twoRootProduct cutoffFallbackFactors

#guard hasExactlyRoots cutoffFallbackRoots #[(1 : F5), (2 : F5)]

private def publicRoots (p : CPolynomial F5) : Array F5 :=
  CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    f5Ctx (lvSplitter { cutoff := 3 } xProbe) p

#guard publicRoots 0 == #[]
#guard publicRoots (CPolynomial.C (3 : F5)) == #[]
#guard publicRoots (CPolynomial.linearFactor (4 : F5)) == #[(4 : F5)]

private def repeatedRootPolynomial : CPolynomial F5 :=
  CPolynomial.linearFactor (1 : F5) *
    CPolynomial.linearFactor (1 : F5) *
      CPolynomial.linearFactor (3 : F5)

#guard hasExactlyRoots (publicRoots repeatedRootPolynomial) #[(1 : F5), (3 : F5)]

private def noRootPolynomial : CPolynomial F5 :=
  CPolynomial.ofArray #[(2 : F5), 0, 1]

#guard publicRoots noRootPolynomial == #[]

end Univariate.Roots.LasVegas

end CompPolyTests
