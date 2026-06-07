/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas
import Mathlib.Algebra.Field.ZMod

/-!
# Las Vegas Univariate Root Tests

Deterministic probe coverage for odd-field Las Vegas splitting and the
characteristic-two trace branch.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

namespace Univariate.Roots.LasVegas

abbrev F2 := ZMod 2

abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 2) :=
  ⟨by decide⟩

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

private def hasExactlyRoots {F : Type*} [BEq F] (roots expected : Array F) : Bool :=
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

private def f2TraceCtx : SmallPrimeTraceContext F2 where
  q := 2
  finite := by infer_instance
  card_eq := by
    simp [F2, Nat.card_eq_fintype_card, ZMod.card]
  frobenius_fixed := by decide
  p := 2
  k := 1
  p_prime := by decide
  q_eq := by decide
  baseConstants := #[(0 : F2), 1]
  baseConstants_size := by rfl
  basis := #[(1 : F2)]
  basis_size := by rfl
  traceValue := id
  traceValue_eq_powerSum := by
    intro z
    simp [tracePowerSum]
  traceValue_mem_base := by decide
  trace_separates := by
    intro a b hne
    refine ⟨(1 : F2), by simp, ?_⟩
    simpa only [one_mul, id_eq] using (sub_ne_zero.mpr hne)

private def f2ElementsReversed : Array F2 :=
  #[(1 : F2), 0]

private theorem f2ElementsReversed_complete :
    ContainsAllFieldElements f2ElementsReversed := by
  unfold ContainsAllFieldElements
  intro a
  fin_cases a <;> decide

private def f2Enumeration : FieldEnumeration F2 :=
  fieldEnumerationOfArray f2ElementsReversed f2ElementsReversed_complete

private def xProbeF2 : ProbeFamily F2 where
  probe _q _factor _attempt := CPolynomial.X

private def constantOneProbeF2 : ProbeFamily F2 where
  probe _q _factor _attempt := CPolynomial.C (1 : F2)

private def failThenXProbeF2 : ProbeFamily F2 where
  probe _q _factor attempt :=
    if attempt = 0 then CPolynomial.C (1 : F2) else CPolynomial.X

private def lvTraceSplitter (cfg : LasVegasConfig) (probes : ProbeFamily F2) :
    LinearFactorProductSplitter F2 :=
  lasVegasLinearFactorProductSplitterWithTrace
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    f2TraceCtx.toFiniteFieldContext f2Enumeration f2TraceCtx cfg probes

private def lvNoTraceSplitter (cfg : LasVegasConfig) (probes : ProbeFamily F2) :
    LinearFactorProductSplitter F2 :=
  lasVegasLinearFactorProductSplitterWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    f2TraceCtx.toFiniteFieldContext f2Enumeration cfg probes

private def f2TwoRootProduct : CPolynomial F2 :=
  CPolynomial.linearFactor (0 : F2) * CPolynomial.linearFactor (1 : F2)

private def f2TraceFactorOrder : Array (CPolynomial F2) :=
  #[CPolynomial.linearFactor (0 : F2), CPolynomial.linearFactor (1 : F2)]

private def f2FallbackFactorOrder : Array (CPolynomial F2) :=
  #[CPolynomial.linearFactor (1 : F2), CPolynomial.linearFactor (0 : F2)]

private def immediateTraceFactors : Array (CPolynomial F2) :=
  (lvTraceSplitter { cutoff := 2 } xProbeF2).splitLinearFactors 2 f2TwoRootProduct

#guard immediateTraceFactors == f2TraceFactorOrder

private def failThenTraceFactors : Array (CPolynomial F2) :=
  (lvTraceSplitter { cutoff := 2 } failThenXProbeF2).splitLinearFactors 2 f2TwoRootProduct

#guard failThenTraceFactors == f2TraceFactorOrder

private def cutoffFallbackTraceFactors : Array (CPolynomial F2) :=
  (lvTraceSplitter { cutoff := 1 } constantOneProbeF2).splitLinearFactors 2 f2TwoRootProduct

#guard cutoffFallbackTraceFactors == f2FallbackFactorOrder

private def missingTraceMetadataFallbackFactors : Array (CPolynomial F2) :=
  (lvNoTraceSplitter { cutoff := 2 } xProbeF2).splitLinearFactors 2 f2TwoRootProduct

#guard missingTraceMetadataFallbackFactors == f2FallbackFactorOrder

private def publicRootsF2 (p : CPolynomial F2) : Array F2 :=
  CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    f2TraceCtx.toFiniteFieldContext (lvTraceSplitter { cutoff := 2 } xProbeF2) p

#guard publicRootsF2 0 == #[]
#guard publicRootsF2 (CPolynomial.C (1 : F2)) == #[]
#guard publicRootsF2 (CPolynomial.linearFactor (1 : F2)) == #[(1 : F2)]

private def repeatedRootPolynomialF2 : CPolynomial F2 :=
  CPolynomial.linearFactor (0 : F2) *
    CPolynomial.linearFactor (0 : F2) *
      CPolynomial.linearFactor (1 : F2)

#guard hasExactlyRoots (publicRootsF2 repeatedRootPolynomialF2) #[(0 : F2), (1 : F2)]

private def noRootPolynomialF2 : CPolynomial F2 :=
  CPolynomial.ofArray #[(1 : F2), 1, 1]

#guard publicRootsF2 noRootPolynomialF2 == #[]

end Univariate.Roots.LasVegas

end CompPolyTests
