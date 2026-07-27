/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Tower.Impl
import CompPoly.Univariate.Roots.Shoup
import Mathlib.Algebra.Field.ZMod

/-!
# Shoup-Style Univariate Root Tests

Focused executable coverage for the small-characteristic trace splitter over
`ZMod 2`, the degree-one binary-field case.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

namespace Univariate.Roots.Shoup

abbrev F2 := ZMod 2

instance : Fact (Nat.Prime 2) :=
  ⟨by decide⟩

private def f2ShoupCtx : SmallPrimeTraceContext F2 where
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

private def f2ShoupSplitter : LinearFactorProductSplitter F2 :=
  shoupLinearFactorProductSplitter f2ShoupCtx

private def rootsInF2 (p : CPolynomial F2) : Array F2 :=
  rootsInFiniteField f2ShoupCtx.toFiniteFieldContext f2ShoupSplitter p

private def f2NoRootQuadratic : CPolynomial F2 :=
  CPolynomial.ofArray #[(1 : F2), 1, 1]

private def f2AllRoots : CPolynomial F2 :=
  CPolynomial.linearFactor (0 : F2) * CPolynomial.linearFactor (1 : F2)

private def f2RepeatedRoots : CPolynomial F2 :=
  CPolynomial.linearFactor (0 : F2) *
    CPolynomial.linearFactor (0 : F2) *
      CPolynomial.linearFactor (1 : F2)

private def f2PartialRoots : CPolynomial F2 :=
  CPolynomial.linearFactor (0 : F2) * f2NoRootQuadratic

private def f2ZeroRootOnly : CPolynomial F2 :=
  CPolynomial.linearFactor (0 : F2)

private def allRootsOut : Array F2 :=
  rootsInF2 f2AllRoots

#guard allRootsOut.contains (0 : F2)
#guard allRootsOut.contains (1 : F2)
#guard allRootsOut.size == 2

private def repeatedRootsOut : Array F2 :=
  rootsInF2 f2RepeatedRoots

#guard repeatedRootsOut.contains (0 : F2)
#guard repeatedRootsOut.contains (1 : F2)
#guard repeatedRootsOut.size == 2

private def zeroRootOut : Array F2 :=
  rootsInF2 f2ZeroRootOnly

#guard zeroRootOut.contains (0 : F2)
#guard zeroRootOut.size == 1

#guard (rootsInF2 f2NoRootQuadratic).isEmpty

private def partialRootsOut : Array F2 :=
  rootsInF2 f2PartialRoots

#guard partialRootsOut.contains (0 : F2)
#guard !(partialRootsOut.contains (1 : F2))
#guard partialRootsOut.size == 1

abbrev BT0 := ConcreteBinaryTower.ConcreteBTField 0

private theorem bt0_card : Nat.card BT0 = 2 := by
  rw [Nat.card_eq_fintype_card]
  simpa [BT0] using
    (ConcreteBinaryTower.getBTFResult 0).fieldFintypeCard

private def bt0ShoupCtx : SmallPrimeTraceContext BT0 where
  q := 2
  finite := by infer_instance
  card_eq := bt0_card
  frobenius_fixed := by
    intro a
    have h := FiniteField.pow_card a
    simpa [bt0_card] using h
  p := 2
  k := 1
  p_prime := by decide
  q_eq := by decide
  baseConstants := #[(0 : BT0), 1]
  baseConstants_size := by rfl
  basis := #[(1 : BT0)]
  basis_size := by rfl
  traceValue := id
  traceValue_eq_powerSum := by
    intro z
    simp [tracePowerSum]
  traceValue_mem_base := by decide
  trace_separates := by
    intro a b hne
    refine ⟨(1 : BT0), by simp, ?_⟩
    simpa only [one_mul, id_eq] using (sub_ne_zero.mpr hne)

private def bt0ShoupSplitter : LinearFactorProductSplitter BT0 :=
  shoupLinearFactorProductSplitter bt0ShoupCtx

private def rootsInBT0 (p : CPolynomial BT0) : Array BT0 :=
  rootsInFiniteField bt0ShoupCtx.toFiniteFieldContext bt0ShoupSplitter p

private def bt0NoRootQuadratic : CPolynomial BT0 :=
  CPolynomial.ofArray #[(1 : BT0), 1, 1]

private def bt0AllRoots : CPolynomial BT0 :=
  CPolynomial.linearFactor (0 : BT0) * CPolynomial.linearFactor (1 : BT0)

private def bt0RepeatedRoots : CPolynomial BT0 :=
  CPolynomial.linearFactor (0 : BT0) *
    CPolynomial.linearFactor (0 : BT0) *
      CPolynomial.linearFactor (1 : BT0)

private def bt0PartialRoots : CPolynomial BT0 :=
  CPolynomial.linearFactor (0 : BT0) * bt0NoRootQuadratic

private def bt0AllRootsOut : Array BT0 :=
  rootsInBT0 bt0AllRoots

#guard bt0AllRootsOut.contains (0 : BT0)
#guard bt0AllRootsOut.contains (1 : BT0)
#guard bt0AllRootsOut.size == 2

private def bt0RepeatedRootsOut : Array BT0 :=
  rootsInBT0 bt0RepeatedRoots

#guard bt0RepeatedRootsOut.contains (0 : BT0)
#guard bt0RepeatedRootsOut.contains (1 : BT0)
#guard bt0RepeatedRootsOut.size == 2

#guard (rootsInBT0 bt0NoRootQuadratic).isEmpty

private def bt0PartialRootsOut : Array BT0 :=
  rootsInBT0 bt0PartialRoots

#guard bt0PartialRootsOut.contains (0 : BT0)
#guard !(bt0PartialRootsOut.contains (1 : BT0))
#guard bt0PartialRootsOut.size == 1

end Univariate.Roots.Shoup

end CompPolyTests
