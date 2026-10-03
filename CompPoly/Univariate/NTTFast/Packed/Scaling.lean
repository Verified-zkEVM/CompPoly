/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import Mathlib.Algebra.GroupWithZero.Defs

/-! # Normalization on a contiguous field-array segment -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Multiply exactly one contiguous segment by the inverse transform size. -/
def scaleSegment [Mul R] (a : Array R) (base count : Nat) (factor : R) : Array R :=
  a.mapIdx (fun i x ↦ if base ≤ i ∧ i < base + count then factor * x else x)

/-- Segment normalization preserves the array length. -/
@[simp] theorem size_scaleSegment [Mul R] (a : Array R) (base count : Nat) (factor : R) :
    (scaleSegment a base count factor).size = a.size := by
  exact Array.size_mapIdx

/-- Scaling an array commutes with reading with the zero default. -/
theorem getD_scaleMap [MulZeroClass R] (a : Array R) (factor : R) (k : Nat) :
    (a.map (fun x ↦ factor * x)).getD k 0 = factor * a.getD k 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? <;> simp only [Option.map_none, Option.map_some,
    Option.getD_none, Option.getD_some, MulZeroClass.mul_zero]

/-- Segment normalization changes exactly its own coordinates. -/
theorem getD_scaleSegment [MulZeroClass R] (a : Array R) (base count : Nat) (factor : R) (k : Nat) :
    (scaleSegment a base count factor).getD k 0 =
      if base ≤ k ∧ k < base + count then factor * a.getD k 0 else a.getD k 0 := by
  simp only [scaleSegment, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx]
  cases a[k]? <;> split <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
      MulZeroClass.mul_zero]

end CompPoly.CPolynomial.NTTFast.Packed
