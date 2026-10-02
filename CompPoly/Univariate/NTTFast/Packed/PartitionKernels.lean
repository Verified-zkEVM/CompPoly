/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.Builders
public import CompPoly.Univariate.NTTFast.Packed.ArrayLemmas
import Mathlib.Tactic.IntervalCases

/-! # Coordinate formulas for partition kernels -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The sixteen-entry partition batch appends the indexed scalar formula. -/
theorem splitStepLeftField_eq (a w : Array KoalaBear.Fast.Field) (i j : USize) (out : Array
    KoalaBear.Fast.Field) :
    splitStepLeftField a w i j out =
      out ++ Array.ofFn (fun k : Fin 16 ↦ a.getD (i.toNat + k.val) 0 + a.getD (j.toNat + k.val)
        0) := by
  unfold splitStepLeftField readField fieldAdd
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide)]
  congr 1
  apply Array.ext
  · simp only [size_literal16, Array.size_ofFn]
  · intro k hk hj
    have hlt : k < 16 := by simpa only [Array.size_ofFn] using hj
    rw [Array.getElem_ofFn]
    interval_cases k <;> rfl

/-- The sixteen-entry partition batch appends the indexed scalar formula. -/
theorem splitStepRightField_eq (a w : Array KoalaBear.Fast.Field) (i j : USize) (out : Array
    KoalaBear.Fast.Field) :
    splitStepRightField a w i j out =
      out ++ Array.ofFn (fun k : Fin 16 ↦ w.getD (i.toNat + k.val) 0 * (a.getD (i.toNat + k.val)
        0 - a.getD (j.toNat + k.val) 0)) := by
  unfold splitStepRightField readField fieldMul fieldSub
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide)]
  congr 1
  apply Array.ext
  · simp only [size_literal16, Array.size_ofFn]
  · intro k hk hj
    have hlt : k < 16 := by simpa only [Array.size_ofFn] using hj
    rw [Array.getElem_ofFn]
    interval_cases k <;> rfl

/-- The sixteen-entry partition batch appends the indexed scalar formula. -/
theorem splitInputStepLeftField_eq (a w : Array KoalaBear.Fast.Field) (i j : USize) (out : Array
    KoalaBear.Fast.Field) :
    splitInputStepLeftField a w i j out =
      out ++ Array.ofFn (fun k : Fin 16 ↦ a.getD (i.toNat + k.val) 0 + a.getD (j.toNat + k.val)
        0) := by
  unfold splitInputStepLeftField readField fieldAdd
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide)]
  congr 1
  apply Array.ext
  · simp only [size_literal16, Array.size_ofFn]
  · intro k hk hj
    have hlt : k < 16 := by simpa only [Array.size_ofFn] using hj
    rw [Array.getElem_ofFn]
    interval_cases k <;> rfl

/-- The sixteen-entry partition batch appends the indexed scalar formula. -/
theorem splitInputStepRightField_eq (a w : Array KoalaBear.Fast.Field) (i j : USize) (out : Array
    KoalaBear.Fast.Field) :
    splitInputStepRightField a w i j out =
      out ++ Array.ofFn (fun k : Fin 16 ↦ w.getD (i.toNat + k.val) 0 * (a.getD (i.toNat + k.val)
        0 - a.getD (j.toNat + k.val) 0)) := by
  unfold splitInputStepRightField readField fieldMul fieldSub
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide)]
  congr 1
  apply Array.ext
  · simp only [size_literal16, Array.size_ofFn]
  · intro k hk hj
    have hlt : k < 16 := by simpa only [Array.size_ofFn] using hj
    rw [Array.getElem_ofFn]
    interval_cases k <;> rfl

end CompPoly.CPolynomial.NTTFast.Packed
