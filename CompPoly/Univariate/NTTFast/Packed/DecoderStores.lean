/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.Decoder

/-! # Four-coordinate tiled decoder stores -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The optimized four-coordinate store is four ordinary array writes at consecutive indices. -/
theorem Native.setField4_eq_storeList (a : Array KoalaBear.Fast.Field) (i : USize)
    (x0 x1 x2 x3 : KoalaBear.Fast.Field) (ha : a.size < USize.size)
    (hi : i.toNat + 4 ≤ a.size) :
    Native.setField4 a i x0 x1 x2 x3 = storeList a i.toNat [x0, x1, x2, x3] := by
  have h3 : (i + 3).toNat = i.toNat + 3 := by
    rw [USize.toNat_add]
    change (i.toNat + (3 : USize).toNat) % USize.size = i.toNat + 3
    rw [Native.usize_numeral 3 (by decide), Nat.mod_eq_of_lt (by omega)]
  have has : a.usize.toNat = a.size := Nat.mod_eq_of_lt ha
  have hu : i ≤ i + 3 ∧ i + 3 < a.usize := by
    constructor
    · rw [USize.le_iff_toNat_le, h3]
      omega
    · rw [USize.lt_iff_toNat_lt, h3, has]
      omega
  have h1 : (i + 1).toNat = i.toNat + 1 := Plan.usize_add_one i (by omega)
  have h2 : (i + 2).toNat = i.toNat + 2 := by
    rw [USize.toNat_add]
    change (i.toNat + (2 : USize).toNat) % USize.size = i.toNat + 2
    rw [Native.usize_numeral 2 (by decide), Nat.mod_eq_of_lt (by omega)]
  unfold Native.setField4
  rw [dite_eq_left hu]
  simp only [Array.uset_eq_set, h1, h2, h3]
  symm
  have h0b : i.toNat < a.size := by omega
  have h1b : i.toNat + 1 < a.size := by omega
  have h2b : i.toNat + 2 < a.size := by omega
  have h3b : i.toNat + 3 < a.size := by omega
  simp only [storeList, Array.setIfInBounds, Nat.add_assoc, Nat.reduceAdd,
    Array.size_set, h0b, h1b, h2b, h3b, ↓reduceDIte]

/-- An optimized four-coordinate store preserves the output array's length. -/
theorem Native.size_setField4 (a : Array KoalaBear.Fast.Field) (i : USize)
    (x0 x1 x2 x3 : KoalaBear.Fast.Field) (ha : a.size < USize.size)
    (hi : i.toNat + 4 ≤ a.size) :
    (Native.setField4 a i x0 x1 x2 x3).size = a.size := by
  rw [Native.setField4_eq_storeList _ _ _ _ _ _ ha hi, size_storeList]

/-- Reading the four-coordinate store has the expected segment-write semantics. -/
theorem Native.getD_setField4 (a : Array KoalaBear.Fast.Field) (i : USize)
    (x0 x1 x2 x3 : KoalaBear.Fast.Field) (ha : a.size < USize.size)
    (hi : i.toNat + 4 ≤ a.size) (k : Nat) :
    (Native.setField4 a i x0 x1 x2 x3).getD k 0 =
      if k < i.toNat then a.getD k 0 else
      if k < i.toNat + 4 then [x0, x1, x2, x3][k - i.toNat]?.getD 0 else a.getD k 0 := by
  rw [Native.setField4_eq_storeList _ _ _ _ _ _ ha hi, getD_storeList]
  · rfl
  · exact hi

end CompPoly.CPolynomial.NTTFast.Packed
