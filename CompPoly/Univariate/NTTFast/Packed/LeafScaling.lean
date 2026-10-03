/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.KernelCorrectness
public import CompPoly.Univariate.NTTFast.Packed.Scaling

/-! # Inverse normalization in the fused final-layer kernel -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Expressions

/-- The ordinary fused leaf preserves the working array's size. -/
@[simp] theorem size_leaf16Field [Field R] (t3 t2 t1 : Array R) (i : USize)
    (a : Array R) (hi : i.toNat + 16 ≤ a.size) : (leaf16Field t3 t2 t1 i a).size = a.size := by
  unfold leaf16Field
  exact size_splice16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi

/-- The normalized fused leaf preserves the working array's size. -/
@[simp] theorem size_leaf16ScaledField [Field R] (t3 t2 t1 : Array R) (i : USize)
    (nInv : R) (a : Array R) (hi : i.toNat + 16 ≤ a.size) :
    (leaf16ScaledField t3 t2 t1 i nInv a).size = a.size := by
  unfold leaf16ScaledField
  exact size_splice16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi

set_option maxHeartbeats 300000 in
/-- Normalization changes each computed leaf coordinate by exactly the inverse-size factor. -/
theorem getD_leaf16ScaledField_inside [Field R] (t3 t2 t1 : Array R) (i : USize)
    (nInv : R) (a : Array R) (hi : i.toNat + 16 ≤ a.size)
    (k : Nat) (hk : i.toNat ≤ k ∧ k < i.toNat + 16) :
    (leaf16ScaledField t3 t2 t1 i nInv a).getD k 0 =
      nInv * (leaf16Field t3 t2 t1 i a).getD k 0 := by
  unfold leaf16ScaledField leaf16Field readField fieldAdd fieldSub fieldMul
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide)]
  rw [getD_splice _ _ _ (by change i.toNat + 16 ≤ a.size; exact hi),
    getD_splice _ _ _ (by change i.toNat + 16 ≤ a.size; exact hi)]
  obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 16 ∧ k = i.toNat + offset :=
    ⟨k - i.toNat, by omega, by omega⟩
  subst k
  interval_cases offset <;>
    simp (disch := omega) only [size_literal16, Nat.add_sub_cancel_left, Nat.sub_self,
      Nat.add_zero, ite_eq_left, ite_eq_right, getD_toArray,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]

/-- The normalized kernel leaves coordinates outside its block unchanged. -/
theorem getD_leaf16ScaledField_outside [Field R] (t3 t2 t1 : Array R) (i : USize)
    (nInv : R) (a : Array R) (hi : i.toNat + 16 ≤ a.size)
    (k : Nat) (hk : ¬(i.toNat ≤ k ∧ k < i.toNat + 16)) :
    (leaf16ScaledField t3 t2 t1 i nInv a).getD k 0 = a.getD k 0 := by
  unfold leaf16ScaledField
  rw [getD_splice _ _ _ (by change i.toNat + 16 ≤ a.size; exact hi)]
  simp (disch := omega) only [size_literal16, ite_eq_right, ite_self]

/-- The unnormalized leaf leaves all other blocks unchanged. -/
theorem getD_leaf16Field_outside [Field R] (t3 t2 t1 : Array R) (i : USize)
    (a : Array R) (hi : i.toNat + 16 ≤ a.size) (k : Nat)
    (hk : ¬(i.toNat ≤ k ∧ k < i.toNat + 16)) :
    (leaf16Field t3 t2 t1 i a).getD k 0 = a.getD k 0 := by
  unfold leaf16Field
  rw [getD_splice _ _ _ (by change i.toNat + 16 ≤ a.size; exact hi)]
  simp (disch := omega) only [size_literal16, ite_eq_right, ite_self]

/-- Fusing normalization multiplies precisely the finished local transform's coordinates. -/
theorem leaf16ScaledField_eq_scaleSegment [Field R] (t3 t2 t1 : Array R) (i : USize)
    (factor : R) (a : Array R) (hi : i.toNat + 16 ≤ a.size) :
    leaf16ScaledField t3 t2 t1 i factor a =
      scaleSegment (leaf16Field t3 t2 t1 i a) i.toNat 16 factor := by
  apply array_eq_of_getD _ _ (0 : R)
  · rw [size_leaf16ScaledField _ _ _ _ _ _ hi,
      size_scaleSegment,
      size_leaf16Field _ _ _ _ _ hi]
  · intro k
    rw [getD_scaleSegment]
    by_cases hk : i.toNat ≤ k ∧ k < i.toNat + 16
    · rw [ite_eq_left hk, getD_leaf16ScaledField_inside _ _ _ _ _ _ hi k hk]
    · rw [ite_eq_right hk, getD_leaf16ScaledField_outside _ _ _ _ _ _ hi k hk,
        getD_leaf16Field_outside _ _ _ _ _ hi k hk]

end CompPoly.CPolynomial.NTTFast.Packed.Expressions
