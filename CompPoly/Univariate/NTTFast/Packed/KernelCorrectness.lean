/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Expressions
public import CompPoly.Univariate.NTTFast.Packed.LeafLayers
import Mathlib.Tactic.IntervalCases

/-! # Mathematical correctness of the fused final layers -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Expressions

/-- The four final DIF layers on one sixteen-coordinate block. -/
def leaf16Stages [Field R] (t3 t2 t1 : Array R) (a : Array R)
    (base : Nat) : Array R :=
  layer16_1 #[1] (layer16_2 t1 (layer16_4 t2 (layer16_8 t3 a base) base) base) base

set_option maxRecDepth 8192 in
set_option maxHeartbeats 600000 in
/-- The fused final-layer expression graph equals four ordinary DIF stages. -/
theorem leaf16Field_eq_stages [Field R] (t3 t2 t1 : Array R)
    (a : Array R) (i : USize) (hi : i.toNat + 16 ≤ a.size)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    leaf16Field t3 t2 t1 i a = leaf16Stages t3 t2 t1 a i.toNat := by
  unfold leaf16Field leaf16Stages readField fieldAdd fieldSub fieldMul
  simp only [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
    Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide), Native.usize_numeral
    4 (by decide), Native.usize_numeral 5 (by decide), Native.usize_numeral 6 (by decide),
    Native.usize_numeral 7 (by decide), Native.usize_numeral 8 (by decide), Native.usize_numeral
    9 (by decide), Native.usize_numeral 10 (by decide), Native.usize_numeral 11 (by decide),
    Native.usize_numeral 12 (by decide), Native.usize_numeral 13 (by decide),
    Native.usize_numeral 14 (by decide), Native.usize_numeral 15 (by decide)]
  apply array_eq_of_getD _ _ (0 : R)
  · simp (disch := omega) only [size_splice16, size_layer16_1, size_layer16_2,
      size_layer16_4, size_layer16_8]
  · intro k
    rw [getD_splice _ _ _ (by change i.toNat + 16 ≤ a.size; exact hi)]
    by_cases hk : i.toNat ≤ k ∧ k < i.toNat + 16
    · obtain ⟨offset, ho, he⟩ : ∃ offset, offset < 16 ∧ k = i.toNat + offset := by
        exact ⟨k - i.toNat, by omega, by omega⟩
      subst k
      interval_cases offset <;>
        simp (disch := (first | (simp -failIfUnchanged only [size_layer16_1, size_layer16_2,
          size_layer16_4, size_layer16_8] <;> omega) | fail)) only
          [getD_layer16_1, getD_layer16_2, getD_layer16_4, getD_layer16_8, getD_layer16_1_zero,
            getD_layer16_2_zero,
            getD_layer16_4_zero, getD_layer16_8_zero, layer16Value,
            Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
            Nat.reduceLT, Nat.add_sub_cancel_left, Nat.sub_self, Nat.add_zero,
            ite_eq_left, ite_eq_right, ↓reduceIte, getD_toArray, size_literal16,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, h3, h2, h1, one_mul]
    · simp (disch := (first | (simp -failIfUnchanged only [size_layer16_1, size_layer16_2,
        size_layer16_4, size_layer16_8] <;> omega) | fail)) only
        [getD_layer16_1_outside, getD_layer16_2_outside, getD_layer16_4_outside,
          getD_layer16_8_outside, size_literal16, ite_eq_right, ite_self]

end CompPoly.CPolynomial.NTTFast.Packed.Expressions
