/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.RelativeCoordinates

/-!
# Concrete endpoint coordinate tests

Symbolic clients check arbitrary endpoints and the chosen concrete tower actions. Raw-word
examples check low-first coefficient order, all 128 bits, and the distinction between field
multiplication and modular bitvector multiplication. A bit-index counterexample checks the
bound in bitwise readback.
-/

namespace CompPolyTests.BinaryTowerRelativeCoordinates

open ConcreteBinaryTower ConcreteBinaryTower.Coordinates

example (k : ℕ) : (inferInstance : Field (ConcreteBTField k)) = instFieldConcrete := rfl

example {i j : ℕ} (h : i ≤ j) :
    letI := ConcreteBTFieldAlgebra h
    (inferInstance : Algebra (ConcreteBTField i) (ConcreteBTField j)) =
      ConcreteBTFieldAlgebra h := rfl

example {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j)
    (c : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    pack h (coordinates h x) = x ∧ coordinates h (pack h c) = c :=
  ⟨pack_coordinates h x, coordinates_pack h c⟩

example (i : ℕ) (h : i ≤ i) (x : ConcreteBTField i)
    (q : Fin (2 ^ (i - i))) : coordinates h x q = x := coordinates_self i h x q

example (i : ℕ) (h : i ≤ i) (c : Fin (2 ^ (i - i)) → ConcreteBTField i) :
    pack h c = c 0 := pack_self i h c

example (k : ℕ) (x : ConcreteBTField (k + 1)) :
    coordinates (Nat.le_succ k) x 0 =
      ConcreteBTField.ofBitVec (x.toBitVec.setWidth (2 ^ k)) := by
  rw [coordinates_eq_setWidth_ushiftRight]
  simp only [Fin.val_zero, Nat.mul_zero, BitVec.ushiftRight_eq, BitVec.ushiftRight_zero]

example (k : ℕ) (x : ConcreteBTField (k + 2)) (q : Fin (2 ^ (k + 2 - k))) :
    coordinates (show k ≤ k + 2 by omega) x q =
      ConcreteBTField.ofBitVec ((BitVec.ushiftRight x.toBitVec (2 ^ k * q.val)).setWidth (2 ^ k)) :=
  coordinates_eq_setWidth_ushiftRight _ x q

-- All operations here elaborate to the concrete field and the explicitly selected endpoint action.
example {i j : ℕ} (h : i ≤ j) (a : ConcreteBTField i) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    letI : Field (ConcreteBTField i) := instFieldConcrete
    coordinates h (@SMul.smul _ _ (ConcreteBTFieldAlgebra h).toSMul a x) q =
      a * coordinates h x q := coordinates_smul h a x q

example {i j : ℕ} (h : i ≤ j) (a : ConcreteBTField i)
    (c : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    pack h (fun q => a * c q) =
      @SMul.smul _ _ (ConcreteBTFieldAlgebra h).toSMul a (pack h c) := pack_smul h a c

example {i j : ℕ} (h : i ≤ j) (x y : ConcreteBTField j) :
    coordinates h (x + y) = coordinates h x + coordinates h y := coordinates_add h x y

example {i j : ℕ} (h : i ≤ j) (c d : Fin (2 ^ (j - i)) → ConcreteBTField i) :
    pack h (c + d) = pack h c + pack h d := pack_add h c d

example (i : ℕ) (h : i ≤ i) (a x : ConcreteBTField i)
    (q : Fin (2 ^ (i - i))) :
    coordinates h (@SMul.smul _ _ (ConcreteBTFieldAlgebra h).toSMul a x) q = a * x := by
  calc
    _ = a * coordinates h x q := coordinates_smul h a x q
    _ = a * x := congrArg (fun z => a * z) (coordinates_self i h x q)

-- Two successor steps retain the order [1, 2, 3, 1], including the old index varying fastest.
example : coordinates (show 1 ≤ 3 by decide) (fromNat (k := 3) 121) =
    ![fromNat 1, fromNat 2, fromNat 3, fromNat 1] := by
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

example : coordinates (show 1 ≤ 3 by decide) (fromNat (k := 3) 121) ≠
    ![fromNat 1, fromNat 3, fromNat 2, fromNat 1] := by
  intro h
  have h₁ := congrFun h 1
  rw [coordinates_eq_setWidth_ushiftRight] at h₁
  contradiction

example : pack (show 1 ≤ 3 by decide)
    ![fromNat 1, fromNat 2, fromNat 3, fromNat 1] = fromNat (k := 3) 121 := by
  apply (coordinates (show 1 ≤ 3 by decide)).injective
  rw [coordinates_pack]
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

example : coordinates (show 6 ≤ 7 by decide)
    (fromNat (k := 7) (2 ^ 127 + 9 * 2 ^ 64 + 2 ^ 63 + 5)) =
      ![fromNat (2 ^ 63 + 5), fromNat (2 ^ 63 + 9)] := by
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

example : (coordinates (show 6 ≤ 7 by decide)
    (fromNat (k := 7) (2 ^ 127 + 9 * 2 ^ 64 + 2 ^ 63 + 5)) 1).toBitVec.getLsbD 63 = true := by
  rw [getLsbD_coordinates _ _ _ _ (by decide)]
  decide +kernel

example : (coordinates (show 1 ≤ 3 by decide) (fromNat (k := 3) 121) 2).toNat = 3 := by
  rw [toNat_coordinates]
  decide +kernel

-- Without the within-block bound, readback could incorrectly expose a neighboring block.
example : (coordinates (show 1 ≤ 2 by decide) (fromNat (k := 2) 4) 0).toBitVec.getLsbD 2 ≠
    (fromNat (k := 2) 4).toBitVec.getLsbD 2 := by
  rw [coordinates_eq_setWidth_ushiftRight]
  decide +kernel

private theorem scalar_word :
    @SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
      (fromNat (k := 1) 2) (fromNat (k := 2) 9) = fromNat (k := 2) 14 := by
  change concreteTowerAlgebraMap 1 2 (Nat.le_succ 1) (fromNat (k := 1) 2) *
    fromNat (k := 2) 9 = _
  rw [concreteTowerAlgebraMap_succ_1]
  change concrete_mul (fromNat (k := 2) 2) (fromNat (k := 2) 9) = _
  simp only [concrete_mul.eq_1, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceDIte]
  decide +kernel

example : coordinates (Nat.le_succ 1)
    (@SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
      (fromNat (k := 1) 2) (fromNat (k := 2) 9)) = ![fromNat 2, fromNat 3] := by
  rw [scalar_word]
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

-- Modular bitvector multiplication would produce raw word two instead of field word fourteen.
example : @SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
    (fromNat (k := 1) 2) (fromNat (k := 2) 9) ≠ fromNat (k := 2) 2 := by
  rw [scalar_word]
  decide +kernel

example : (2 : ConcreteBTField 1) ≠ fromNat (k := 1) 2 := by decide +kernel

end CompPolyTests.BinaryTowerRelativeCoordinates
