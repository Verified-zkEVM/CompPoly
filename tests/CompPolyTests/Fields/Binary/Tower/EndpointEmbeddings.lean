/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.Algebra

/-!
# Concrete binary tower embedding tests

Symbolic self, adjacent, and skipped-level maps preserve their input words. The concrete
controls retain bit 127 and distinguish an embedded old generator from the new generator.
-/

namespace CompPolyTests.ConcreteTowerEmbeddings

open ConcreteBinaryTower

example {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField i) :
    (AlgebraTower.algebraMap (AT := ConcreteBTField) i j h x).toNat = x.toNat :=
  toNat_concreteTowerAlgebraMap h x

example (i : ℕ) (h : i ≤ i) (x : ConcreteBTField i) :
    concreteTowerAlgebraMap i i h x = x := by
  apply ConcreteBTField.toBitVec_injective
  rw [concreteTowerAlgebraMap_eq_setWidth, BitVec.setWidth_eq]

example (i : ℕ) (x : ConcreteBTField i) :
    (canonicalAlgMap (i + 1) (canonicalAlgMap i x)).toNat = x.toNat := by
  rw [toNat_canonicalAlgMap, toNat_canonicalAlgMap]

example (i : ℕ) (x : ConcreteBTField i) :
    (concreteTowerAlgebraMap i (i + 3) (by omega) x).toBitVec =
      x.toBitVec.setWidth (2 ^ (i + 3)) :=
  concreteTowerAlgebraMap_eq_setWidth _ x

example : (concreteTowerAlgebraMap 0 3 (by decide) (Z 0)).toBitVec = BitVec.ofNat 8 1 := by
  rw [concreteTowerAlgebraMap_eq_setWidth]
  decide +kernel

example : (concreteTowerAlgebraMap 7 8 (by decide)
    (ConcreteBTField.ofBitVec (BitVec.ofNat 128 (2 ^ 127 + 1)))).toBitVec =
      BitVec.ofNat 256 (2 ^ 127 + 1) := by
  rw [concreteTowerAlgebraMap_eq_setWidth]
  decide +kernel

example (j : ℕ) (h : 7 ≤ j) (x : ConcreteBTField 7) :
    (concreteTowerAlgebraMap 7 j h x).toBitVec.getLsbD 127 = x.toBitVec.getLsbD 127 := by
  rw [concreteTowerAlgebraMap_eq_setWidth, BitVec.getLsbD_setWidth]
  have hwidth : 2 ^ 7 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h
  simp only [show 127 < 2 ^ j by omega, decide_true, Bool.true_and]

example : (concreteTowerAlgebraMap 1 3 (by decide) (Z 1)).toBitVec = BitVec.ofNat 8 2 :=
  concreteTowerAlgebraMap_Z_succ (k := 0) (by decide)

-- Zero-extension retains the old generator rather than selecting the destination generator.
example : concreteTowerAlgebraMap 1 3 (by decide) (Z 1) ≠ Z 3 := by
  intro h
  have hw := congrArg ConcreteBTField.toNat h
  rw [toNat_concreteTowerAlgebraMap] at hw
  change BitVec.toNat (Z (0 + 1)) = BitVec.toNat (Z (2 + 1)) at hw
  rw [toNat_Z_succ, toNat_Z_succ] at hw
  exact (by decide : 2 ≠ 16) hw

end CompPolyTests.ConcreteTowerEmbeddings
