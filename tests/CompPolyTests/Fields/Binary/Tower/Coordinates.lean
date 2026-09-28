/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.Coordinates
import CompPoly.Data.RingTheory.AlgebraTower.Coordinates

/-!
# Concrete binary tower coordinate tests

Symbolic clients exercise successor coordinates and the generic endpoint API with the actual
concrete tower scalar actions. Asymmetric raw words distinguish low-first order, retain both
64-bit halves, and distinguish the field scalar action from modular bitvector multiplication.
-/

namespace CompPolyTests.BinaryTowerCoordinates

open ConcreteBinaryTower ConcreteBinaryTower.Coordinates AlgebraTower

-- The coordinate adapter retains the existing field and predecessor algebra dictionaries.
example (k : ℕ) : (inferInstance : Field (ConcreteBTField k)) = instFieldConcrete := rfl

example (k : ℕ) :
    (inferInstance : Algebra (ConcreteBTField k) (ConcreteBTField (k + 1))) =
      ConcreteBTFieldAlgebra (Nat.le_succ k) := rfl

example (k : ℕ) (x : ConcreteBTField (k + 1)) (c : Fin 2 → ConcreteBTField k) :
    (succCoordinates k).symm (succCoordinates k x) = x ∧
      succCoordinates k ((succCoordinates k).symm c) = c :=
  ⟨(succCoordinates k).symm_apply_apply x, (succCoordinates k).apply_symm_apply c⟩

example (k : ℕ) (x : ConcreteBTField (k + 1)) (j : Fin 2) :
    natCoordinates succCoordinates k 1 x j = succCoordinates k x j := by
  rw [natCoordinates_succ, natCoordinates_zero]
  fin_cases j <;> rfl

example {i j : ℕ} (h : i ≤ j) (x : ConcreteBTField j) :
    natPackOfLE succCoordinates h (natCoordinatesOfLE succCoordinates h x) = x :=
  natPackOfLE_natCoordinatesOfLE succCoordinates h x

example {i j : ℕ} (h : i ≤ j)
    (c : Fin (coordinateSize (fun _ => 2) i (j - i)) → ConcreteBTField i) :
    natCoordinatesOfLE succCoordinates h (natPackOfLE succCoordinates h c) = c :=
  natCoordinatesOfLE_natPackOfLE succCoordinates h c

example {i j : ℕ} (h : i ≤ j) (a : ConcreteBTField i) (x : ConcreteBTField j) :
    natCoordinatesOfLE succCoordinates h
      (@SMul.smul _ _ (ConcreteBTFieldAlgebra h).toSMul a x) =
        a • natCoordinatesOfLE succCoordinates h x :=
  (natCoordinatesOfLE succCoordinates h).map_smul a x

example (i : ℕ) (h : i ≤ i) (a x : ConcreteBTField i)
    (j : Fin (coordinateSize (fun _ => 2) i (i - i))) :
    natCoordinatesOfLE succCoordinates h
      (@SMul.smul _ _ (ConcreteBTFieldAlgebra h).toSMul a x) j = a * x := by
  rw [natCoordinatesOfLE_self]
  change concreteTowerAlgebraMap i i h a * x = a * x
  rw [concreteTowerAlgebraMap_id]
  rfl

example (k : ℕ) (x : ConcreteBTField (k + 2)) :
    (natCoordinatesConstOfLE succCoordinates (show k ≤ k + 2 by omega)).symm
      (natCoordinatesConstOfLE succCoordinates (show k ≤ k + 2 by omega) x) = x :=
  (natCoordinatesConstOfLE succCoordinates (show k ≤ k + 2 by omega)).symm_apply_apply x

-- Two successor steps keep the old coordinate index fastest.
example : natCoordinatesConstOfLE succCoordinates (show 1 ≤ 3 by decide)
    (fromNat (k := 3) 121) = ![fromNat 1, fromNat 2, fromNat 3, fromNat 1] := by
  ext j
  fin_cases j <;>
    simp only [natCoordinatesConstOfLE_apply, natCoordinatesOfLE_apply,
      natCoordinates_succ, natCoordinates_zero, succCoordinates_apply] <;>
    decide +kernel

-- Word nine has different constant and generator coefficients; reversing them is detectable.
example : succCoordinates 1 (fromNat (k := 2) 9) = ![fromNat 1, fromNat 2] := by
  rw [succCoordinates_apply]
  decide +kernel

example : succCoordinates 1 (fromNat (k := 2) 9) ≠ ![fromNat 2, fromNat 1] := by
  rw [succCoordinates_apply]
  decide +kernel

example : ((succCoordinates 1).symm ![fromNat 1, fromNat 2]).toNat = 9 := by
  rw [succCoordinates_symm_apply]
  decide +kernel

example : (joinSucc 6 (fromNat (2 ^ 63 + 5)) (fromNat (2 ^ 62 + 9))).toNat =
    2 ^ 126 + 9 * 2 ^ 64 + 2 ^ 63 + 5 := by
  decide +kernel

-- The tower field action gives 14; multiplying the raw bitvectors would give 2 instead.
private theorem scalar_word :
    @SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
      (fromNat (k := 1) 2) (fromNat (k := 2) 9) = fromNat (k := 2) 14 := by
  change concreteTowerAlgebraMap 1 2 (Nat.le_succ 1) (fromNat (k := 1) 2) *
    fromNat (k := 2) 9 = _
  rw [concreteTowerAlgebraMap_succ_1]
  change concrete_mul (fromNat (k := 2) 2) (fromNat (k := 2) 9) = _
  simp only [concrete_mul.eq_1, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceDIte]
  decide +kernel

example : succCoordinates 1
    (@SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
      (fromNat (k := 1) 2) (fromNat (k := 2) 9)) = ![fromNat 2, fromNat 3] := by
  rw [scalar_word, succCoordinates_apply]
  decide +kernel

example : (2 : ConcreteBTField 1) ≠ fromNat (k := 1) 2 := by
  decide +kernel

end CompPolyTests.BinaryTowerCoordinates
