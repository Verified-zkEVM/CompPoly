/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

import CompPoly.Fields.Binary.Tower.Concrete.BasisCoordinates

/-!
# Concrete basis-coordinate correspondence tests

Symbolic clients exercise arbitrary endpoints and the selected concrete scalar action.
Asymmetric coefficients distinguish the numeric basis order across skipped levels. The
128-bit cases retain bit 127, and a raw-word multiplication counterexample distinguishes
the field action from modular bitvector multiplication.
-/

namespace CompPolyTests.BinaryTowerBasisCoordinates

open ConcreteBinaryTower ConcreteBinaryTower.Coordinates

example {i j : ℕ} (h : i ≤ j) :
    let := ConcreteBTFieldAlgebra h
    (inferInstance : Algebra (ConcreteBTField i) (ConcreteBTField j)) =
      ConcreteBTFieldAlgebra h := rfl

example {i j : ℕ} (h : i ≤ j) (a : ConcreteBTField i) (x : ConcreteBTField j)
    (q : Fin (2 ^ (j - i))) :
    let := ConcreteBTFieldAlgebra h
    (multilinearBasis i j h).repr
      (@SMul.smul _ _ (ConcreteBTFieldAlgebra h).toSMul a x) q =
        a * coordinates h x q := by
  let := ConcreteBTFieldAlgebra h
  exact (multilinearBasis_repr h _ q).trans (coordinates_smul h a x q)

example (i : ℕ) (h : i ≤ i) (x : ConcreteBTField i)
    (q : Fin (2 ^ (i - i))) :
    let := ConcreteBTFieldAlgebra h
    letI : Module (ConcreteBTField i) (ConcreteBTField i) :=
      (ConcreteBTFieldAlgebra h).toModule
    (multilinearBasis i i h).repr x q = x := by
  let := ConcreteBTFieldAlgebra h
  let : Module (ConcreteBTField i) (ConcreteBTField i) :=
    (ConcreteBTFieldAlgebra h).toModule
  rw [multilinearBasis_repr, coordinates_self]

example (i : ℕ) (h : i ≤ i) (q : Fin (2 ^ (i - i))) :
    multilinearBasis i i h q = 1 := by
  rw [← pack_single_eq_multilinearBasis, pack_self]
  have hq : q = 0 := by
    apply Fin.ext
    have hq := q.isLt
    simp only [Nat.sub_self, pow_zero] at hq
    simpa only [Fin.val_zero] using (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hq))
  rw [hq, Pi.single_eq_same]

-- The two middle coefficients differ, so exchanging the generator order changes the result.
example :
    let := ConcreteBTFieldAlgebra (show 1 ≤ 3 by decide)
    (multilinearBasis 1 3 (by decide)).repr (fromNat (k := 3) 121) =
      Finsupp.equivFunOnFinite.symm ![fromNat 1, fromNat 2, fromNat 3, fromNat 1] := by
  let := ConcreteBTFieldAlgebra (show 1 ≤ 3 by decide)
  ext q
  rw [multilinearBasis_repr, Finsupp.coe_equivFunOnFinite_symm]
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

example :
    let := ConcreteBTFieldAlgebra (show 1 ≤ 3 by decide)
    (multilinearBasis 1 3 (by decide)).repr (fromNat (k := 3) 121) 1 ≠
      (multilinearBasis 1 3 (by decide)).repr (fromNat (k := 3) 121) 2 := by
  let := ConcreteBTFieldAlgebra (show 1 ≤ 3 by decide)
  rw [multilinearBasis_repr, multilinearBasis_repr,
    coordinates_eq_setWidth_ushiftRight, coordinates_eq_setWidth_ushiftRight]
  decide +kernel

example : multilinearBasis 1 3 (by decide) 2 = fromNat (k := 3) 16 := by
  apply (coordinates (show 1 ≤ 3 by decide)).injective
  rw [coordinates_multilinearBasis]
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

example :
    (∑ q : Fin 4, concreteTowerAlgebraMap 1 3 (by decide)
      (![fromNat 1, fromNat 2, fromNat 3, fromNat 1] q) *
        multilinearBasis 1 3 (by decide) q) = fromNat (k := 3) 121 := by
  refine (pack_eq_sum_multilinearBasis (show 1 ≤ 3 by decide)
    ![fromNat 1, fromNat 2, fromNat 3, fromNat 1]).symm.trans ?_
  apply (coordinates (show 1 ≤ 3 by decide)).injective
  rw [coordinates_pack]
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

example :
    let := ConcreteBTFieldAlgebra (show 6 ≤ 7 by decide)
    ((multilinearBasis 6 7 (by decide)).repr
      (fromNat (k := 7) (2 ^ 127 + 9 * 2 ^ 64 + 2 ^ 63 + 5)) 1).toBitVec.getLsbD 63 = true := by
  let := ConcreteBTFieldAlgebra (show 6 ≤ 7 by decide)
  rw [multilinearBasis_repr, getLsbD_coordinates _ _ _ _ (by decide)]
  decide +kernel

example :
    (∑ q : Fin 2, concreteTowerAlgebraMap 6 7 (by decide)
      (![fromNat (2 ^ 63 + 5), fromNat (2 ^ 63 + 9)] q) *
        multilinearBasis 6 7 (by decide) q) =
      fromNat (k := 7) (2 ^ 127 + 9 * 2 ^ 64 + 2 ^ 63 + 5) := by
  refine (pack_eq_sum_multilinearBasis (show 6 ≤ 7 by decide)
    ![fromNat (2 ^ 63 + 5), fromNat (2 ^ 63 + 9)]).symm.trans ?_
  apply (coordinates (show 6 ≤ 7 by decide)).injective
  rw [coordinates_pack]
  ext q
  fin_cases q <;> rw [coordinates_eq_setWidth_ushiftRight] <;> decide +kernel

private theorem scalar_word :
    @SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
      (fromNat (k := 1) 3) (fromNat (k := 2) 13) = fromNat (k := 2) 11 := by
  change concreteTowerAlgebraMap 1 2 (Nat.le_succ 1) (fromNat (k := 1) 3) *
    fromNat (k := 2) 13 = _
  rw [concreteTowerAlgebraMap_succ_1]
  change concrete_mul (fromNat (k := 2) 3) (fromNat (k := 2) 13) = _
  simp only [concrete_mul.eq_1, Nat.reduceEqDiff, Nat.reduceSub, ↓reduceDIte]
  decide +kernel

-- The field action gives raw word 11; modular multiplication gives raw word 7.
example :
    let := ConcreteBTFieldAlgebra (Nat.le_succ 1)
    (multilinearBasis 1 2 (Nat.le_succ 1)).repr
      (@SMul.smul _ _ (ConcreteBTFieldAlgebra (Nat.le_succ 1)).toSMul
        (fromNat (k := 1) 3) (fromNat (k := 2) 13)) 1 ≠
      (multilinearBasis 1 2 (Nat.le_succ 1)).repr
        (ConcreteBTField.ofBitVec
          (BitVec.mul (fromNat (k := 2) 3).toBitVec (fromNat (k := 2) 13).toBitVec)) 1 := by
  let := ConcreteBTFieldAlgebra (Nat.le_succ 1)
  rw [scalar_word, multilinearBasis_repr, multilinearBasis_repr,
    coordinates_eq_setWidth_ushiftRight, coordinates_eq_setWidth_ushiftRight]
  decide +kernel

end CompPolyTests.BinaryTowerBasisCoordinates
