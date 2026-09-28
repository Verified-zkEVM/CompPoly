/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Algebra

/-!
# Successor coordinates for concrete binary tower fields

`ConcreteBinaryTower.Coordinates.succCoordinates k` identifies level `k + 1` with two
coefficients in level `k`, ordered as the constant coefficient followed by the coefficient
of the new generator `Z (k + 1)`. Its scalar action is induced by the existing tower map
from level `k` to level `k + 1`.

The underlying `split` and `join` functions use high/low order. The executable `low`, `high`,
and `joinSucc` adapters expose low/high order and their bodies for direct word reduction.
The linear equivalence is characterized by its application and inverse-application lemmas.
The decomposition and linearity proofs use the existing algebraic expansion lemmas in
`CompPoly.Fields.Binary.Tower.Concrete.Algebra`.

These successor equivalences can be passed to `AlgebraTower.natCoordinatesOfLE` from
`CompPoly.Data.RingTheory.AlgebraTower.Coordinates` to obtain coordinates between any ordered
pair of levels.

The tower and constant-first successor expansion are described in [DP23], §2.3.
The paper's generator `X_k` corresponds to `Z (k + 1)` here.

## References

* [Diamond, B. E. and Posen, J., *Succinct arguments over towers of binary fields*][DP23]
-/

public section

namespace ConcreteBinaryTower.Coordinates

/-- The constant coefficient of a level-`k + 1` word, stored in its low `2 ^ k` bits. -/
@[expose] def low (k : ℕ) (x : ConcreteBTField (k + 1)) : ConcreteBTField k :=
  (split (by omega) x).2

/-- The coefficient of `Z (k + 1)`, stored in the high `2 ^ k` bits of the word. -/
@[expose] def high (k : ℕ) (x : ConcreteBTField (k + 1)) : ConcreteBTField k :=
  (split (by omega) x).1

/-- Construct a level-`k + 1` word with constant coefficient `lo` and generator coefficient `hi`. -/
@[expose] def joinSucc (k : ℕ) (lo hi : ConcreteBTField k) : ConcreteBTField (k + 1) :=
  join (by omega) hi lo

/-- Reading the low coefficient after joining recovers it. -/
@[simp] theorem low_joinSucc (k : ℕ) (lo hi : ConcreteBTField k) :
    low k (joinSucc k lo hi) = lo :=
  congrArg Prod.snd (split_join_eq_split (k := k + 1) (by omega) hi lo)

/-- Reading the high coefficient after joining recovers it. -/
@[simp] theorem high_joinSucc (k : ℕ) (lo hi : ConcreteBTField k) :
    high k (joinSucc k lo hi) = hi :=
  congrArg Prod.fst (split_join_eq_split (k := k + 1) (by omega) hi lo)

/-- Joining the two coefficients recovers the original word. -/
@[simp] theorem joinSucc_low_high (k : ℕ) (x : ConcreteBTField (k + 1)) :
    joinSucc k (low k x) (high k x) = x :=
  join_split_eq_join (by omega) x

/-- The low coefficient preserves the canonical field addition. -/
theorem low_add (k : ℕ) (x y : ConcreteBTField (k + 1)) :
    low k (x + y) = low k x + low k y :=
  congrArg Prod.snd (split_sum_eq_sum_split (k := k + 1) (by omega)
    x y (high k x) (low k x) (high k y) (low k y) rfl rfl)

/-- The high coefficient preserves the canonical field addition. -/
theorem high_add (k : ℕ) (x y : ConcreteBTField (k + 1)) :
    high k (x + y) = high k x + high k y :=
  congrArg Prod.fst (split_sum_eq_sum_split (k := k + 1) (by omega)
    x y (high k x) (low k x) (high k y) (low k y) rfl rfl)

/-- A joined word is the sum of its embedded constant and generator terms. -/
theorem joinSucc_eq_map_mul_add (k : ℕ) (lo hi : ConcreteBTField k) :
    joinSucc k lo hi =
      concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k) hi * Z (k + 1) +
        concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k) lo := by
  rw [joinSucc, join_eq_join_via_add_smul]
  rfl

/-- The action induced by the tower embedding multiplies both coefficients by the scalar. -/
theorem smul_joinSucc (k : ℕ) (a lo hi : ConcreteBTField k) :
    letI := ConcreteBTFieldAlgebra (Nat.le_succ k)
    a • joinSucc k lo hi = joinSucc k (a * lo) (a * hi) := by
  let := ConcreteBTFieldAlgebra (Nat.le_succ k)
  change concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k) a * joinSucc k lo hi = _
  simp only [joinSucc_eq_map_mul_add, map_mul, mul_add, mul_assoc]

/-- The constant coefficient commutes with the scalar action induced by the tower embedding. -/
theorem low_smul (k : ℕ) (a : ConcreteBTField k) (x : ConcreteBTField (k + 1)) :
    letI := ConcreteBTFieldAlgebra (Nat.le_succ k)
    low k (a • x) = a * low k x := by
  let := ConcreteBTFieldAlgebra (Nat.le_succ k)
  conv_lhs => rw [← joinSucc_low_high k x, smul_joinSucc, low_joinSucc]

/-- The generator coefficient commutes with the scalar action induced by the tower embedding. -/
theorem high_smul (k : ℕ) (a : ConcreteBTField k) (x : ConcreteBTField (k + 1)) :
    letI := ConcreteBTFieldAlgebra (Nat.le_succ k)
    high k (a • x) = a * high k x := by
  let := ConcreteBTFieldAlgebra (Nat.le_succ k)
  conv_lhs => rw [← joinSucc_low_high k x, smul_joinSucc, high_joinSucc]

/-- Coordinates `(constant coefficient, generator coefficient)` for the scalar action
induced by the tower embedding from level `k` to level `k + 1`. -/
def succCoordinates (k : ℕ) :
    letI := ConcreteBTFieldAlgebra (Nat.le_succ k)
    ConcreteBTField (k + 1) ≃ₗ[ConcreteBTField k] (Fin 2 → ConcreteBTField k) := by
  letI := ConcreteBTFieldAlgebra (Nat.le_succ k)
  exact {
    toFun := fun x => ![low k x, high k x]
    invFun := fun c => joinSucc k (c 0) (c 1)
    map_add' := fun x y => by
      ext j
      fin_cases j
      · exact low_add k x y
      · exact high_add k x y
    map_smul' := fun a x => by
      ext j
      fin_cases j
      · exact low_smul k a x
      · exact high_smul k a x
    left_inv := fun x => joinSucc_low_high k x
    right_inv := fun c => by
      ext j
      fin_cases j
      · exact low_joinSucc k (c 0) (c 1)
      · exact high_joinSucc k (c 0) (c 1) }

/-- The forward function is exactly low/high readback, in that order. -/
@[simp] theorem succCoordinates_apply (k : ℕ) (x : ConcreteBTField (k + 1)) :
    succCoordinates k x = ![low k x, high k x] := by
  rfl

/-- The inverse constructs a word with constant coefficient `c 0` and generator coefficient
`c 1`. -/
@[simp] theorem succCoordinates_symm_apply (k : ℕ) (c : Fin 2 → ConcreteBTField k) :
    (succCoordinates k).symm c = joinSucc k (c 0) (c 1) := by
  rfl

end ConcreteBinaryTower.Coordinates
