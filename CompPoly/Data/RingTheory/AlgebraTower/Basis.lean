/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Data.RingTheory.AlgebraTower.Coordinates
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.AlgebraTower

/-!
# Bases from adjacent tower coordinates

`AlgebraTower.natBasis` is the basis determined by the executable equivalence
`AlgebraTower.natCoordinates`. Its `repr` is the coordinate map, and its vectors equal the
executable `AlgebraTower.natBasisVector` values.

`AlgebraTower.natBasisOfLE` provides the same basis at arbitrary endpoints `i ≤ j`,
with vectors in `A j` and coefficients in `A i`. Its representation agrees with
`AlgebraTower.natCoordinatesOfLE`, and `AlgebraTower.natBasisVectorOfLE` computes its vectors.

The successor basis agrees with `Module.Basis.smulTower'`, reindexed by `finProdFinEquiv`.
The old coordinate index varies fastest. Each vector is the embedded old basis vector
multiplied by the corresponding new successor basis vector. No normalization of that
successor vector is assumed.

The construction uses `Module.Basis.ofEquivFun` and the scalar-tower basis equations from
Mathlib's `Mathlib.RingTheory.AlgebraTower` module.
-/

public section

namespace AlgebraTower

variable {A : ℕ → Type*} [∀ k, CommSemiring (A k)] [t : AlgebraTower A]
  {d : ℕ → ℕ}
  (step : ∀ k, letI := t.toAlgebra (Nat.le_succ k)
    A (k + 1) ≃ₗ[A k] (Fin (d k) → A k))

/-- The basis whose coordinates are `natCoordinates`, over the action of the given tower map. -/
noncomputable def natBasis (i n : ℕ) :
    letI := t.toAlgebra (Nat.le_add_right i n)
    Module.Basis (Fin (coordinateSize d i n)) (A i) (A (i + n)) := by
  letI := t.toAlgebra (Nat.le_add_right i n)
  exact Module.Basis.ofEquivFun (natCoordinates step i n)

/-- The mathematical basis representation is the executable coordinate map. -/
@[simp]
theorem natBasis_repr (i n : ℕ) (x : A (i + n)) (j : Fin (coordinateSize d i n)) :
    letI := t.toAlgebra (Nat.le_add_right i n)
    (natBasis step i n).repr x j = natCoordinates step i n x j := by
  rfl

/-- Packing a unit coordinate vector gives the corresponding mathematical basis vector. -/
theorem natBasisVector_eq_natBasis (i n : ℕ) (j : Fin (coordinateSize d i n)) :
    natBasisVector step i n j = natBasis step i n j := by
  let := t.toAlgebra (Nat.le_add_right i n)
  apply (natBasis step i n).repr.injective
  ext idx
  rw [natBasis_repr, congrFun (natCoordinates_natBasisVector step i n j) idx,
    Module.Basis.repr_self]
  simp only [Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- The next relative basis is the scalar-tower composition of the previous basis and the
next successor basis, with the old index varying fastest. -/
theorem natBasis_succ (i n : ℕ) :
    letI := t.toAlgebra (Nat.le_add_right i n)
    letI := t.toAlgebra (Nat.le_succ (i + n))
    letI := t.toAlgebra (Nat.le_add_right i (n + 1))
    letI := toIsScalarTower t (Nat.le_add_right i n) (Nat.le_succ (i + n))
    natBasis step i (n + 1) =
      ((natBasis step i n).smulTower' (Module.Basis.ofEquivFun (step (i + n)))).reindex
        finProdFinEquiv := by
  let := t.toAlgebra (Nat.le_add_right i n)
  let := t.toAlgebra (Nat.le_succ (i + n))
  let := t.toAlgebra (Nat.le_add_right i (n + 1))
  let := toIsScalarTower t (Nat.le_add_right i n) (Nat.le_succ (i + n))
  apply Module.Basis.repr_injective
  ext x j
  exact natCoordinates_succ step i n x j

/-- At flattened index `oldIndex + oldSize * newIndex`, the vector is the embedded old
vector multiplied by the new successor vector. -/
theorem natBasisVector_succ (i n : ℕ) (b : Fin (d (i + n)))
    (j : Fin (coordinateSize d i n)) :
    natBasisVector step i (n + 1) (finProdFinEquiv (b, j)) =
      t.algebraMap (i + n) (i + n + 1) (Nat.le_succ (i + n)) (natBasisVector step i n j) *
        (step (i + n)).symm (Pi.single b 1) := by
  let := t.toAlgebra (Nat.le_add_right i n)
  let := t.toAlgebra (Nat.le_succ (i + n))
  let := t.toAlgebra (Nat.le_add_right i (n + 1))
  let := toIsScalarTower t (Nat.le_add_right i n) (Nat.le_succ (i + n))
  rw [natBasisVector_eq_natBasis, natBasis_succ]
  simp only [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.smulTower'_apply]
  rw [natBasisVector_eq_natBasis, Module.Basis.coe_ofEquivFun]
  rfl

/-- The basis at arbitrary comparable endpoints, over the action of the given tower map. -/
noncomputable def natBasisOfLE {i j : ℕ} (h : i ≤ j) :
    letI := t.toAlgebra h
    Module.Basis (Fin (coordinateSize d i (j - i))) (A i) (A j) := by
  letI := t.toAlgebra h
  exact Module.Basis.ofEquivFun (natCoordinatesOfLE step h)

/-- The endpoint basis representation is the executable endpoint coordinate map. -/
@[simp]
theorem natBasisOfLE_repr {i j : ℕ} (h : i ≤ j) (x : A j)
    (idx : Fin (coordinateSize d i (j - i))) :
    letI := t.toAlgebra h
    (natBasisOfLE step h).repr x idx = natCoordinatesOfLE step h x idx := by
  rfl

/-- Packing a unit coordinate vector computes the corresponding endpoint basis vector. -/
theorem natBasisVectorOfLE_eq_natBasisOfLE {i j : ℕ} (h : i ≤ j)
    (idx : Fin (coordinateSize d i (j - i))) :
    natBasisVectorOfLE step h idx = natBasisOfLE step h idx := by
  let := t.toAlgebra h
  apply (natBasisOfLE step h).repr.injective
  ext pos
  rw [natBasisOfLE_repr, congrFun (natCoordinatesOfLE_natBasisVectorOfLE step h idx) pos,
    Module.Basis.repr_self]
  simp only [Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- Endpoint basis vectors agree with the height-indexed basis after identifying the endpoints. -/
theorem natBasisOfLE_apply {i j : ℕ} (h : i ≤ j)
    (idx : Fin (coordinateSize d i (j - i))) :
    natBasisOfLE step h idx =
      cast (congrArg A (Nat.add_sub_of_le h)) (natBasis step i (j - i) idx) := by
  rw [← natBasisVectorOfLE_eq_natBasisOfLE, natBasisVectorOfLE_eq_natBasisVector,
    natBasisVector_eq_natBasis]

/-- At equal endpoints the unique basis vector is one. -/
@[simp]
theorem natBasisOfLE_self (i : ℕ) (idx : Fin (coordinateSize d i (i - i))) :
    natBasisOfLE step (Nat.le_refl i) idx = 1 := by
  rw [← natBasisVectorOfLE_eq_natBasisOfLE, natBasisVectorOfLE_self]

end AlgebraTower
