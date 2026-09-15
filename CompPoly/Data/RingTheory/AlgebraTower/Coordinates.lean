/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Data.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Coordinates along a natural-number-indexed algebra tower

Given linear coordinate equivalences between adjacent levels of an `AlgebraTower`,
`AlgebraTower.natCoordinates` gives coordinates at level `i + n` over level `i`. Each scalar
action is induced by the corresponding map of the given tower. The number of successor
coordinates may vary with the level, and may be zero when such an equivalence exists.

The old coordinate index varies fastest: a pair `(newIndex, oldIndex)` has flattened index
`oldIndex + oldSize * newIndex`. Constant successor coordinate count two gives the usual
least-significant-bit-first order.

`AlgebraTower.natPack` is the inverse coordinate map. `AlgebraTower.natBasisVector` packs
a unit coordinate vector. Both are executable, with no enumeration of the tower carriers.
The corresponding mathematical basis is constructed in
`CompPoly.Data.RingTheory.AlgebraTower.Basis`.

The construction uses `LinearEquiv.restrictScalars`, `LinearEquiv.piCongrRight`,
`LinearEquiv.curry`, and `finProdFinEquiv`.
-/

public section

namespace AlgebraTower

private def composeCoordinates {R S T : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    {m n : ℕ} (e : S ≃ₗ[R] (Fin m → R)) (f : T ≃ₗ[S] (Fin n → S)) :
    T ≃ₗ[R] (Fin (n * m) → R) :=
  (f.restrictScalars R).trans
    ((LinearEquiv.piCongrRight fun _ : Fin n => e).trans
      ((LinearEquiv.curry R R (Fin n) (Fin m)).symm.trans
        (LinearEquiv.funCongrLeft R R finProdFinEquiv.symm)))

/-- The number of coordinates from level `i` through `n` steps with chosen coordinate counts `d`.
The next step contributes a new outer block of coordinates. -/
abbrev coordinateSize (d : ℕ → ℕ) (i n : ℕ) : ℕ :=
  Nat.rec 1 (fun k size => d (i + k) * size) n

/-- An interval with no successor steps has one coordinate. -/
@[simp]
theorem coordinateSize_zero (d : ℕ → ℕ) (i : ℕ) : coordinateSize d i 0 = 1 := rfl

/-- The number of coordinates is multiplied by the next successor coordinate count. -/
@[simp]
theorem coordinateSize_succ (d : ℕ → ℕ) (i n : ℕ) :
    coordinateSize d i (n + 1) = d (i + n) * coordinateSize d i n := rfl

/-- A constant successor coordinate count `r` gives `r ^ n` coordinates over `n` steps. -/
theorem coordinateSize_const (r i n : ℕ) :
    coordinateSize (fun _ => r) i n = r ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [coordinateSize_succ, ih, pow_succ, Nat.mul_comm]

variable {A : ℕ → Type*} [∀ k, CommSemiring (A k)] [t : AlgebraTower A]
  {d : ℕ → ℕ}
  (step : ∀ k, letI := t.toAlgebra (Nat.le_succ k)
    A (k + 1) ≃ₗ[A k] (Fin (d k) → A k))

/-- Coordinates of `A (i + n)` over `A i`, obtained by composing adjacent equivalences.

The scalar action is induced by the given tower map from `i` to `i + n`. At each step,
the old index varies fastest, so `(b, j)` is placed at `j + oldSize * b`. -/
def natCoordinates (i : ℕ) : (n : ℕ) →
    letI := t.toAlgebra (Nat.le_add_right i n)
    A (i + n) ≃ₗ[A i] (Fin (coordinateSize d i n) → A i)
  | 0 => by
      -- Capture the coefficient action before installing the chosen self action.
      letI : Module (A i) (Fin (coordinateSize d i 0) → A i) := inferInstance
      letI : Module (A i) (A i) := (t.toAlgebra (Nat.le_add_right i 0)).toModule
      let z : Fin (coordinateSize d i 0) := ⟨0, by change 0 < 1; decide⟩
      exact {
        toFun := fun x _ => x
        invFun := fun c => c z
        map_add' := fun _ _ => rfl
        map_smul' := fun a x => by
          funext j
          change t.algebraMap i i (Nat.le_add_right i 0) a * x = a * x
          rw [algebraMap_self_apply]
        left_inv := fun _ => rfl
        right_inv := fun c => by
          funext j
          have hj : j = z := Fin.ext (by
            have h : j.val < 1 := j.isLt
            change j.val = 0
            omega)
          subst j
          rfl }
  | n + 1 => by
      letI := t.toAlgebra (Nat.le_add_right i n)
      letI := t.toAlgebra (Nat.le_succ (i + n))
      letI := t.toAlgebra (Nat.le_add_right i (n + 1))
      letI := toIsScalarTower t (Nat.le_add_right i n) (Nat.le_succ (i + n))
      exact composeCoordinates (natCoordinates i n) (step (i + n))

/-- At height zero the single coordinate is the original element. -/
@[simp]
theorem natCoordinates_zero (i : ℕ) (x : A i) (j : Fin (coordinateSize d i 0)) :
    natCoordinates step i 0 x j = x := by
  rfl

/-- Read the new outer coordinate, then the old inner coordinate.
Division selects the outer block and remainder selects the position within that block. -/
theorem natCoordinates_succ (i n : ℕ) (x : A (i + (n + 1)))
    (j : Fin (coordinateSize d i (n + 1))) :
    natCoordinates step i (n + 1) x j =
      natCoordinates step i n (step (i + n) x j.divNat) j.modNat := by
  rfl

/-- Pack coordinates in the order used by `natCoordinates`, using the inverse successor maps. -/
def natPack (i n : ℕ) (c : Fin (coordinateSize d i n) → A i) : A (i + n) :=
  (natCoordinates step i n).symm c

/-- At height zero packing returns the single input coefficient. -/
@[simp]
theorem natPack_zero (i : ℕ) (c : Fin (coordinateSize d i 0) → A i) :
    natPack step i 0 c = c ⟨0, by simp only [coordinateSize_zero]; decide⟩ := by
  rfl

/-- Pack each old coordinate block, then apply the inverse of the next successor map. -/
theorem natPack_succ (i n : ℕ) (c : Fin (coordinateSize d i (n + 1)) → A i) :
    natPack step i (n + 1) c =
      (step (i + n)).symm
        (fun b => natPack step i n (fun j => c (finProdFinEquiv (b, j)))) := by
  rfl

/-- Reading back packed coordinates recovers the input coefficients. -/
@[simp]
theorem natCoordinates_natPack (i n : ℕ) (c : Fin (coordinateSize d i n) → A i) :
    natCoordinates step i n (natPack step i n c) = c :=
  (natCoordinates step i n).apply_symm_apply c

/-- Packing the coordinates of an element recovers that element. -/
@[simp]
theorem natPack_natCoordinates (i n : ℕ) (x : A (i + n)) :
    natPack step i n (natCoordinates step i n x) = x :=
  (natCoordinates step i n).symm_apply_apply x

/-- The executable vector whose coordinate at `j` is one and whose other coordinates are zero. -/
def natBasisVector (i n : ℕ) (j : Fin (coordinateSize d i n)) : A (i + n) :=
  natPack step i n (Pi.single j 1)

/-- A basis vector reads back as its unit coordinate vector. -/
@[simp]
theorem natCoordinates_natBasisVector (i n : ℕ) (j : Fin (coordinateSize d i n)) :
    natCoordinates step i n (natBasisVector step i n j) = Pi.single j 1 :=
  natCoordinates_natPack step i n (Pi.single j 1)

end AlgebraTower
