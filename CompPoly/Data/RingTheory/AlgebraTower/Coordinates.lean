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

For arbitrary endpoints `h : i ≤ j`, `AlgebraTower.natCoordinatesOfLE` and its packing
and vector companions accept elements of `A j` directly. `AlgebraTower.natCoordinatesConstOfLE`
also presents constant successor coordinate count `r` as `Fin (r ^ (j - i))`.

The construction uses `LinearEquiv.restrictScalars`, `LinearEquiv.piCongrRight`,
`LinearEquiv.curry`, and `finProdFinEquiv`. Endpoint and coordinate-count identifications use
`LinearEquiv.cast`, `LinearEquiv.funCongrLeft`, and `finCongr`.
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

private theorem natCoordinates_cast_apply (i : ℕ) {n m : ℕ} (h : n = m)
    (x : A (i + n)) (idx : Fin (coordinateSize d i m)) :
    natCoordinates step i m (cast (congrArg (fun k => A (i + k)) h) x) idx =
      natCoordinates step i n x (Fin.cast (congrArg (coordinateSize d i) h.symm) idx) := by
  cases h
  rfl

/-- Coordinates of `A j` over `A i` for comparable endpoints, with the given tower action.
The coordinate count and order are those of the `j - i` successor steps starting at `i`. -/
def natCoordinatesOfLE {i j : ℕ} (h : i ≤ j) :
    letI := t.toAlgebra h
    A j ≃ₗ[A i] (Fin (coordinateSize d i (j - i)) → A i) := by
  letI := t.toAlgebra h
  letI : ∀ k : {k : ℕ // i ≤ k}, Module (A i) (A k.val) :=
    fun k => (t.toAlgebra k.property).toModule
  let e : (⟨j, h⟩ : {k : ℕ // i ≤ k}) =
      ⟨i + (j - i), Nat.le_add_right i (j - i)⟩ :=
    Subtype.ext (Nat.add_sub_of_le h).symm
  exact (LinearEquiv.cast (R := A i) (M := fun k : {k : ℕ // i ≤ k} => A k.val) e).trans
    (natCoordinates step i (j - i))

/-- Endpoint coordinates are height coordinates after identifying `j` with `i + (j - i)`.
The coordinate index is unchanged. -/
theorem natCoordinatesOfLE_apply {i j : ℕ} (h : i ≤ j) (x : A j)
    (idx : Fin (coordinateSize d i (j - i))) :
    natCoordinatesOfLE step h x idx =
      natCoordinates step i (j - i) (cast (congrArg A (Nat.add_sub_of_le h).symm) x) idx := by
  rfl

/-- With equal endpoints the single coordinate is the original element. -/
@[simp]
theorem natCoordinatesOfLE_self (i : ℕ) (x : A i)
    (idx : Fin (coordinateSize d i (i - i))) :
    natCoordinatesOfLE step (Nat.le_refl i) x idx = x := by
  rw [natCoordinatesOfLE_apply,
    natCoordinates_cast_apply step i (Nat.sub_self i).symm, natCoordinates_zero]

/-- Pack coordinates into `A j`, inverting the coordinate map over the given tower action. -/
def natPackOfLE {i j : ℕ} (h : i ≤ j) (c : Fin (coordinateSize d i (j - i)) → A i) : A j :=
  (natCoordinatesOfLE step h).symm c

/-- Endpoint packing is height packing followed by the identification `i + (j - i) = j`. -/
theorem natPackOfLE_eq_natPack {i j : ℕ} (h : i ≤ j)
    (c : Fin (coordinateSize d i (j - i)) → A i) :
    natPackOfLE step h c = cast (congrArg A (Nat.add_sub_of_le h)) (natPack step i (j - i) c) := by
  rfl

/-- Packing at equal endpoints returns the single coefficient. -/
@[simp]
theorem natPackOfLE_self (i : ℕ) (c : Fin (coordinateSize d i (i - i)) → A i) :
    natPackOfLE step (Nat.le_refl i) c =
      c ⟨0, by simp only [Nat.sub_self, coordinateSize_zero]; decide⟩ := by
  exact (natCoordinatesOfLE_self step i (natPackOfLE step (Nat.le_refl i) c) _).symm.trans
    (congrFun ((natCoordinatesOfLE step (Nat.le_refl i)).apply_symm_apply c) _)

/-- Reading packed endpoint coordinates recovers the input coefficients. -/
@[simp]
theorem natCoordinatesOfLE_natPackOfLE {i j : ℕ} (h : i ≤ j)
    (c : Fin (coordinateSize d i (j - i)) → A i) :
    natCoordinatesOfLE step h (natPackOfLE step h c) = c :=
  (natCoordinatesOfLE step h).apply_symm_apply c

/-- Packing the endpoint coordinates of an element recovers that element. -/
@[simp]
theorem natPackOfLE_natCoordinatesOfLE {i j : ℕ} (h : i ≤ j) (x : A j) :
    natPackOfLE step h (natCoordinatesOfLE step h x) = x :=
  (natCoordinatesOfLE step h).symm_apply_apply x

/-- The executable endpoint vector with coordinate one at `idx` and zero elsewhere. -/
def natBasisVectorOfLE {i j : ℕ} (h : i ≤ j) (idx : Fin (coordinateSize d i (j - i))) : A j :=
  natPackOfLE step h (Pi.single idx 1)

/-- Endpoint vectors agree with height vectors under the canonical endpoint identification. -/
theorem natBasisVectorOfLE_eq_natBasisVector {i j : ℕ} (h : i ≤ j)
    (idx : Fin (coordinateSize d i (j - i))) :
    natBasisVectorOfLE step h idx =
      cast (congrArg A (Nat.add_sub_of_le h)) (natBasisVector step i (j - i) idx) :=
  natPackOfLE_eq_natPack step h (Pi.single idx 1)

/-- An endpoint vector reads back as its unit coordinate vector. -/
@[simp]
theorem natCoordinatesOfLE_natBasisVectorOfLE {i j : ℕ} (h : i ≤ j)
    (idx : Fin (coordinateSize d i (j - i))) :
    natCoordinatesOfLE step h (natBasisVectorOfLE step h idx) = Pi.single idx 1 :=
  natCoordinatesOfLE_natPackOfLE step h (Pi.single idx 1)

/-- At equal endpoints the unique executable basis vector is one. -/
@[simp]
theorem natBasisVectorOfLE_self (i : ℕ) (idx : Fin (coordinateSize d i (i - i))) :
    natBasisVectorOfLE step (Nat.le_refl i) idx = 1 := by
  rw [natBasisVectorOfLE, natPackOfLE_self]
  have hidx : idx = ⟨0, by simp only [Nat.sub_self, coordinateSize_zero]; decide⟩ := by
    apply Fin.ext
    have := idx.isLt
    simp only [Nat.sub_self, coordinateSize_zero] at this
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ this)
  simp only [hidx, Pi.single_eq_same]

variable {r : ℕ}
  (constantStep : ∀ k, letI := t.toAlgebra (Nat.le_succ k)
    A (k + 1) ≃ₗ[A k] (Fin r → A k))

/-- Endpoint coordinates with constant successor coordinate count `r`, indexed by `Fin (r^(j-i))`.
Only the coordinate count is identified with a power; each index retains its numeric value. -/
def natCoordinatesConstOfLE {i j : ℕ} (h : i ≤ j) :
    letI := t.toAlgebra h
    A j ≃ₗ[A i] (Fin (r ^ (j - i)) → A i) := by
  letI := t.toAlgebra h
  exact (natCoordinatesOfLE (d := fun _ => r) constantStep h).trans
    (LinearEquiv.funCongrLeft (A i) (A i)
      (finCongr (coordinateSize_const r i (j - i))).symm)

/-- Constant-count coordinates read the same numeric index in the endpoint coordinate map. -/
theorem natCoordinatesConstOfLE_apply {i j : ℕ} (h : i ≤ j) (x : A j)
    (idx : Fin (r ^ (j - i))) :
    natCoordinatesConstOfLE constantStep h x idx =
      natCoordinatesOfLE constantStep h x
        (Fin.cast (coordinateSize_const r i (j - i)).symm idx) := by
  rfl

/-- Constant-count coordinates at equal endpoints consist of the original element. -/
@[simp]
theorem natCoordinatesConstOfLE_self (i : ℕ) (x : A i) (idx : Fin (r ^ (i - i))) :
    natCoordinatesConstOfLE constantStep (Nat.le_refl i) x idx = x := by
  rw [natCoordinatesConstOfLE_apply, natCoordinatesOfLE_self]

end AlgebraTower
