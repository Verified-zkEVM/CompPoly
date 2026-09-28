/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Data.RingTheory.AlgebraTower.Basis
meta import CompPoly.Data.RingTheory.AlgebraTower.Coordinates

/-!
# Finite-product tower coordinate tests

Successive function rings give towers with arbitrary finite step ranks, using constant
functions as the tower maps. A rectangular two-step example distinguishes the two index
orders. Rank zero, rank one, and height zero exercise the boundary cases without field or
nontriviality assumptions. Symbolic clients check the selected scalar action and the actual
basis representation.

Endpoint clients accept unrelated `i`, `j` and `h : i ≤ j` without client-side casts. Constant
coordinate counts zero, one and two exercise the normalized index type. A zero intermediate
count gives an explicitly noninjective tower map from a nontrivial source.
-/

namespace CompPolyTests.AlgebraTower.Coordinates

open _root_.AlgebraTower

private def FunctionTower (d : ℕ → ℕ) : ℕ → Type
  | 0 => ℕ
  | k + 1 => Fin (d k) → FunctionTower d k

private instance functionTowerCommSemiring (d : ℕ → ℕ) :
    (k : ℕ) → CommSemiring (FunctionTower d k)
  | 0 => inferInstanceAs (CommSemiring ℕ)
  | k + 1 =>
      letI := functionTowerCommSemiring d k
      inferInstanceAs (CommSemiring (Fin (d k) → FunctionTower d k))

private def functionStep (d : ℕ → ℕ) (k : ℕ) :
    FunctionTower d k →+* FunctionTower d (k + 1) :=
  Pi.constRingHom (Fin (d k)) (FunctionTower d k)

private instance functionTower (d : ℕ → ℕ) : AlgebraTower (FunctionTower d) :=
  ofNatStep (functionStep d)

private def functionCoordinates (d : ℕ → ℕ) (k : ℕ) :
    letI := (functionTower d).toAlgebra (Nat.le_succ k)
    FunctionTower d (k + 1) ≃ₗ[FunctionTower d k] (Fin (d k) → FunctionTower d k) := by
  letI := (functionTower d).toAlgebra (Nat.le_succ k)
  exact {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      funext b
      change (((ofNatStep (functionStep d)).algebraMap k (k + 1) (Nat.le_succ k) a) * x) b =
        a * x b
      rw [ofNatStep_algebraMap_succ]
      rfl }

private abbrev ranks : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | _ => 1

private def rectangular : FunctionTower ranks 2 := ![![10, 11], ![20, 21], ![30, 31]]

-- Compiled execution uses the coordinate maps and packing, without the noncomputable Basis.
#guard List.ofFn (show Fin 6 → ℕ from
    natCoordinates (functionCoordinates ranks) 0 2 rectangular) ==
  [10, 11, 20, 21, 30, 31]
#guard (show ℕ from natPack (functionCoordinates ranks) 0 2
    ![10, 11, 20, 21, 30, 31] 2 0) == 30
#guard List.ofFn (show Fin 6 → ℕ from natCoordinates (functionCoordinates ranks) 0 2
    (natBasisVector (functionCoordinates ranks) 0 2 4)) == [0, 0, 0, 0, 1, 0]

private theorem rectangular_pack :
    natPack (functionCoordinates ranks) 0 2 ![10, 11, 20, 21, 30, 31] = rectangular := by
  simp only [natPack_succ, natPack_zero]
  funext b j
  fin_cases b <;> fin_cases j <;> rfl

-- The preceding-level coordinate varies fastest, even when the next rank differs.
example : natCoordinates (functionCoordinates ranks) 0 2 rectangular =
    ![10, 11, 20, 21, 30, 31] := by
  rw [← rectangular_pack, natCoordinates_natPack]

-- The transposed order is still a bijection, but gives a different second coefficient.
example : natCoordinates (functionCoordinates ranks) 0 2 rectangular 1 ≠
    rectangular ((finProdFinEquiv.symm (1 : Fin (2 * 3))).2)
      ((finProdFinEquiv.symm (1 : Fin (2 * 3))).1) := by
  conv_lhs => rw [← rectangular_pack]
  change natCoordinates (functionCoordinates ranks) 0 2
    (natPack (functionCoordinates ranks) 0 2 ![10, 11, 20, 21, 30, 31]) 1 ≠ rectangular 1 0
  rw [congrFun (natCoordinates_natPack (functionCoordinates ranks) 0 2
    ![10, 11, 20, 21, 30, 31]) 1]
  change (11 : ℕ) ≠ 20
  decide

example (x : ℕ) : natCoordinates (functionCoordinates ranks) 0 0 x 0 = x :=
  natCoordinates_zero _ _ _ _

-- A legitimate first basis vector need not be one in the target ring.
example : natBasisVector (functionCoordinates ranks) 0 1 0 ≠
    (1 : FunctionTower ranks 1) := by
  intro h
  have hone : natCoordinates (functionCoordinates ranks) 0 1
      (1 : FunctionTower ranks 1) 1 = 1 := by
    rw [natCoordinates_succ, natCoordinates_zero]
    rfl
  have hc := congrArg (fun x : FunctionTower ranks 1 =>
    natCoordinates (functionCoordinates ranks) 0 1 x 1) h
  rw [congrFun (natCoordinates_natBasisVector (functionCoordinates ranks) 0 1 0) 1,
    hone] at hc
  exact Nat.zero_ne_one hc

example (x : FunctionTower (fun _ => 1) 3) :
    natPack (functionCoordinates (fun _ => 1)) 1 2
      (natCoordinates (functionCoordinates (fun _ => 1)) 1 2 x) = x :=
  natPack_natCoordinates _ _ _ _

-- A zero successor rank is a valid free presentation of a zero function ring.
example (x : FunctionTower (fun _ => 0) 2) :
    natPack (functionCoordinates (fun _ => 0)) 0 2
      (natCoordinates (functionCoordinates (fun _ => 0)) 0 2 x) = x :=
  natPack_natCoordinates _ _ _ _

example (r i n : ℕ) : coordinateSize (fun _ => r) i n = r ^ n :=
  coordinateSize_const r i n

-- Endpoint transport preserves the independently specified rectangular order.
#guard List.ofFn (show Fin 6 → ℕ from
    natCoordinatesOfLE (functionCoordinates ranks) (show 0 ≤ 2 by decide)
    rectangular) == [10, 11, 20, 21, 30, 31]
#guard (show ℕ from natPackOfLE (functionCoordinates ranks) (show 0 ≤ 2 by decide)
    ![10, 11, 20, 21, 30, 31] 2 0) == 30

example (x : FunctionTower ranks 1) (idx : Fin 2) :
    natCoordinatesOfLE (functionCoordinates ranks) (show 0 ≤ 1 by decide) x idx = x idx := by
  rw [natCoordinatesOfLE_apply, natCoordinates_succ, natCoordinates_zero]
  change x ⟨idx.val / 1, _⟩ = x idx
  congr 1
  exact Fin.ext (Nat.div_one idx.val)

example : natBasisVectorOfLE (functionCoordinates ranks) (show 0 ≤ 2 by decide) 4 =
    natBasisVector (functionCoordinates ranks) 0 2 4 :=
  natBasisVectorOfLE_eq_natBasisVector _ _ _

private def shiftedBinary : FunctionTower (fun _ => 2) 3 :=
  ![![![10, 11], ![20, 21]], ![![30, 31], ![40, 41]]]

-- Four coefficients over level one retain both entries of each lower-level element.
#guard List.ofFn (fun idx => List.ofFn (show Fin 2 → ℕ from
    natCoordinatesConstOfLE (functionCoordinates (fun _ => 2)) (show 1 ≤ 3 by decide)
      shiftedBinary idx)) == [[10, 11], [20, 21], [30, 31], [40, 41]]
#guard (show ℕ from (natCoordinatesConstOfLE (functionCoordinates (fun _ => 2))
    (show 1 ≤ 3 by decide)).symm ![![10, 11], ![20, 21], ![30, 31], ![40, 41]]
      1 0 1) == 31

private abbrev zeroMiddle : ℕ → ℕ
  | 0 => 2
  | 1 => 0
  | _ => 1

example : (0 : FunctionTower zeroMiddle 1) ≠ 1 := by
  intro h
  exact Nat.zero_ne_one (congrFun h 0)

-- The distinct source elements above have the same image in the zero function ring.
example : (functionTower zeroMiddle).algebraMap 1 2 (by decide) 0 =
    (functionTower zeroMiddle).algebraMap 1 2 (by decide) 1 := by
  funext idx
  exact Fin.elim0 idx

example (x : FunctionTower zeroMiddle 3) :
    natPackOfLE (functionCoordinates zeroMiddle) (show 1 ≤ 3 by decide)
      (natCoordinatesOfLE (functionCoordinates zeroMiddle) (show 1 ≤ 3 by decide) x) = x :=
  natPackOfLE_natCoordinatesOfLE _ _ _

-- Zero successors give no coordinates at positive height, but one at height zero.
example (x : FunctionTower (fun _ => 0) 2) :
    (natCoordinatesConstOfLE (functionCoordinates (fun _ => 0)) (show 0 ≤ 2 by decide)).symm
      (fun idx : Fin 0 => Fin.elim0 idx) = x := by
  apply (natCoordinatesConstOfLE (functionCoordinates (fun _ => 0))
    (show 0 ≤ 2 by decide)).injective
  rw [LinearEquiv.apply_symm_apply]
  funext idx
  exact Fin.elim0 idx

#guard List.ofFn (show Fin 1 → ℕ from
    natCoordinatesConstOfLE (functionCoordinates (fun _ => 0))
    (Nat.le_refl 0) 37) == [37]

example {i j : ℕ} (h : i ≤ j) (x : FunctionTower (fun _ => 1) j) :
    (natCoordinatesConstOfLE (functionCoordinates (fun _ => 1)) h).symm
      (natCoordinatesConstOfLE (functionCoordinates (fun _ => 1)) h x) = x :=
  LinearEquiv.symm_apply_apply _ _

section Generic

variable {A : ℕ → Type*} [∀ k, CommSemiring (A k)] [t : AlgebraTower A]
  {d : ℕ → ℕ}
  (step : ∀ k, letI := t.toAlgebra (Nat.le_succ k)
    A (k + 1) ≃ₗ[A k] (Fin (d k) → A k))

example (i n : ℕ) (a : A i) (x : A (i + n)) :
    natCoordinates step i n (t.algebraMap i (i + n) (Nat.le_add_right i n) a * x) =
      a • natCoordinates step i n x := by
  let := t.toAlgebra (Nat.le_add_right i n)
  exact (natCoordinates step i n).map_smul a x

example (i n : ℕ) (c : Fin (coordinateSize d i n) → A i) :
    letI := t.toAlgebra (Nat.le_add_right i n)
    (natBasis step i n).repr (natPack step i n c) = c := by
  let := t.toAlgebra (Nat.le_add_right i n)
  funext j
  rw [natBasis_repr, congrFun (natCoordinates_natPack step i n c) j]

example (i n : ℕ) (c : Fin (coordinateSize d i n) → A i) :
    letI := t.toAlgebra (Nat.le_add_right i n)
    ∑ j, c j • natBasis step i n j = natPack step i n c := by
  let := t.toAlgebra (Nat.le_add_right i n)
  have hc : (natBasis step i n).repr (natPack step i n c) = c := by
    funext j
    rw [natBasis_repr, congrFun (natCoordinates_natPack step i n c) j]
  simpa only [hc] using (natBasis step i n).sum_repr (natPack step i n c)

-- These endpoint types contain neither a client-side carrier cast nor a rewritten endpoint.
example {i j : ℕ} (h : i ≤ j) (x : A j) :
    natPackOfLE step h (natCoordinatesOfLE step h x) = x :=
  natPackOfLE_natCoordinatesOfLE _ _ _

example {i j : ℕ} (h : i ≤ j) (a : A i) (x : A j) :
    natCoordinatesOfLE step h (t.algebraMap i j h a * x) =
      a • natCoordinatesOfLE step h x := by
  let := t.toAlgebra h
  exact (natCoordinatesOfLE step h).map_smul a x

example {i j : ℕ} (h h' : i ≤ j) : natCoordinatesOfLE step h = natCoordinatesOfLE step h' :=
  rfl

example {i j : ℕ} (h h' : i ≤ j) (c : Fin (coordinateSize d i (j - i)) → A i) :
    natPackOfLE step h c = natPackOfLE step h' c := rfl

example {i j : ℕ} (h h' : i ≤ j) :
    natBasisVectorOfLE step h = natBasisVectorOfLE step h' := rfl

example {i j : ℕ} (h h' : i ≤ j) : natBasisOfLE step h = natBasisOfLE step h' := rfl

example {i j : ℕ} (h : i ≤ j) (c : Fin (coordinateSize d i (j - i)) → A i) :
    letI := t.toAlgebra h
    (natBasisOfLE step h).repr (natPackOfLE step h c) = c := by
  let := t.toAlgebra h
  funext idx
  rw [natBasisOfLE_repr, congrFun (natCoordinatesOfLE_natPackOfLE step h c) idx]

example {i j : ℕ} (h : i ≤ j) (c : Fin (coordinateSize d i (j - i)) → A i) :
    letI := t.toAlgebra h
    ∑ idx, c idx • natBasisOfLE step h idx = natPackOfLE step h c := by
  let := t.toAlgebra h
  have hc : (natBasisOfLE step h).repr (natPackOfLE step h c) = c := by
    funext idx
    rw [natBasisOfLE_repr, congrFun (natCoordinatesOfLE_natPackOfLE step h c) idx]
  simpa only [hc] using (natBasisOfLE step h).sum_repr (natPackOfLE step h c)

example {i j : ℕ} (h : i ≤ j) (idx : Fin (coordinateSize d i (j - i))) :
    natBasisOfLE step h idx =
      cast (congrArg A (Nat.add_sub_of_le h)) (natBasis step i (j - i) idx) :=
  natBasisOfLE_apply _ _ _

variable {r : ℕ}
  (constantStep : ∀ k, letI := t.toAlgebra (Nat.le_succ k)
    A (k + 1) ≃ₗ[A k] (Fin r → A k))

example {i j : ℕ} (h h' : i ≤ j) :
    natCoordinatesConstOfLE constantStep h = natCoordinatesConstOfLE constantStep h' := rfl

example {i j : ℕ} (h : i ≤ j) (a : A i) (x : A j) :
    natCoordinatesConstOfLE constantStep h (t.algebraMap i j h a * x) =
      a • natCoordinatesConstOfLE constantStep h x := by
  let := t.toAlgebra h
  exact (natCoordinatesConstOfLE constantStep h).map_smul a x

end Generic

end CompPolyTests.AlgebraTower.Coordinates
