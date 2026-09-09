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

end Generic

end CompPolyTests.AlgebraTower.Coordinates
