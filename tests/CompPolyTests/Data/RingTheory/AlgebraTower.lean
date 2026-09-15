/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Data.RingTheory.AlgebraTower
import Mathlib.Data.ZMod.Basic

/-!
# Algebra tower identity and adjacent-map regression tests

The projection `(x, y) ↦ (x, x)` on `GF(2) × GF(2)` is an idempotent ring endomorphism.
Using it between every pair of levels gives coherent maps whose self-maps are not identities.
The identity law excludes this family of maps. Identity maps on the same carrier give a valid
tower over a commutative semiring that is not a field.

Using the projection only as the adjacent step gives a valid tower via `AlgebraTower.ofNatStep`.
Symbolic clients check composition and recover any existing natural-number-indexed tower
from its adjacent maps.
-/

namespace CompPolyTests.AlgebraTower

section Generic

variable {ι : Type*} [Preorder ι] {A : ι → Type*}
  [∀ i, CommSemiring (A i)] [AlgebraTower A]

example (i : ι) (h : i ≤ i) :
    AlgebraTower.algebraMap (AT := A) i i h = RingHom.id (A i) := by
  simp

example (i : ι) (h : i ≤ i) (x : A i) :
    AlgebraTower.algebraMap (AT := A) i i h x = x := by
  simp only [AlgebraTower.algebraMap_self_apply]

end Generic

section NatStep

variable {A : ℕ → Type*} [∀ k, CommSemiring (A k)]
  (step : ∀ k, A k →+* A (k + 1))

example (i : ℕ) (h : i ≤ i) :
    (AlgebraTower.ofNatStep step).algebraMap i i h = RingHom.id (A i) :=
  (AlgebraTower.ofNatStep step).algebraMap_self' i

example (i : ℕ) (h : i ≤ i + 1) :
    (AlgebraTower.ofNatStep step).algebraMap i (i + 1) h = step i := by
  simp

example {i j : ℕ} (h h' : i ≤ j) :
    (AlgebraTower.ofNatStep step).algebraMap i j h =
      (AlgebraTower.ofNatStep step).algebraMap i j h' := rfl

example {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : A i) :
    (AlgebraTower.ofNatStep step).algebraMap i k (hij.trans hjk) x =
      (AlgebraTower.ofNatStep step).algebraMap j k hjk
        ((AlgebraTower.ofNatStep step).algebraMap i j hij x) :=
  congrArg (fun f : A i →+* A k => f x)
    ((AlgebraTower.ofNatStep step).coherence' i j k hij hjk)

example {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    letI := AlgebraTower.ofNatStep step
    letI := AlgebraTower.toAlgebra (A := A) hij
    letI := AlgebraTower.toAlgebra (A := A) hjk
    letI := AlgebraTower.toAlgebra (A := A) (hij.trans hjk)
    IsScalarTower (A i) (A j) (A k) :=
  AlgebraTower.toIsScalarTower (AlgebraTower.ofNatStep step) hij hjk

-- Reconstructing an existing tower from its adjacent maps preserves every comparable map.
example [t : AlgebraTower A] {i j : ℕ} (h : i ≤ j) :
    (AlgebraTower.ofNatStep (fun k => t.algebraMap k (k + 1) (Nat.le_succ k))).algebraMap
      i j h = t.algebraMap i j h := by
  induction h with
  | refl =>
    exact ((AlgebraTower.ofNatStep (fun k =>
      t.algebraMap k (k + 1) (Nat.le_succ k))).algebraMap_self' i).trans
        (t.algebraMap_self' i).symm
  | @step j h ih =>
    rw [AlgebraTower.ofNatStep_algebraMap_succ_right _ h, ih,
      t.coherence' i j (j + 1) h (Nat.le_succ j)]

end NatStep

private abbrev R := ZMod 2 × ZMod 2

/-- The ring endomorphism `(x, y) ↦ (x, x)`. -/
private def diagonal : R →+* R where
  toFun x := (x.1, x.1)
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

-- Constant projection maps satisfy commutativity and composition.
example (r x : R) : diagonal r * x = x * diagonal r := mul_comm _ _

example : diagonal = diagonal.comp diagonal := by
  ext x <;> rfl

private theorem diagonal_ne_id : diagonal ≠ RingHom.id R := by
  intro h
  have h01 := congrArg (fun f : R →+* R => (f (0, 1)).2) h
  change (0 : ZMod 2) = 1 at h01
  exact zero_ne_one h01

-- A tower cannot use this projection for every map.
example : ¬ ∃ t : AlgebraTower (fun _ : ℕ => R),
    ∀ i j h, t.algebraMap i j h = diagonal := by
  rintro ⟨t, ht⟩
  exact diagonal_ne_id ((ht 0 0 le_rfl).symm.trans (t.algebraMap_self' 0))

/-- The constant tower on `GF(2) × GF(2)` with identity maps. -/
private abbrev constantTower : AlgebraTower (fun _ : ℕ => R) where
  algebraMap _ _ _ := RingHom.id R
  algebraMap_self' _ := rfl
  commutes' _ _ _ r x := mul_comm r x
  coherence' _ _ _ _ _ := rfl

example (x : R) : constantTower.algebraMap 0 2 (by decide) x = x := rfl

/-- A valid tower with noninjective adjacent maps on the same non-field carrier. -/
private abbrev projectionTower : AlgebraTower (fun _ : ℕ => R) :=
  AlgebraTower.ofNatStep (fun _ => diagonal)

example (k : ℕ) : projectionTower.algebraMap k k le_rfl (0, 1) = (0, 1) := by
  rw [projectionTower.algebraMap_self']
  rfl

example : projectionTower.algebraMap 0 2 (by decide) (0, 1) = (0, 0) := by
  rw [AlgebraTower.ofNatStep_algebraMap_succ_right _ (show 0 ≤ 1 by decide),
    AlgebraTower.ofNatStep_algebraMap_succ]
  rfl

example (k : ℕ) :
    ¬ Function.Injective (projectionTower.algebraMap k (k + 1) (Nat.le_succ k)) := by
  rw [AlgebraTower.ofNatStep_algebraMap_succ]
  intro h
  have he := h (show diagonal (0, 1) = diagonal (0, 0) from rfl)
  exact one_ne_zero (congrArg Prod.snd he)

end CompPolyTests.AlgebraTower
