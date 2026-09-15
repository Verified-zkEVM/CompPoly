/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Data.RingTheory.AlgebraTower
import Mathlib.Data.ZMod.Basic

/-!
# Algebra tower identity regression tests

The projection `(x, y) ↦ (x, x)` on `GF(2) × GF(2)` is an idempotent ring endomorphism.
Using it between every pair of levels gives coherent maps whose self-maps are not identities.
The identity law excludes this family of maps. Identity maps on the same carrier give a valid
tower over a commutative semiring that is not a field.
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

end CompPolyTests.AlgebraTower
