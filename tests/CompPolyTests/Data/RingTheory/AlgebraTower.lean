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

The old commutativity and composition laws admit an idempotent nonidentity endomorphism
on a constant family. The self-map law excludes it while retaining commutative semirings
and arbitrary preorders as the only ambient assumptions.
-/

namespace CompPolyTests.AlgebraTower

section Generic

variable {ι : Type*} [Preorder ι] {A : ι → Type*}
  [∀ i, CommSemiring (A i)] [AlgebraTower A]

example (i : ι) (h : i ≤ i) :
    AlgebraTower.algebraMap (AT := A) i i h = RingHom.id (A i) := by
  simp only [AlgebraTower.algebraMap_self]

example (i : ι) (h : i ≤ i) (x : A i) :
    AlgebraTower.algebraMap (AT := A) i i h x = x := by
  simp only [AlgebraTower.algebraMap_self_apply]

example (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : A i) :
    AlgebraTower.algebraMap (AT := A) i k (hij.trans hjk) x =
      AlgebraTower.algebraMap (AT := A) j k hjk
        (AlgebraTower.algebraMap (AT := A) i j hij x) := by
  rw [AlgebraTower.coherence', RingHom.comp_apply]

end Generic

private abbrev R := ZMod 2 × ZMod 2

private def diagonal : R →+* R where
  toFun x := (x.1, x.1)
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def oldMap (_i _j : ℕ) (_h : _i ≤ _j) : R →+* R := diagonal

-- These are precisely the two laws that previously sufficed for the constant family.
example (i j : ℕ) (h : i ≤ j) (r x : R) : oldMap i j h r * x = x * oldMap i j h r :=
  mul_comm _ _

example (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    oldMap i k (hij.trans hjk) = (oldMap j k hjk).comp (oldMap i j hij) := by
  ext x <;> rfl

private theorem diagonal_ne_id : diagonal ≠ RingHom.id R := by
  intro h
  have bad := congrArg (fun f : R →+* R => (f (0, 1)).2) h
  change (0 : ZMod 2) = 1 at bad
  exact zero_ne_one bad

-- No strengthened tower can retain all the maps of that old-contract counterexample.
example : ¬ ∃ t : AlgebraTower (fun _ : ℕ => R),
    ∀ i j h, t.algebraMap i j h = oldMap i j h := by
  rintro ⟨t, ht⟩
  exact diagonal_ne_id ((ht 0 0 le_rfl).symm.trans (t.identity' 0))

-- A concrete valid control on the same non-field carrier rules out a vacuous contract.
private abbrev constantTower : AlgebraTower (fun _ : ℕ => R) where
  algebraMap _ _ _ := RingHom.id R
  identity' _ := rfl
  commutes' _ _ _ r x := mul_comm r x
  coherence' _ _ _ _ _ := rfl

example (x : R) : constantTower.algebraMap 0 2 (by decide) x = x := rfl

end CompPolyTests.AlgebraTower
