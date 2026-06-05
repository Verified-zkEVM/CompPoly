/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Support.FinHelpers
import Mathlib.Data.Fin.Rev

/-!
# Binary Tower `Fin 2` Linear Independence

Linear-independence lemmas specialized to functions indexed by `Fin 2`.
-/

open Polynomial
open AdjoinRoot
open Module

section LinearIndependentFin2
universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}
variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι → V} {s t : Set ι} {x y : V}

theorem linearIndependent_fin2' {f : Fin 2 → V} :
    LinearIndependent K f ↔ f 0 ≠ 0 ∧ ∀ a : K, a • f 0 ≠ f 1 := by
  rw [← linearIndependent_equiv Fin.revPerm, linearIndependent_fin2]
  rfl

end LinearIndependentFin2
