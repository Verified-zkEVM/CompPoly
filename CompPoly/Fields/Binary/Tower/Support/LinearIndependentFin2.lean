/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Support.FinHelpers

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
  rw [linearIndependent_fin_succ', linearIndependent_unique_iff, Set.range_unique,
    Submodule.mem_span_singleton,
    not_exists]
  rw [show Fin.init f default = f 0 by rfl]
  rfl

end LinearIndependentFin2
