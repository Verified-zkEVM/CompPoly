/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT

/-!
# Additive NTT compatibility entry point

The umbrella import retains concrete tower definitions and instances alongside the generic
algorithms and correctness theorems.
-/

namespace CompPolyTests.AdditiveNTTCompatibility

open AdditiveNTT ConcreteBinaryTower

example : BTF₃ = ConcreteBTField 3 := rfl

example : (inferInstance : Field BTF₃) = instFieldConcrete := rfl

example (k : ℕ) : NeZero (2 ^ k) := inferInstance

example (k : ℕ) :
    letI := ConcreteBTFieldAlgebra (show 0 ≤ k by omega)
    LinearIndependent (ConcreteBTField 0) (computableBasisExplicit k) :=
  hβ_lin_indep_concrete k

example : Fin 16 → BTF₃ := testNTTBTF₃

end CompPolyTests.AdditiveNTTCompatibility
