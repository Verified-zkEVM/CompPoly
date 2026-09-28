/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
meta import CompPoly.Fields.Binary.AdditiveNTT.Impl

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

-- The existing field numeral 7 is 1; retain every word of the affine example's output.
#guard (List.finRange 16).map (fun i => (testNTTBTF₃ i).toNat) ==
  [1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14]

end CompPolyTests.AdditiveNTTCompatibility
