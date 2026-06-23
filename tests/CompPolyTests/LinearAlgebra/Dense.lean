/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense
import Mathlib.Algebra.Field.ZMod

/-!
# Dense Linear-Algebra Tests

Focused regression coverage for the dense homogeneous-kernel witness used by
Guruswami-Sudan interpolation.
-/

namespace CompPolyTests

open CompPoly

namespace LinearAlgebra.Dense

abbrev F3 := ZMod 3

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

private def dependentSystem : DenseMatrix F3 :=
  DenseMatrix.ofFn 1 2 fun _ col ↦
    if col = 0 then 1 else 2

#guard (DenseMatrix.homogeneousWitness dependentSystem).isSome

end LinearAlgebra.Dense

end CompPolyTests
