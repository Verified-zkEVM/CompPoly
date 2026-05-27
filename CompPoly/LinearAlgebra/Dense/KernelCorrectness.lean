/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.Dense.Kernel

/-!
# Dense Homogeneous-Kernel Correctness

Correctness contracts for executable dense homogeneous-kernel witnesses.
-/

namespace CompPoly

namespace DenseMatrix

/-- Any homogeneous witness returned by the executable kernel search has matrix-column width. -/
theorem homogeneousWitness_width [Field F] [BEq F]
    {M : DenseMatrix F} {v : Array F} (h : homogeneousWitness M = some v) :
    VectorWidth M v := by
  sorry

/-- Any homogeneous witness returned by the executable kernel search is nonzero. -/
theorem homogeneousWitness_nonzero [Field F] [BEq F]
    {M : DenseMatrix F} {v : Array F} (h : homogeneousWitness M = some v) :
    NonzeroVector v := by
  sorry

/-- Soundness of the homogeneous witness returned by Gaussian elimination. -/
theorem homogeneousWitness_sound [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) {v : Array F}
    (h : homogeneousWitness M = some v) :
    VectorWidth M v /\ IsHomogeneousSolution M v /\ NonzeroVector v := by
  sorry

/-- If no homogeneous witness is returned, the homogeneous kernel is trivial. -/
theorem homogeneousWitness_none_complete [Field F] [BEq F] [LawfulBEq F]
    {M : DenseMatrix F} (hM : WellFormed M) (h : homogeneousWitness M = none) :
    forall v, VectorWidth M v -> IsHomogeneousSolution M v -> Not (NonzeroVector v) := by
  sorry

end DenseMatrix

end CompPoly

