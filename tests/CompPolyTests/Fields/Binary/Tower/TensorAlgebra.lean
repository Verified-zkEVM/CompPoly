/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.Fields.Binary.Tower.TensorAlgebra

/-!
# Tensor action compatibility import regression

The binary-tower import path exposes the generic basis helper without changing the
default scalar action on equal tensor factors.
-/

open scoped TensorProduct

namespace CompPolyTests.BinaryTowerTensorAlgebra

example {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L] :
    algebraMap L (L ⊗[K] L) = Algebra.TensorProduct.includeLeftRingHom := rfl

example {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L] :
    (inferInstance : Module L (L ⊗[K] L)) = TensorProduct.leftModule := rfl

example {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L] :
    (inferInstance : DistribMulAction L (L ⊗[K] L)) = TensorProduct.leftDistribMulAction := rfl

example {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L] :
    (inferInstance : SMul L (L ⊗[K] L)) = TensorProduct.leftHasSMul := rfl

end CompPolyTests.BinaryTowerTensorAlgebra
