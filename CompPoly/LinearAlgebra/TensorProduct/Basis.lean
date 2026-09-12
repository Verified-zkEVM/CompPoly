/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bases for the right scalar action on tensor products

`Module.Basis.baseChangeRight` lifts a basis of `Left` over `K` to a basis of
`Left ⊗[K] Right` over `Right`, with scalars acting on the right tensor factor.
The action is explicit in each declaration; importing this module preserves Mathlib's
default action on the left factor, including when `Left = Right`.

For equal factors, select the right `Algebra`, `Module`, `DistribMulAction` and `SMul`
locally when combining this basis with scalar notation and module laws. Tensor products
provide independent default instances at each of these levels.
-/

@[expose] public section

open scoped TensorProduct

namespace Module.Basis

variable {K Left Right ι : Type*} [CommSemiring K] [Semiring Left] [CommSemiring Right]
  [Algebra K Left] [Algebra K Right]

/-- Lift a `K`-basis of `Left` to a `Right`-basis of `Left ⊗[K] Right`, using the
right-factor scalar action. This is the right-sided counterpart to `Basis.baseChange`. -/
noncomputable def baseChangeRight (b : Basis ι K Left) :
    letI rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
    letI := rightAlgebra.toModule
    Basis ι Right (Left ⊗[K] Right) := by
  letI rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
  letI := rightAlgebra.toModule
  exact (b.baseChange Right).map (Algebra.TensorProduct.commRight K Right Left).toLinearEquiv

/-- Coordinates of a pure tensor in the basis for the right-factor scalar action. -/
@[simp]
lemma baseChangeRight_repr_tmul (b : Basis ι K Left) (x : Left) (y : Right) (i : ι) :
    letI rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
    letI := rightAlgebra.toModule
    (b.baseChangeRight (Right := Right)).repr (x ⊗ₜ[K] y) i = b.repr x i • y := by
  let rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
  let := rightAlgebra.toModule
  rw [baseChangeRight, Basis.map_repr]
  change (b.baseChange Right).repr (y ⊗ₜ[K] x) i = b.repr x i • y
  exact baseChange_repr_tmul Right b y x i

/-- The right-action basis vectors are the original basis vectors tensored with one. -/
@[simp]
lemma baseChangeRight_apply (b : Basis ι K Left) (i : ι) :
    letI rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
    letI := rightAlgebra.toModule
    b.baseChangeRight (Right := Right) i = b i ⊗ₜ[K] 1 := by
  let rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
  let := rightAlgebra.toModule
  simp only [baseChangeRight, Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    baseChange_apply, Algebra.TensorProduct.commRight_tmul]

end Module.Basis
