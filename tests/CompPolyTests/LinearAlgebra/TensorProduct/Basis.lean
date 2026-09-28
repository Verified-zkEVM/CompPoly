/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

import CompPoly.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Tensor basis action regression tests

Check that importing the right-action basis helper preserves the default left action,
that both coordinate systems reconstruct arbitrary tensors and recover arbitrary coordinates,
and that the actions and coordinates differ on the proper field extension `ℂ/ℝ`.
-/

open Module
open scoped TensorProduct BigOperators

namespace CompPolyTests.TensorProductBasis

section Actions

variable {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]

-- The equal-factor case is where a global rightAlgebra instance would change the default.
example : algebraMap L (L ⊗[K] L) = Algebra.TensorProduct.includeLeftRingHom := rfl

example : (inferInstance : Module L (L ⊗[K] L)) = TensorProduct.leftModule := rfl

example : (inferInstance : DistribMulAction L (L ⊗[K] L)) =
    TensorProduct.leftDistribMulAction := rfl

example : (inferInstance : SMul L (L ⊗[K] L)) = TensorProduct.leftHasSMul := rfl

example :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := L)
    algebraMap L (L ⊗[K] L) = Algebra.TensorProduct.includeRight.toRingHom := rfl

-- When the extension is the base itself, the two inclusions coincide.
example (x : K) : x ⊗ₜ[K] (1 : K) = (1 : K) ⊗ₜ[K] x := by
  simpa only [smul_eq_mul, mul_one] using (TensorProduct.smul_tmul x (1 : K) (1 : K))

end Actions

section Coordinates

variable {K Left Right ι : Type*} [CommSemiring K] [Semiring Left]
  [CommSemiring Right] [Algebra K Left] [Algebra K Right] [Fintype ι]

example (b : Basis ι K Right) (z : Left ⊗[K] Right) :
    ∑ i, (b.baseChange Left).repr z i • ((1 : Left) ⊗ₜ[K] b i) = z := by
  simpa only [Basis.baseChange_apply] using (b.baseChange Left).sum_repr z

example (b : Basis ι K Right) (c : ι → Left) (i : ι) :
    (b.baseChange Left).repr (∑ j, c j • ((1 : Left) ⊗ₜ[K] b j)) i = c i := by
  simpa only [Basis.baseChange_apply] using congrFun ((b.baseChange Left).repr_sum_self c) i

example (b : Basis ι K Left) (z : Left ⊗[K] Right) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
    ∑ i, (b.baseChangeRight (Right := Right)).repr z i • (b i ⊗ₜ[K] (1 : Right)) = z := by
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
  simpa only [Basis.baseChangeRight_apply] using (b.baseChangeRight (Right := Right)).sum_repr z

example (b : Basis ι K Left) (c : ι → Right) (i : ι) :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
    (b.baseChangeRight (Right := Right)).repr
      (∑ j, c j • (b j ⊗ₜ[K] (1 : Right))) i = c i := by
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := Left) (B := Right)
  simpa only [Basis.baseChangeRight_apply] using
    congrFun ((b.baseChangeRight (Right := Right)).repr_sum_self c) i

end Coordinates

section EqualFactors

variable {K L ι : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L] [Fintype ι]

-- Exercise the documented proof-local recipe on arbitrary tensors with equal factors.
example (b : Basis ι K L) (z : L ⊗[K] L) :
    letI rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := L)
    letI := rightAlgebra.toModule
    letI := rightAlgebra.toModule.toDistribMulAction
    letI := rightAlgebra.toSMul
    ∑ i, (b.baseChangeRight (Right := L)).repr z i • (b i ⊗ₜ[K] (1 : L)) = z := by
  let rightAlgebra := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := L)
  let := rightAlgebra.toModule
  let := rightAlgebra.toModule.toDistribMulAction
  let := rightAlgebra.toSMul
  simpa only [Basis.baseChangeRight_apply] using (b.baseChangeRight (Right := L)).sum_repr z

section LocalRightAction

/-- The `L`-algebra structure on `L ⊗[K] L` induced by `r ↦ 1 ⊗ r`. -/
noncomputable local instance tensorRightAlgebra : Algebra L (L ⊗[K] L) :=
  Algebra.TensorProduct.rightAlgebra

noncomputable local instance : Module L (L ⊗[K] L) :=
  (tensorRightAlgebra (K := K) (L := L)).toModule

noncomputable local instance : DistribMulAction L (L ⊗[K] L) :=
  (tensorRightAlgebra (K := K) (L := L)).toModule.toDistribMulAction

noncomputable local instance : SMul L (L ⊗[K] L) :=
  (tensorRightAlgebra (K := K) (L := L)).toSMul

example (b : Basis ι K L) (c : ι → L) (i : ι) :
    (b.baseChangeRight (Right := L)).repr (∑ j, c j • (b j ⊗ₜ[K] (1 : L))) i = c i := by
  simpa only [Basis.baseChangeRight_apply] using
    congrFun ((b.baseChangeRight (Right := L)).repr_sum_self c) i

example (x y r : L) : r • (x ⊗ₜ[K] y) = x ⊗ₜ[K] (r * y) := by
  change (Algebra.TensorProduct.includeRight r : L ⊗[K] L) * (x ⊗ₜ[K] y) = _
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

-- Ordinary module and algebra lemmas must use the action selected for scalar notation.
example (r s : L) (x y : L ⊗[K] L) :
    r • (x + y) = r • x + r • y ∧ (r + s) • x = r • x + s • x ∧
      (r * s) • x = r • (s • x) ∧ (1 : L) • x = x ∧ (0 : L) • x = 0 ∧
      r • (0 : L ⊗[K] L) = 0 ∧ r • x = algebraMap L (L ⊗[K] L) r * x ∧
      r • x * y = r • (x * y) ∧ x * (r • y) = r • (x * y) := by
  exact ⟨smul_add r x y, add_smul r s x, mul_smul r s x, one_smul L x,
    zero_smul L x, smul_zero r, Algebra.smul_def r x,
    Algebra.smul_mul_assoc r x y, Algebra.mul_smul_comm r x y⟩

example (k : K) (r : L) (x : L ⊗[K] L) : (k • r) • x = k • (r • x) :=
  smul_assoc k r x

end LocalRightAction

-- The local hierarchy leaves all four surrounding defaults unchanged.
example : algebraMap L (L ⊗[K] L) = Algebra.TensorProduct.includeLeftRingHom := rfl
example : (inferInstance : Module L (L ⊗[K] L)) = TensorProduct.leftModule := rfl
example : (inferInstance : DistribMulAction L (L ⊗[K] L)) =
    TensorProduct.leftDistribMulAction := rfl
example : (inferInstance : SMul L (L ⊗[K] L)) = TensorProduct.leftHasSMul := rfl

end EqualFactors

section ProperExtension

open Complex

/-- Complex coordinates in the left-action basis `1 ⊗ 1, 1 ⊗ I` of `ℂ ⊗[ℝ] ℂ`. -/
private noncomputable def leftCoords (z : ℂ ⊗[ℝ] ℂ) : Fin 2 →₀ ℂ :=
  (basisOneI.baseChange ℂ).repr z

/-- Complex coordinates in the right-action basis `1 ⊗ 1, I ⊗ 1` of `ℂ ⊗[ℝ] ℂ`. -/
private noncomputable def rightCoords (z : ℂ ⊗[ℝ] ℂ) : Fin 2 →₀ ℂ := by
  letI := Algebra.TensorProduct.rightAlgebra (R := ℝ) (A := ℂ) (B := ℂ)
  letI := (Algebra.TensorProduct.rightAlgebra (R := ℝ) (A := ℂ) (B := ℂ)).toModule
  exact (basisOneI.baseChangeRight (Right := ℂ)).repr z

example : leftCoords (I ⊗ₜ[ℝ] (1 : ℂ)) 1 = 0 := by
  simp [leftCoords, Basis.baseChange_repr_tmul, coe_basisOneI_repr]

example : rightCoords (I ⊗ₜ[ℝ] (1 : ℂ)) 1 = 1 := by
  simp [rightCoords, Basis.baseChangeRight_repr_tmul, coe_basisOneI_repr]

-- Interchanging factors changes the tensor, even though the scalar types are identical.
example : I ⊗ₜ[ℝ] (1 : ℂ) ≠ (1 : ℂ) ⊗ₜ[ℝ] I := by
  intro h
  have bad := congrArg (fun z => leftCoords z 1) h
  simp [leftCoords, Basis.baseChange_repr_tmul, coe_basisOneI_repr] at bad

-- The row and column coefficient systems cannot be silently identified.
example : leftCoords (I ⊗ₜ[ℝ] (1 : ℂ)) ≠ rightCoords (I ⊗ₜ[ℝ] (1 : ℂ)) := by
  intro h
  have bad := congrArg (fun c : Fin 2 →₀ ℂ => c 1) h
  simp [leftCoords, rightCoords, Basis.baseChange_repr_tmul,
    Basis.baseChangeRight_repr_tmul, coe_basisOneI_repr] at bad

end ProperExtension

end CompPolyTests.TensorProductBasis
