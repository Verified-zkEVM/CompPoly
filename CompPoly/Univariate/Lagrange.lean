/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Katerina Hristova, Julian Sutherland
-/
import Mathlib.LinearAlgebra.Lagrange
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly

/-!
  # Lagrange Interpolation

  This file defines computable Lagrange interpolation
  for univariate polynomials, i.e. `CPolynomial`s.
-/
namespace CompPoly

namespace CPolynomial

namespace CLagrange

variable {R : Type*} [BEq R] [Field R] [LawfulBEq R]

/-- `basisDivisor xᵢ xⱼ` is the unique linear or constant computable polynomial such that
when evaluated at `xᵢ` it gives `1` and `xⱼ` it gives `0` (where when `xᵢ = xⱼ` it is
identically `0`). Such polynomials are the building blocks for the Lagrange interpolants. -/
def basisDivisor (xᵢ xⱼ : R) : CPolynomial R :=
  C (xᵢ - xⱼ)⁻¹ * (X - C xⱼ)

lemma cbasisDivisor_eq_basisDivisor {xᵢ xⱼ : R} : (basisDivisor xᵢ xⱼ).toPoly = Lagrange.basisDivisor xᵢ xⱼ := by
  unfold basisDivisor Lagrange.basisDivisor
  simp only [toPoly_mul, C_toPoly, toPoly_sub, X_toPoly]

/-- Computable Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `x i` for a
map `x : ι → F`. For `i, j ∈ s`, `basis s x i` evaluates to `0` at `x j` for `i ≠ j`. When
`x` is injective on `s`, `basis s x i` evaluates to 1 at `x i`. -/
def basis {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
    CPolynomial R := ∏ j ∈ s.erase i, basisDivisor (x i) (x j)

lemma cbasis_eq_basis {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
    (basis s x i).toPoly = Lagrange.basis s x i := by
  unfold basis Lagrange.basis
  rw [toPoly_prod]
  congr
  funext j
  rw [cbasisDivisor_eq_basisDivisor]

/-- Computable Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `x : ι → F`
injective on `s` and a value function `y : ι → F`, `interpolate s x y` is the unique computable
polynomial of degree `< #s` that takes value `y i` on `x i` for all `i` in `s`. -/
def interpolate {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) :
    (ι → R) →ₗ[R] CPolynomial R where
    toFun := fun y ↦ ∑ i ∈ s, C (y i) * basis s x i
    map_add' := by
      intros r₁ r₂
      rw [←Finset.sum_add_distrib]
      congr
      funext i
      rw [CPolynomial.eq_iff_coeff]
      intros n
      erw [
        coeff_add,
        coeff_C_mul, coeff_C_mul, coeff_C_mul,
        @NonUnitalNonAssocRing.right_distrib
      ]
    map_smul' := by
      intros m r
      have h₁ : ∑ i ∈ s, C ((m • r) i) * basis s x i  = ∑ i ∈ s, C m * (C (r i) * basis s x i) := by
        congr
        funext i
        rw [Pi.smul_apply, smul_eq_mul, CPolynomial.eq_iff_coeff]
        intros n
        rw [coeff_C_mul, coeff_C_mul, coeff_C_mul, ←_root_.mul_assoc]
      rw [h₁, ←Finset.mul_sum]
      rfl

lemma cinterpolate_eq_interpolate {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → R} {y : ι → R} :
    (interpolate s x y).toPoly = Lagrange.interpolate s x y := by
  unfold interpolate
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Lagrange.interpolate_apply]
  rw [toPoly_sum]
  congr
  funext i
  rw [toPoly_mul, C_toPoly, cbasis_eq_basis]

/-- Produces the unique polynomial of degree at most n-1 that equals r[i] at ω^i
    for i = 0, 1, ..., n-1.

    Uses Lagrange interpolation: p(X) = Σᵢ rᵢ · Lᵢ(X)
    where Lᵢ(X) = ∏_{j≠i} (X - ωʲ) / (ωⁱ - ωʲ). -/
def interpolatePow {n : ℕ} (ω : R) (r : Vector R n) :
    CPolynomial R := interpolate Finset.univ (fun i ↦ ω ^ i.val) r.get

/-
If ω^a = ω^b for a, b < n ≤ orderOf ω, then a = b.
-/
theorem eq_of_pow_eq_pow_of_lt_orderOf {G : Type*} [Group G] {ω : G} {n : ℕ}
    (h_order : n ≤ orderOf ω) (a b : Fin n) (h_pow : ω ^ (a : ℕ) = ω ^ (b : ℕ)) : a = b := by
  rw [ pow_eq_pow_iff_modEq ] at h_pow;
  exact Fin.ext
    (
      (Nat.mod_eq_of_lt ( show ( a : ℕ ) < orderOf ω from lt_of_lt_of_le a.2 h_order )) ▸
        Nat.mod_eq_of_lt ( show ( b : ℕ ) < orderOf ω from lt_of_lt_of_le b.2 h_order ) ▸ h_pow
    )

/--
  Key correctness theorem for `interpolatePow`.
-/
lemma eval_interpolatePow_at_node {n : ℕ} {ω : Rˣ} {r : Vector R n} : n < orderOf ω →
    ∀ i : Fin n, (interpolatePow ω.1 r).eval (ω.1 ^ i.1) = r.get i := by
  intros order_ω_lt_n i
  unfold interpolatePow
  rw [
    eval_toPoly,
    cinterpolate_eq_interpolate,
    Lagrange.eval_interpolate_at_node (v := (fun (i : Fin n) ↦ ω.1 ^ i.val))
  ]
  · simp only [Finset.coe_univ, Set.injOn_univ]
    intros a b h
    simp only at h
    apply Fin.eq_of_val_eq
    have h₁ : a.1 < orderOf ω := by
      omega
    have h₂ : b.1 < orderOf ω := by
      omega
    have h₃ : ω ^ a.1 = ω ^ b.1 := by
      rw [←Units.val_inj]
      simpa using h
    have h_le : n ≤ orderOf ω := le_of_lt order_ω_lt_n
    have h_eq : a = b := eq_of_pow_eq_pow_of_lt_orderOf h_le a b h₃
    exact congr_arg Fin.val h_eq
  · exact Finset.mem_univ _

end CLagrange

end CPolynomial

end CompPoly
