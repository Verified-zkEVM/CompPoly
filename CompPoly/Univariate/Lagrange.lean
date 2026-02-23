/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Katerina Hristova, Julian Sutherland.
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

lemma toPoly_sub {p q : CPolynomial R} : (p - q).toPoly = p.toPoly - q.toPoly := by
  rw [← Polynomial.coeff_inj]
  funext i
  rw [Polynomial.coeff_sub, ← coeff_toPoly]
  have hp : p.toPoly.coeff i = p.coeff i := by rw [coeff_toPoly]
  have hq : q.toPoly.coeff i = q.coeff i := by rw [coeff_toPoly]
  rw [hp, hq, @coeff_sub]

lemma toPoly_prod.{u} {ι : Type u} [DecidableEq ι] {s : Finset ι} {f : ι → CPolynomial R} :
  (∏ j ∈ s, f j).toPoly = ∏ j ∈ s, ((f j).toPoly) := by
  generalize n_eq : s.card = n
  revert s
  induction n with
  | zero =>
    simp only [Finset.card_eq_zero, forall_eq, Finset.prod_empty]
    exact Raw.toPoly_one
  | succ n ih =>
    intros s h
    have s_has_elm : ∃ i, i ∈ s := by
      rw [←Finset.nonempty_def, ←Finset.card_pos]
      simp [h]
    rcases s_has_elm with ⟨i, i_in_s⟩
    have : s = {i} ∪ (s.erase i) := by
      refine Eq.symm (Finset.ext ?_)
      intros a
      simp only [Finset.singleton_union, Finset.mem_insert, Finset.mem_erase, ne_eq]
      have := eq_or_ne a i
      aesop
    have s_disjoint : Disjoint {i} (s.erase i) := by simp
    rw [this, Finset.prod_union s_disjoint, Finset.prod_union s_disjoint]
    simp only [Finset.prod_singleton, toPoly_mul]
    rw [@ih (s.erase i)]
    rw [@Finset.card_erase_eq_ite]
    simp [i_in_s, h]

lemma toPoly_sum.{u} {ι : Type u} [DecidableEq ι] {s : Finset ι} {f : ι → CPolynomial R} :
  (∑ j ∈ s, f j).toPoly = ∑ j ∈ s, ((f j).toPoly) := by
  generalize n_eq : s.card = n
  revert s
  induction n with
  | zero =>
    simp only [Finset.card_eq_zero, forall_eq, Finset.sum_empty]
    exact Raw.toPoly_zero
  | succ n ih =>
    intros s h
    have s_has_elm : ∃ i, i ∈ s := by
      rw [←Finset.nonempty_def, ←Finset.card_pos]
      simp [h]
    rcases s_has_elm with ⟨i, i_in_s⟩
    have : s = {i} ∪ (s.erase i) := by
      refine Eq.symm (Finset.ext ?_)
      intros a
      simp only [Finset.singleton_union, Finset.mem_insert, Finset.mem_erase, ne_eq]
      have := eq_or_ne a i
      aesop
    have s_disjoint : Disjoint {i} (s.erase i) := by simp
    rw [this, Finset.sum_union s_disjoint, Finset.sum_union s_disjoint]
    simp only [Finset.sum_singleton]
    have CPoly_add {p q : CPolynomial R} : (p + q).toPoly = p.toPoly + q.toPoly := by
      apply Raw.toPoly_add
    rw [CPoly_add, @ih (s.erase i)]
    simp [Finset.card_erase_of_mem i_in_s, h]

/-- `basisDivisor xᵢ xⱼ` is the unique linear or constant computable polynomial such that
when evaluated at `xᵢ` it gives `1` and `xⱼ` it gives `0` (where when `xᵢ = xⱼ` it is
identically `0`). Such polynomials are the building blocks for the Lagrange interpolants. -/
def basisDivisor (xᵢ xⱼ : R) : CPolynomial R :=
  C (xᵢ - xⱼ)⁻¹ * (X - C xⱼ)

lemma cBasisDivisorEq {xᵢ xⱼ : R} : (basisDivisor xᵢ xⱼ).toPoly = Lagrange.basisDivisor xᵢ xⱼ := by
  unfold basisDivisor Lagrange.basisDivisor
  simp only [toPoly_mul, C_toPoly, toPoly_sub, X_toPoly]

/-- Computable Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `x i` for a
map `x : ι → F`. For `i, j ∈ s`, `basis s x i` evaluates to `0` at `x j` for `i ≠ j`. When
`x` is injective on `s`, `basis s x i` evaluates to 1 at `x i`. -/
def basis.{u} {ι : Type u} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
  CPolynomial R := ∏ j ∈ s.erase i, basisDivisor (x i) (x j)

lemma cBasisEq {ι : Type u} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
    (basis s x i).toPoly = Lagrange.basis s x i := by
  unfold basis Lagrange.basis
  rw [toPoly_prod]
  congr
  funext j
  rw [cBasisDivisorEq]

/-- Computable Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `x : ι → F`
injective on `s` and a value function `y : ι → F`, `interpolate s x y` is the unique computable
polynomial of degree `< #s` that takes value `y i` on `x i` for all `i` in `s`. -/
def interpolate.{u} {ι : Type u} [DecidableEq ι] (s : Finset ι) (x : ι → R) :
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

lemma lagrangeEq {ι : Type u} [DecidableEq ι] {s : Finset ι} {x : ι → R} {y : ι → R} :
  (interpolate s x y).toPoly = Lagrange.interpolate s x y := by
  unfold interpolate
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Lagrange.interpolate_apply]
  rw [toPoly_sum]
  congr
  funext i
  rw [toPoly_mul, C_toPoly, cBasisEq]

/-- Produces the unique polynomial of degree at most n-1 that equals r[i] at ω^i
    for i = 0, 1, ..., n-1.

    Uses Lagrange interpolation: p(X) = Σᵢ rᵢ · Lᵢ(X)
    where Lᵢ(X) = ∏_{j≠i} (X - ωʲ) / (ωⁱ - ωʲ). -/
def interpolatePow {n : ℕ} (ω : R) (r : Vector R n) :
    CPolynomial R := interpolate (Finset.univ : Finset (Fin n)) (fun i ↦ ω ^ i.val) r.get

end CLagrange

end CPolynomial

end CompPoly
