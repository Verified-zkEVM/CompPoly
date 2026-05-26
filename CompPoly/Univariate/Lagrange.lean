/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen, Katerina Hristova, Julian Sutherland
-/
import Mathlib.LinearAlgebra.Lagrange
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly.Impl

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

lemma cbasisDivisor_eq_basisDivisor {xᵢ xⱼ : R} :
    (basisDivisor xᵢ xⱼ).toPoly = Lagrange.basisDivisor xᵢ xⱼ := by
  unfold basisDivisor Lagrange.basisDivisor
  simp only [toPoly_mul, C_toPoly, toPoly_sub, X_toPoly]

/-! ### Helpers for deferred-trim folds

The `basis` product and `interpolate` sum below combine raw arrays with the untrimmed
`Raw.mulRaw`/`Raw.addRaw` and trim once at the end, rather than paying a trim per factor
(as `Finset.prod`/`Finset.sum` over the canonical `CPolynomial.Mul`/`.Add` instances
would). Computability requires bypassing the noncomputable `Finset.toList`, so the folds
go through `Quotient.liftOn` on the underlying multiset with a permutation-invariance
proof routed through `toPoly`. -/

/-- `basisDivisor`-product fold over a list, combining factors with the untrimmed
`Raw.mulRaw`. The wrapping `basis` definition trims this once. -/
private def basisListRaw {ι : Type*} (x : ι → R) (i : ι) (l : List ι) :
    CPolynomial.Raw R :=
  l.foldr (fun j acc => Raw.mulRaw (basisDivisor (x i) (x j)).val acc) (Raw.C 1)

private lemma toPoly_basisListRaw {ι : Type*} (x : ι → R) (i : ι) (l : List ι) :
    (basisListRaw x i l).toPoly =
      (l.map (fun j => Lagrange.basisDivisor (x i) (x j))).prod := by
  induction l with
  | nil =>
      show (Raw.C 1).toPoly = (1 : Polynomial R)
      rw [Raw.toPoly_C, Polynomial.C_1]
  | cons head tail ih =>
      show (Raw.mulRaw (basisDivisor (x i) (x head)).val (basisListRaw x i tail)).toPoly = _
      have hmul : (Raw.mulRaw (basisDivisor (x i) (x head)).val (basisListRaw x i tail)).toPoly
          = (basisDivisor (x i) (x head)).val.toPoly * (basisListRaw x i tail).toPoly := by
        rw [← Raw.toPoly_trim]
        exact Raw.toPoly_mul _ _
      have hbd : (basisDivisor (x i) (x head)).val.toPoly
          = Lagrange.basisDivisor (x i) (x head) := cbasisDivisor_eq_basisDivisor
      rw [hmul, hbd, ih, List.map_cons, List.prod_cons]

private lemma basisListRaw_trim_perm {ι : Type*} (x : ι → R) (i : ι)
    {l₁ l₂ : List ι} (h : l₁.Perm l₂) :
    (basisListRaw x i l₁).trim = (basisListRaw x i l₂).trim := by
  apply Raw.Trim.isCanonical_ext (Raw.Trim.isCanonical_trim _) (Raw.Trim.isCanonical_trim _)
  intro k
  rw [Raw.Trim.coeff_eq_coeff, Raw.Trim.coeff_eq_coeff,
      ← Raw.coeff_toPoly, ← Raw.coeff_toPoly,
      toPoly_basisListRaw, toPoly_basisListRaw]
  exact congrArg (fun p : Polynomial R => p.coeff k) (h.map _).prod_eq

/-- Computable Lagrange basis polynomials indexed by `s : Finset ι`, defined at nodes `x i` for a
map `x : ι → F`. For `i, j ∈ s`, `basis s x i` evaluates to `0` at `x j` for `i ≠ j`. When
`x` is injective on `s`, `basis s x i` evaluates to 1 at `x i`.

The product folds `(s.erase i).val` with the untrimmed `Raw.mulRaw` via `Quotient.liftOn`
and trims once at the end, rather than paying one `Raw.mul` trim per factor (as the
`Finset.prod` formulation would). -/
def basis {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
    CPolynomial R :=
  Quotient.liftOn (s.erase i).val
    (fun l => ⟨(basisListRaw x i l).trim, Raw.Trim.isCanonical_trim _⟩)
    (fun _ _ h => Subtype.ext (basisListRaw_trim_perm x i h))

lemma cbasis_eq_basis {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) (i : ι) :
    (basis s x i).toPoly = Lagrange.basis s x i := by
  obtain ⟨l, hl⟩ := Quotient.exists_rep (s.erase i).val
  have hbasis : basis s x i =
      ⟨(basisListRaw x i l).trim, Raw.Trim.isCanonical_trim _⟩ := by
    show Quotient.liftOn (s.erase i).val _ _ = _
    rw [← hl]; rfl
  rw [hbasis]
  show (basisListRaw x i l).trim.toPoly = Lagrange.basis s x i
  rw [Raw.toPoly_trim, toPoly_basisListRaw]
  unfold Lagrange.basis
  rw [Finset.prod_eq_multiset_prod, ← hl]
  rfl

/-! ### Interpolation sum

The `interpolate` sum is folded with the untrimmed `Raw.addRaw`, with each addend itself
formed by `Raw.mulRaw (Raw.C (y i)) (basis s x i).val` (also untrimmed). One `trim` runs
at the end of the entire fold. -/

private def interpolateListRaw {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) (l : List ι) : CPolynomial.Raw R :=
  l.foldr
    (fun i acc => Raw.addRaw (Raw.mulRaw (Raw.C (y i)) (basis s x i).val) acc)
    (Raw.mk #[])

private lemma toPoly_interpolateListRaw {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) (l : List ι) :
    (interpolateListRaw s x y l).toPoly =
      (l.map (fun i => Polynomial.C (y i) * Lagrange.basis s x i)).sum := by
  induction l with
  | nil =>
      show (Raw.mk #[] : CPolynomial.Raw R).toPoly = 0
      change (0 : CPolynomial.Raw R).toPoly = 0
      exact Raw.toPoly_zero
  | cons head tail ih =>
      show (Raw.addRaw (Raw.mulRaw (Raw.C (y head)) (basis s x head).val)
              (interpolateListRaw s x y tail)).toPoly = _
      rw [Raw.toPoly_addRaw]
      have hmul : (Raw.mulRaw (Raw.C (y head)) (basis s x head).val).toPoly
          = Polynomial.C (y head) * Lagrange.basis s x head := by
        rw [← Raw.toPoly_trim]
        change ((Raw.C (y head)) * (basis s x head).val).toPoly = _
        rw [Raw.toPoly_mul, Raw.toPoly_C]
        congr 1
        exact cbasis_eq_basis s x head
      rw [hmul, ih, List.map_cons, List.sum_cons]

private lemma interpolateListRaw_trim_perm {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) {l₁ l₂ : List ι} (h : l₁.Perm l₂) :
    (interpolateListRaw s x y l₁).trim = (interpolateListRaw s x y l₂).trim := by
  apply Raw.Trim.isCanonical_ext (Raw.Trim.isCanonical_trim _) (Raw.Trim.isCanonical_trim _)
  intro k
  rw [Raw.Trim.coeff_eq_coeff, Raw.Trim.coeff_eq_coeff,
      ← Raw.coeff_toPoly, ← Raw.coeff_toPoly,
      toPoly_interpolateListRaw, toPoly_interpolateListRaw]
  exact congrArg (fun p : Polynomial R => p.coeff k) (h.map _).sum_eq

/-- Computable raw-fold form of the interpolation polynomial: defer trimming to the
end of the `Finset.sum`. -/
private def interpolateRaw {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) : CPolynomial R :=
  Quotient.liftOn s.val
    (fun l => ⟨(interpolateListRaw s x y l).trim, Raw.Trim.isCanonical_trim _⟩)
    (fun _ _ h => Subtype.ext (interpolateListRaw_trim_perm s x y h))

private lemma toPoly_interpolateRaw {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {x : ι → R} {y : ι → R} :
    (interpolateRaw s x y).toPoly =
      ∑ i ∈ s, Polynomial.C (y i) * Lagrange.basis s x i := by
  obtain ⟨l, hl⟩ := Quotient.exists_rep s.val
  have hraw : interpolateRaw s x y =
      ⟨(interpolateListRaw s x y l).trim, Raw.Trim.isCanonical_trim _⟩ := by
    show Quotient.liftOn s.val _ _ = _
    rw [← hl]; rfl
  rw [hraw]
  show (interpolateListRaw s x y l).trim.toPoly = _
  rw [Raw.toPoly_trim, toPoly_interpolateListRaw]
  rw [Finset.sum_eq_multiset_sum, ← hl]
  rfl

private lemma interpolateRaw_eq_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → R) (y : ι → R) :
    interpolateRaw s x y = ∑ i ∈ s, C (y i) * basis s x i := by
  apply CPolynomial.ext
  apply Raw.Trim.isCanonical_ext (interpolateRaw s x y).property
    (∑ i ∈ s, C (y i) * basis s x i).property
  intro k
  rw [← Raw.coeff_toPoly, ← Raw.coeff_toPoly]
  change (interpolateRaw s x y).toPoly.coeff k =
    (∑ i ∈ s, C (y i) * basis s x i).toPoly.coeff k
  rw [toPoly_interpolateRaw, toPoly_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [toPoly_mul, C_toPoly, cbasis_eq_basis]

/-- Computable Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `x : ι → F`
injective on `s` and a value function `y : ι → F`, `interpolate s x y` is the unique computable
polynomial of degree `< #s` that takes value `y i` on `x i` for all `i` in `s`. -/
def interpolate {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → R) :
    (ι → R) →ₗ[R] CPolynomial R where
    toFun := fun y ↦ interpolateRaw s x y
    map_add' := by
      intros r₁ r₂
      rw [interpolateRaw_eq_sum, interpolateRaw_eq_sum, interpolateRaw_eq_sum]
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
      rw [interpolateRaw_eq_sum, interpolateRaw_eq_sum]
      have h₁ : ∑ i ∈ s, C ((m • r) i) * basis s x i  = ∑ i ∈ s, C m * (C (r i) * basis s x i) := by
        congr
        funext i
        rw [Pi.smul_apply, smul_eq_mul, CPolynomial.eq_iff_coeff]
        intros n
        rw [coeff_C_mul, coeff_C_mul, coeff_C_mul, ←_root_.mul_assoc]
      rw [h₁, ←Finset.mul_sum]
      simp only [RingHom.id_apply]
      rw [eq_iff_coeff]; intro i; rw [coeff_C_mul, coeff_smul]



lemma cinterpolate_eq_interpolate
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → R} {y : ι → R} :
      (interpolate s x y).toPoly = Lagrange.interpolate s x y := by
  show (interpolateRaw s x y).toPoly = _
  rw [toPoly_interpolateRaw, Lagrange.interpolate_apply]

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
