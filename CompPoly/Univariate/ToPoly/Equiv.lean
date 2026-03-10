 /-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
 -/
import CompPoly.Univariate.ToPoly.Core

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*} [Ring R] [BEq R]
variable {Q : Type*} [Ring Q]

section RingEquiv

@[grind =]
lemma toPoly_neg [LawfulBEq R] (p : CPolynomial R) :
    (-p).toPoly = -p.toPoly := by
  ext i
  rw [Polynomial.coeff_neg, CPolynomial.toPoly, CPolynomial.toPoly]
  rw [Raw.coeff_toPoly, Raw.coeff_toPoly]
  simpa using (Raw.neg_coeff (p := p.val) (i := i))

@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  apply Raw.toPoly_add

@[grind =]
lemma toPoly_sub [LawfulBEq R] (p q : CPolynomial R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  change (p + -q).toPoly = p.toPoly + -q.toPoly
  rw [toPoly_add, toPoly_neg]

@[grind =]
lemma Raw.toPoly_mul_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (i : ℕ) :
    (p * q).toPoly.coeff i = (p.toPoly * q.toPoly).coeff i := by
  rw [coeff_toPoly, mul_coeff, Polynomial.coeff_mul]; simp
  have h_antidiagonal :
      Finset.HasAntidiagonal.antidiagonal i =
      Finset.image (fun x => (x, i - x)) (Finset.range (i + 1)) := by
    exact Finset.Nat.antidiagonal_eq_image i
  simp [h_antidiagonal ]
  have h_coeff : ∀ x, p.toPoly.coeff x = p[x]?.getD 0 ∧ q.toPoly.coeff x = q[x]?.getD 0 := by
    intro x
    repeat rw [coeff_toPoly]
    constructor <;> simp
  refine Finset.sum_congr rfl ?_
  intro x hx
  rcases h_coeff x with ⟨hp, _hq⟩
  rcases h_coeff (i - x) with ⟨_, hq⟩
  simp [hp, hq]

@[grind =]
lemma toPoly_mul_coeffC [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p.val * q.val).toPoly.coeff i = (p.val.toPoly * q.val.toPoly).coeff i := by
  simpa using Raw.toPoly_mul_coeff p.val q.val i

@[grind =]
lemma toPoly_mul [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  ext i
  exact toPoly_mul_coeffC p q i

@[simp, grind =]
lemma eval₂_C {R : Type*} [Ring R] [BEq R] {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (r : R) :
    (Raw.C r).eval₂ f x = f r := by
  unfold CPolynomial.Raw.eval₂ Raw.C
  ring_nf
  simp [Array.zipIdx]

@[simp, grind =]
lemma Raw.toPoly_C {R : Type*} [Ring R] [BEq R] (r : R) :
    (Raw.C r).toPoly = Polynomial.C r := by
  unfold Raw.toPoly
  exact eval₂_C Polynomial.C Polynomial.X r

@[simp, grind =]
lemma Raw.toPoly_one [LawfulBEq R] :
    (1 : CPolynomial.Raw R).toPoly = 1 := by
  have : (1 : CPolynomial.Raw R).toPoly = (Raw.C 1).toPoly := by rfl
  apply this.trans; clear this
  apply toPoly_C

lemma toPoly_one [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).toPoly = 1 := by apply Raw.toPoly_one

omit [BEq R] in
@[simp, grind =]
lemma Raw.toPoly_zero : (0 : CPolynomial.Raw R).toPoly = 0 := by
  simp [Raw.toPoly, Raw.eval₂]

lemma toPoly_zero : (0 : CPolynomial R).toPoly = 0 := by
  apply Raw.toPoly_zero

@[simp, grind =]
lemma Raw.toPoly_X [LawfulBEq R] :
    (Raw.X : CPolynomial.Raw R).toPoly = Polynomial.X := by
  unfold CPolynomial.Raw.X
  simp [Raw.toPoly, Raw.eval₂]

@[grind =]
lemma toPoly_pow [Nontrivial R] [LawfulBEq R] (p : CPolynomial R) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := by
  induction n with
  | zero =>
    simp only [_root_.pow_zero]
    rw [toPoly_one]
  | succ n ih =>
    have hp : p ^ (n + 1) = p ^ n * p := by
      apply ext
      change (p.val ^ (n + 1)) = (p.val ^ n * p.val)
      rw [pow_succ_right]
    have htp : p.toPoly ^ (n + 1) = p.toPoly ^ n * p.toPoly := by
      simpa using (_root_.pow_succ (p.toPoly : R[X]) n)
    rw [hp, toPoly_mul, ih, htp]

lemma toPoly_sum.{u} {R : Type*} [BEq R] [Field R] [LawfulBEq R] {ι : Type u} [DecidableEq ι]
    {s : Finset ι} {f : ι → CPolynomial R} :
      (∑ j ∈ s, f j).toPoly = ∑ j ∈ s, ((f j).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (toPoly_zero (R := R))
  | insert a s ha ih =>
      simp [Finset.sum_insert, ha, toPoly_add, ih]

lemma toPoly_prod.{u} {R : Type*} [BEq R] [Field R] [LawfulBEq R] {ι : Type u} [DecidableEq ι]
    {s : Finset ι} {f : ι → CPolynomial R} :
      (∏ j ∈ s, f j).toPoly = ∏ j ∈ s, ((f j).toPoly) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [toPoly_one]
  | insert a s ha ih =>
      simp [Finset.prod_insert, ha, toPoly_mul, ih]

noncomputable def ringEquiv [LawfulBEq R] :
  CPolynomial R ≃+* Polynomial R where
  toFun := CPolynomial.toPoly
  invFun := fun p => ⟨p.toImpl, trim_toImpl p⟩
  left_inv := by
    unfold Function.LeftInverse; intro x
    apply Subtype.ext; apply toImpl_toPoly_of_canonical
  right_inv := by
    unfold Function.RightInverse CPolynomial.toPoly
    apply toPoly_toImpl
  map_mul' := by intros p q; rw [toPoly_mul p q]
  map_add' := by intros p q; apply toPoly_add

end RingEquiv

section ImplementationCorrectness

theorem monomial_toPoly [DecidableEq R] [LawfulBEq R] (n : ℕ) (c : R) :
    (monomial n c).toPoly = Polynomial.monomial n c := by
  ext i
  simp only [CPolynomial.toPoly, monomial]
  rw [Polynomial.coeff_monomial, coeff_toPoly, CPolynomial.Raw.coeff_monomial]

theorem C_toPoly [LawfulBEq R] (r : R) : (C r).toPoly = Polynomial.C r := by
  convert Raw.toPoly_C r
  convert Raw.toPoly_trim
  infer_instance

theorem X_toPoly [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).toPoly = Polynomial.X := by
  convert Raw.toPoly_X using 1
  (expose_names; infer_instance)
  infer_instance

theorem eval_toPoly [LawfulBEq R] (x : R) (p : CPolynomial R) :
    eval x p = p.toPoly.eval x := by
  convert Raw.eval_toPoly_eq_eval x p.val
  · rw [ Raw.eval_toPoly_eq_eval ]; rfl
  · convert Raw.eval_toPoly_eq_eval x p.val

omit [BEq R] in
theorem Raw.eval₂_toPoly {S : Type*} [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial.Raw R) :
    p.eval₂ f x = p.toPoly.eval₂ f x := by
  unfold CompPoly.CPolynomial.Raw.toPoly CompPoly.CPolynomial.Raw.eval₂
  rw [← Array.foldl_hom (fun q : R[X] => q.eval₂ f x)
    (g₁ := fun acc (t : R × ℕ) => acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) => acc + f a * x ^ i)]
  · simp
  · intro acc t
    rcases t with ⟨a, i⟩
    simp [Polynomial.eval₂_add, Polynomial.C_mul_X_pow_eq_monomial]

theorem eval₂_toPoly {S : Type*} [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂ f x p = p.toPoly.eval₂ f x := by
  simpa [CompPoly.CPolynomial.eval₂, CompPoly.CPolynomial.toPoly] using
    (Raw.eval₂_toPoly (f := f) (x := x) (p := p.val))

theorem coeff_toPoly [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    p.coeff i = p.toPoly.coeff i := by
  unfold toPoly coeff
  simp [Raw.coeff_toPoly]

theorem divX_toPoly [LawfulBEq R] (p : CPolynomial R) :
    (divX p).toPoly = p.toPoly.divX := by
  ext n
  simp only [CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly, CPolynomial.coeff,
    CompPoly.CPolynomial.coeff_divX, Polynomial.coeff_divX]

theorem support_toPoly [LawfulBEq R] (p : CPolynomial R) :
    p.support = p.toPoly.support := by
  convert Set.ext _
  rotate_left
  exact ℕ
  exact { i | p.val.coeff i ≠ 0 }
  exact { i | ( p.toPoly.coeff i ) ≠ 0 }
  · simp +zetaDelta at *
    intro x
    convert Iff.rfl
    convert Raw.coeff_toPoly
    exact Eq.symm Array.getD_eq_getD_getElem?
  · simp +decide [ CPolynomial.support, Finset.ext_iff, Set.ext_iff ]
    grind

end ImplementationCorrectness

end CPolynomial

end CompPoly
