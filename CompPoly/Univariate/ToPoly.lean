/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import CompPoly.Data.Array.Lemmas
import CompPoly.Univariate.Basic

/-!
  # Equivalence with Mathlib Polynomials

  This file establishes the equivalence between `CPolynomial.Raw R` and mathlib's `Polynomial R`.
  The main results (thus far) are:
  - `toPoly`: converts `CPolynomial.Raw R` to `Polynomial R`
  - `ofPoly` (aliased from `Polynomial.toImpl`): converts `Polynomial R` to `CPolynomial.Raw R`
  - `toPoly_toImpl`: the round-trip from `Polynomial` is the identity
  - `toImpl_toPoly_of_canonical`: the round-trip from canonical `CPolynomial.Raw` is the identity

  This shows that `CPolynomial R` is isomorphic to `Polynomial R`.
-/

open Polynomial

/-- Convert a mathlib `Polynomial` to a `CPolynomial.Raw` by extracting coefficients
up to the degree. -/
def Polynomial.toImpl {R : Type*} [Semiring R] (p : R[X]) : CompPoly.CPolynomial.Raw R :=
  match p.degree with
  | ⊥ => #[]
  | some d  => .ofFn (fun i : Fin (d + 1) => p.coeff i)

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*} [Ring R] [BEq R]

variable {Q : Type*} [Ring Q]

section ToPoly

/-- Convert a `CPolynomial.Raw` to a (mathlib) `Polynomial`. -/
noncomputable def Raw.toPoly (p : CPolynomial.Raw R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Alternative definition of `toPoly` using `Finsupp`; currently unused. -/
noncomputable def Raw.toPoly' (p : CPolynomial.Raw R) : Polynomial R :=
  Polynomial.ofFinsupp (Finsupp.onFinset (Finset.range p.size) p.coeff (by
    intro n hn
    rw [Finset.mem_range]
    by_contra! h
    have h' : p.coeff n = 0 := by simp [h]
    contradiction
  ))

/-- Convert a canonical polynomial to a (mathlib) `Polynomial`. -/
noncomputable def toPoly (p : CPolynomial R) : Polynomial R := p.val.toPoly

namespace Raw

alias ofPoly := Polynomial.toImpl

/-- Evaluation is preserved by `toPoly`. -/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomial.Raw Q) : p.toPoly.eval x = p.eval x := by
  unfold Raw.toPoly Raw.eval eval₂
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp

/-- The coefficients of `p.toPoly` match those of `p`. -/
lemma coeff_toPoly {p : CPolynomial.Raw Q} {n : ℕ} : p.toPoly.coeff n = p.coeff n := by
  unfold Raw.toPoly Raw.eval₂

  let f := fun (acc: Q[X]) ((a,i): Q × ℕ) ↦ acc + Polynomial.C a * Polynomial.X ^ i
  change (Array.foldl f 0 p.zipIdx).coeff n = p.coeff n

  -- we slightly weaken the goal, to use `Array.foldl_induction`
  let motive (size: ℕ) (acc: Q[X]) := acc.coeff n = if (n < size) then p.coeff n else 0

  have zipIdx_size : p.zipIdx.size = p.size := by simp [Array.zipIdx]

  suffices h : motive p.zipIdx.size (Array.foldl f 0 p.zipIdx) by
    rw [h, ite_eq_left_iff, zipIdx_size]
    intro hn
    replace hn : n ≥ p.size := by linarith
    rw [Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn, Option.getD_none]

  apply Array.foldl_induction motive
  · change motive 0 0
    simp [motive]

  change ∀ (i : Fin p.zipIdx.size) acc, motive i acc → motive (i + 1) (f acc p.zipIdx[i])
  unfold motive f
  intros i acc h
  have i_lt_p : i < p.size := by linarith [i.is_lt]
  have : p.zipIdx[i] = (p[i], ↑i) := by simp [Array.getElem_zipIdx]
  rw [this, Polynomial.coeff_add, coeff_C_mul, coeff_X_pow, mul_ite, h]
  rcases (Nat.lt_trichotomy i n) with hlt | rfl | hgt
  · have h1 : ¬ (n < i) := by linarith
    have h2 : ¬ (n = i) := by linarith
    have h3 : ¬ (n < i + 1) := by linarith
    simp [h1, h2, h3]
  · simp [i_lt_p]
  · have h1 : ¬ (n = i) := by linarith
    have h2 : n < i + 1 := by linarith
    simp [hgt, h1, h2]

/-- Case analysis for `toImpl`: either the polynomial is zero or has a specific form. -/
lemma toImpl_elim (p : Q[X]) :
    (p = 0 ∧ p.toImpl = #[])
  ∨ (p ≠ 0 ∧ p.toImpl = .ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) := by
  unfold toImpl
  by_cases hbot : p.degree = ⊥
  · left
    use degree_eq_bot.mp hbot
    rw [hbot]
  right
  use degree_ne_bot.mp hbot
  have hnat : p.degree = p.natDegree := Polynomial.degree_eq_natDegree (degree_ne_bot.mp hbot)
  simp [hnat]

/-- `toImpl` is a right-inverse of `toPoly`: the round-trip from `Polynomial` is the identity.

  This shows `toPoly` is surjective and `toImpl` is injective. -/
theorem toPoly_toImpl {p : Q[X]} : p.toImpl.toPoly = p := by
  ext n
  rw [coeff_toPoly]
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨_, h⟩
  · simp [h]
  rw [h]
  by_cases h : n < p.natDegree + 1
  · simp [h]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, reduceDIte, Option.getD_none]
  replace h := Nat.lt_of_succ_le (not_lt.mp h)
  symm
  exact coeff_eq_zero_of_natDegree_lt h

/-- Trimming doesn't change the `toPoly` image. -/
@[grind =]
lemma toPoly_trim [LawfulBEq R] {p : CPolynomial.Raw R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]

/-- `toPoly` preserves addition. -/
@[grind =]
theorem toPoly_addRaw {p q : CPolynomial.Raw Q} : (addRaw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, add_coeff?]

@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  change (p.add q).toPoly = p.toPoly + q.toPoly; unfold add
  rw [toPoly_trim, toPoly_addRaw]

/-- Non-zero polynomials map to non-empty arrays. -/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]

/-- The last coefficient of `toImpl p` is the leading coefficient of `p`. -/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]

/-- `toImpl` produces canonical polynomials (no trailing zeros). -/
@[simp, grind =]
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · rw [h, Trim.canonical_empty]
  rw [Trim.canonical_iff]
  unfold Array.getLast
  intro
  rw [getLast_toImpl h_nz]
  exact Polynomial.leadingCoeff_ne_zero.mpr h_nz

end Raw

/-- On canonical polynomials, `toImpl` is a left-inverse of `toPoly`.

  This shows `toPoly` is a bijection from `CPolynomial R` to `Polynomial R`. -/
@[grind =]
lemma toImpl_toPoly_of_canonical [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p := by
  -- we will change something slightly more general: `toPoly` is injective on canonical polynomials
  suffices h_inj : ∀ q : CPolynomial R, p.toPoly = q.toPoly → p = q by
    have : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
    exact h_inj ⟨ p.toPoly.toImpl, trim_toImpl p.toPoly ⟩ this |> congrArg Subtype.val |>.symm
  intro q hpq
  apply CPolynomial.ext
  apply Trim.canonical_ext p.property q.property
  intro i
  rw [← coeff_toPoly, ← coeff_toPoly]
  exact hpq |> congrArg (fun p => p.coeff i)

/-- The round-trip from `CPolynomial.Raw` to `Polynomial` and back yields the canonical form. -/
@[simp, grind =]
theorem Raw.toImpl_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) : p.toPoly.toImpl = p.trim := by
  rw [← toPoly_trim]
  exact toImpl_toPoly_of_canonical ⟨ p.trim, Trim.trim_twice p⟩

/-- Evaluation is preserved by `toImpl`. -/
@[simp, grind =]
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- Evaluation is unchanged by trimming. -/
@[simp, grind =]
lemma Raw.eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial.Raw R) :
    p.trim.eval x = p.eval x := by
  rw [← toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end ToPoly

section RingEquiv

/-- Ring equivalence between canonical computable polynomials and Mathlib polynomials.

  This establishes that `CPolynomial R` and `Polynomial R` are isomorphic as rings.
  The equivalence is given by `toPoly` (evaluation-based conversion) and `toImpl`
  (coefficient extraction).

  **Prerequisites**: This can only be constructed after:
  1. `CPolynomial` has a `Semiring`/`CommSemiring` instance (see `Canonical.lean`)
  2. We prove that `toPoly` preserves multiplication (see `toPoly_mul` below)
  3. We prove that `toPoly` preserves addition for trimmed polynomials

  TODO: Construct this ring equivalence once prerequisites are met.
-/
@[grind =]
lemma Raw.toPoly_mul_coeff [LawfulBEq R] (p q : CPolynomial.Raw R) (i : ℕ) :
    (p * q).toPoly.coeff i = (p.toPoly * q.toPoly).coeff i := by
  rw [coeff_toPoly, mul_coeff, Polynomial.coeff_mul]; simp
  -- equality of indices
  have h_antidiagonal :
      Finset.HasAntidiagonal.antidiagonal i =
      Finset.image (fun x => (x, i - x)) (Finset.range (i + 1)) := by
    exact Finset.Nat.antidiagonal_eq_image i
  simp [h_antidiagonal ]
  -- equality of terms
  have h_coeff : ∀ x, p.toPoly.coeff x = p[x]?.getD 0 ∧ q.toPoly.coeff x = q[x]?.getD 0 := by
    intro x
    repeat rw [coeff_toPoly]
    constructor <;> simp
  grind

@[grind =]
lemma toPoly_mul_coeffC [LawfulBEq R] (p q : CPolynomial R) (i : ℕ) :
    (p.val * q.val).toPoly.coeff i = (p.val.toPoly * q.val.toPoly).coeff i := by grind

/-- Converting the product of two canonical polynomials to a mathlib `Polynomial` is the same as
  the product of their conversions: `(p * q).toPoly = p.toPoly * q.toPoly`. -/
@[grind =]
lemma toPoly_mul [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  convert Polynomial.ext (toPoly_mul_coeff p.val q.val)

/-- Converting the sum of two raw polynomials to a mathlib `Polynomial` is the same as the sum of
  their conversions: `(p + q).toPoly = p.toPoly + q.toPoly`. -/
@[grind =]
lemma toPoly_addC [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by rw [toPoly_add]

/-
Evaluating the constant polynomial `C r` yields `f r`.
-/
@[simp, grind =]
lemma eval₂_C {R : Type*} [Ring R] [BEq R] {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (r : R) :
    (Raw.C r).eval₂ f x = f r := by
  unfold CPolynomial.Raw.eval₂ Raw.C
  ring_nf
  simp [Array.zipIdx]

/-
Converting the constant polynomial `C r` to a `Polynomial` yields `Polynomial.C r`.
-/
@[simp, grind =]
-- TODO canoncial versions of these too?
lemma Raw.toPoly_C {R : Type*} [Ring R] [BEq R] (r : R) :
    (Raw.C r).toPoly = Polynomial.C r := by
  unfold Raw.toPoly
  exact eval₂_C Polynomial.C Polynomial.X r

/--
`toPoly` preserves the multiplicative identity
-/
@[simp, grind =]
lemma Raw.toPoly_one [LawfulBEq R] :
    (1 : CPolynomial.Raw R).toPoly = 1 := by
  have : (1 : CPolynomial.Raw R).toPoly = (Raw.C 1).toPoly := by rfl
  apply this.trans; clear this
  apply toPoly_C

/-- The ring equivalence sends the canonical variable `X` to `Polynomial.X`. -/
@[simp, grind =]
lemma Raw.toPoly_X [LawfulBEq R] :
    (Raw.X : CPolynomial.Raw R).toPoly = Polynomial.X := by
  unfold CPolynomial.Raw.X
  simp [Raw.toPoly, Raw.eval₂]

/--
`toPoly` preserves the additive identity
-/
@[simp, grind =]
lemma Raw.toPoly_zero [CommSemiring R] [LawfulBEq R] :
    (0 : CPolynomial.Raw R).toPoly = 0 := by simp [Raw.toPoly, Raw.eval₂]

/-- Ring equivalence between canonical computable polynomials and mathlib's `Polynomial R`.

  `CPolynomial R` (polynomials with no trailing zeros) is isomorphic as a ring to `Polynomial R`.
  The forward map is `CPolynomial.toPoly`; the inverse sends `p : Polynomial R` to
  `⟨p.toImpl, trim_toImpl p⟩` (the canonical polynomial whose underlying array is `p.toImpl`). -/
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

-- Lemmas stating that each operation on computable polynomials matches its
-- mathlib counterpart when viewed via `toPoly`, enabling transport back and forth
section ImplementationCorrectness

/-- The implementation of monomial is correct. -/
theorem monomial_toPoly [DecidableEq R] [LawfulBEq R] (n : ℕ) (c : R) :
    (monomial n c).toPoly = Polynomial.monomial n c := by
  ext i
  simp only [CPolynomial.toPoly, monomial]
  rw [Polynomial.coeff_monomial, coeff_toPoly, CPolynomial.Raw.coeff_monomial]

/-- The implementation of `C` is correct. -/
theorem C_toPoly [LawfulBEq R] (r : R) : (C r).toPoly = Polynomial.C r := by
  convert Raw.toPoly_C r
  convert Raw.toPoly_trim
  infer_instance

/-- The implementation of `X` is correct. -/
theorem X_toPoly [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).toPoly = Polynomial.X := by
  convert Raw.toPoly_X using 1
  (expose_names; infer_instance)
  infer_instance

/-- The implementation of `eval` is correct. -/
theorem eval_toPoly [LawfulBEq R] (x : R) (p : CPolynomial R) :
    eval x p = p.toPoly.eval x := by
  convert Raw.eval_toPoly_eq_eval x p.val
  · rw [ Raw.eval_toPoly_eq_eval ]; rfl
  · convert Raw.eval_toPoly_eq_eval x p.val

/-- The implementation of `eval₂` is correct. -/
theorem eval₂_toPoly {S : Type*} [Semiring S] (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂ f x p = p.toPoly.eval₂ f x := sorry

/-- The implementation of `coeff` is correct. -/
theorem coeff_toPoly [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    p.coeff i = p.toPoly.coeff i := by
  unfold toPoly coeff
  simp [Raw.coeff_toPoly]

theorem divX_toPoly [LawfulBEq R] (p : CPolynomial R) :
    (divX p).toPoly = p.toPoly.divX := by
  ext n
  -- compare coefficients after converting to mathlib polynomials
  simp only [CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly, CPolynomial.coeff,
    CompPoly.CPolynomial.coeff_divX, Polynomial.coeff_divX]


/-- The implementation of `support` is correct. -/
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

/-- The implementation of `degree` is correct. -/
theorem degree_toPoly [LawfulBEq R] (p : CPolynomial R) :
    p.degree = p.toPoly.degree := by
  -- Since `p` is a canonical polynomial, its degree is equal to the degree of
  -- its polynomial representation.
  have h_deg_eq : p.val.toPoly.degree = p.val.degree := by
    unfold CPolynomial.Raw.degree at *
    rcases h : ( p : CompPoly.CPolynomial.Raw R ).lastNonzero with ( _ | ⟨ k, hk ⟩ )
      <;> simp_all +decide [ Polynomial.degree_eq_bot ]
    · have := p.prop
      unfold CompPoly.CPolynomial.Raw.trim at this; aesop
    · have := CPolynomial.Raw.Trim.lastNonzero_spec h
      rw [ Polynomial.degree_eq_of_le_of_coeff_ne_zero ]
      · rw [ Polynomial.degree_le_iff_coeff_zero ]
        intro m hm; by_cases hm' : m < p.val.size
          <;> simp_all +decide [ CPolynomial.Raw.coeff_toPoly ]
      · rw [ CompPoly.CPolynomial.Raw.coeff_toPoly ]; aesop
  exact h_deg_eq.symm

/-- The implementation of `natDegree` is correct. -/
theorem natDegree_toPoly [LawfulBEq R] (p : CPolynomial R) :
    p.natDegree = p.toPoly.natDegree := by
  -- Since the degree of p is equal to the degree of p.toPoly, and the natural
  -- degree is defined as the degree, we can conclude p.natDegree = p.toPoly.natDegree.
  have h_deg_eq : p.degree = p.toPoly.degree := by
    exact degree_toPoly p
  -- Since the natural degree is the degree's natural number version, and
  -- p.degree = p.toPoly.degree, their natural degrees must also be equal.
  have h_natDegree_eq : p.natDegree = p.degree.unbotD 0 := by
    unfold CPolynomial.natDegree CPolynomial.degree
    unfold CPolynomial.Raw.natDegree CPolynomial.Raw.degree
    cases p.val.lastNonzero <;> rfl
  aesop

/-- The implementation of `leadingCoeff` is correct. -/
theorem leadingCoeff_toPoly [LawfulBEq R] (p : CPolynomial R) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  by_contra h_contra
  -- Apply the contradiction assumption to obtain the equality of leading coefficients.
  apply h_contra
  obtain ⟨q, hq⟩ : ∃ q : Polynomial R, p = ⟨q.toImpl, trim_toImpl q⟩ := by
    use p.toPoly
    generalize_proofs at *
    convert Subtype.ext ?_
    exact Eq.symm (toImpl_toPoly_of_canonical p)
  -- Since `q.toImpl` is the array of coefficients of `q`, the leading
  -- coefficient of `q.toImpl` is the same as the leading coefficient of `q`.
  have h_leading_coeff_eq : q.toImpl.getLast (by
  by_cases hq_zero : q = 0 <;> simp_all +decide [ Polynomial.toImpl ]
  · -- Since the polynomial is zero, its leading coefficient is zero.
    simp [CompPoly.CPolynomial.leadingCoeff, CompPoly.CPolynomial.toPoly] at h_contra
    simp +decide [ CompPoly.CPolynomial.Raw.leadingCoeff, CompPoly.CPolynomial.Raw.toPoly ]
      at h_contra
    exact h_contra (by unfold CompPoly.CPolynomial.Raw.trim; aesop)
  · cases h : q.degree <;> simp_all +decide [ Polynomial.degree_eq_natDegree hq_zero ])
      = q.leadingCoeff := by
    all_goals generalize_proofs at *
    convert Raw.getLast_toImpl _
    rintro rfl; simp_all +decide [ Polynomial.toImpl ]
  generalize_proofs at *
  convert h_leading_coeff_eq using 1
  · unfold CPolynomial.leadingCoeff
    unfold CPolynomial.Raw.leadingCoeff
    unfold Array.getLastD; aesop
  · rw [ ← h_leading_coeff_eq, hq ]
    rw [ show (CompPoly.CPolynomial.toPoly ⟨q.toImpl, by assumption⟩ : Polynomial R) = q
        from ?_ ]
    · exact h_leading_coeff_eq.symm
    · apply Raw.toPoly_toImpl

/-- The implementation of `erase` is correct. -/
theorem erase_toPoly [LawfulBEq R] [DecidableEq R] (n : ℕ) (p : CPolynomial R) :
    (erase n p).toPoly = p.toPoly.erase n := by
  have h_erase_def : (CompPoly.CPolynomial.erase n p).toPoly
      = p.toPoly - Polynomial.monomial n (p.val.coeff n) := by
    have h_erase_toPoly : ∀ (p q : CompPoly.CPolynomial.Raw R),
        (p - q).toPoly = p.toPoly - q.toPoly := by
      intros p q;
      have h_erase_toPoly : ∀ (p q : CompPoly.CPolynomial.Raw R),
          (p + -q).toPoly = p.toPoly + (-q).toPoly := by
        exact fun p q => toPoly_addC p (-q)
      convert h_erase_toPoly p q using 1
      simp +decide [ Raw.toPoly ]
      rw [ show ( -q : CompPoly.CPolynomial.Raw R ) = q.map ( fun x => -x ) from ?_ ]
      · simp +decide [ Raw.eval₂ ]
        induction' q using Array.recOn with q ih; simp +decide [ *, Array.zipIdx ]
        induction' q using List.reverseRecOn with q ih <;>
          simp +decide [ *, List.mapIdx_append ]
        grind
      · rfl
    convert h_erase_toPoly _ _
    convert monomial_toPoly n ( p.val.coeff n ) |> Eq.symm
  convert h_erase_def using 1
  ext m; simp +decide [ Polynomial.coeff_monomial ]
  by_cases h : n = m <;> simp +decide [ h ]
  · rw [ eq_comm, sub_eq_zero ]
    convert Raw.coeff_toPoly using 1
    exact Eq.symm Array.getD_eq_getD_getElem?
  · rw [ Polynomial.coeff_erase ]; aesop

/-- The implementation of `C r * X^n` agrees with `Polynomial.monomial n r`. -/
theorem C_mul_X_pow_toPoly [LawfulBEq R] [DecidableEq R] [Nontrivial R] (r : R) (n : ℕ) :
    (C r * X ^ n).toPoly = Polynomial.monomial n r := by
  convert C_mul_X_pow_eq_monomial r n using 1
  constructor <;> intro h
  · exact C_mul_X_pow_eq_monomial r n
  · convert monomial_toPoly n r

end ImplementationCorrectness

end CPolynomial

end CompPoly
