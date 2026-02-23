/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/

import CompPoly.Bivariate.Basic
import CompPoly.Univariate.ToPoly
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Equivalence with Mathlib Bivariate Polynomials

This file establishes the conversion from `CBivariate R` to Mathlib's `R[X][Y]`
(`Polynomial (Polynomial R)`).

The main definition is:
- `toPoly`: converts `CBivariate R` to `R[X][Y]`

Proofs that `toPoly` preserves evaluation, coefficients, degrees, etc. (and that it
forms an isomorphism with an inverse `ofPoly`) will be added as the implementation
is completed. The target interface matches ArkLib's `Polynomial.Bivariate` and
Mathlib's `Polynomial.Bivariate`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace CompPoly

namespace CBivariate

/-- Convert `CBivariate R` to Mathlib's bivariate polynomial `R[X][Y]`.

  Maps each Y-coefficient through `CPolynomial.toPoly`, then builds
  `Polynomial (Polynomial R)` as the sum of monomials.
  -/
noncomputable def toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p : CBivariate R) : R[X][Y] :=
  (CPolynomial.support p).sum (fun j =>
    monomial j (CPolynomial.toPoly (p.val.coeff j)))

/-- Convert Mathlib's `R[X][Y]` to `CBivariate R` (inverse of `toPoly`).

  Extracts each Y-coefficient via `p.coeff`, converts to `CPolynomial R` via
  `toImpl` and trimming, then builds the canonical bivariate sum.
  -/
def ofPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (p : R[X][Y]) : CBivariate R :=
  (p.support).sum (fun j =>
    let cj := p.coeff j
    CPolynomial.monomial j ⟨cj.toImpl, CPolynomial.Raw.trim_toImpl cj⟩)

/-
Helper lemma: `toPoly` maps zero to zero.
-/
lemma toPoly_zero {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] :
    toPoly (0 : CBivariate R) = 0 := by
      -- The sum over the empty set is zero.
      simp [CompPoly.CBivariate.toPoly]
      rw [ Finset.sum_eq_zero ]
      aesop

/-
Helper lemma: `toPoly` preserves addition.
Proof idea:
1. `toPoly` is a sum of monomials.
2. `coeff (p + q) j = coeff p j + coeff q j`.
3. `CPolynomial.toPoly` is additive.
4. `monomial` is additive.
5. Use `Finset.sum_add_distrib` and `Finset.sum_subset` to handle supports.
-/
lemma toPoly_add {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p q : CBivariate R) : toPoly (p + q) = toPoly p + toPoly q := by
      have h_linear : ∀ (p q : CPolynomial R), (p + q).toPoly = p.toPoly + q.toPoly := by
        intros p q
        exact (by
        apply CPolynomial.Raw.toPoly_add)
      -- Apply the linearity of toPoly to the coefficients of p and q.
      have h_coeff : ∀ (j : ℕ), (p + q).val.coeff j = p.val.coeff j + q.val.coeff j := by
        apply CPolynomial.coeff_add
      unfold CBivariate.toPoly
      rw [ Finset.sum_subset
        ( show CompPoly.CPolynomial.support (p + q) ⊆
            CompPoly.CPolynomial.support p ∪ CompPoly.CPolynomial.support q from ?_ ) ]
      · simp +decide [ Finset.sum_add_distrib, h_coeff, h_linear ]
        rw [ ← Finset.sum_subset (Finset.subset_union_left),
            ← Finset.sum_subset (Finset.subset_union_right) ]
        · simp +contextual [ CPolynomial.support ]
          intro x hx hq
          cases hx <;> simp_all +decide
          · by_cases hx : x < Array.size q.val <;> simp_all +decide
            · exact toFinsupp_eq_zero.mp rfl
            · exact toFinsupp_eq_zero.mp rfl
          · grind
        · simp +contextual [ CPolynomial.mem_support_iff ]
          aesop
      · simp +contextual [ h_coeff ]
        intro j hj₁ hj₂
        contrapose! hj₂
        simp_all +decide
        -- Since $j$ is in the support of $p$ or $q$, the coefficient of $j$ in $p + q$ is non-zero.
        have h_coeff_nonzero : (p + q).val.coeff j ≠ 0 := by
          intro h
          simp_all +decide [ Polynomial.ext_iff ]
          obtain ⟨ x, hx ⟩ := hj₂
          specialize h_coeff j
          simp_all +decide
          exact hx ( by rw [ ← h_linear ]; aesop )
        exact (CPolynomial.mem_support_iff (p + q) j).mpr h_coeff_nonzero
      · intro j hj
        simp_all +decide [ CompPoly.CPolynomial.support ]
        grind

/-
Helper lemma: `toPoly` maps a monomial `c * Y^n` to `c.toPoly * Y^n`.
-/
lemma toPoly_monomial {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (n : ℕ) (c : CPolynomial R) :
    toPoly (CPolynomial.monomial n c) = monomial n (c.toPoly) := by
      unfold CPolynomial.monomial
      unfold CBivariate.toPoly
      unfold CPolynomial.support
      rw [ Finset.sum_eq_single n ] <;>
        simp +decide [ CompPoly.CPolynomial.Raw.monomial ]
      · split_ifs <;> simp_all +decide [ Array.push ]
      · grind
      · split_ifs <;> simp_all +decide [ Array.push ]
        exact toFinsupp_eq_zero.mp rfl

/-
Helper lemma: `ofPoly` maps zero to zero.
-/
lemma ofPoly_zero {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    ofPoly (0 : R[X][Y]) = 0 := by
      unfold CompPoly.CBivariate.ofPoly
      simp +decide [ Polynomial.support ]

/-
Helper lemma: `ofPoly` maps a monomial `c * Y^n` to `CPolynomial.monomial n ⟨c.toImpl, ...⟩`.
-/
lemma ofPoly_monomial {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (n : ℕ) (c : R[X]) :
    ofPoly (monomial n c) =
    CPolynomial.monomial n ⟨c.toImpl, CPolynomial.Raw.trim_toImpl c⟩ := by
      unfold CompPoly.CBivariate.ofPoly
      simp +decide
      rw [ Finset.sum_eq_single n ] <;> simp +decide [ Polynomial.coeff_monomial ]
      aesop

/-
Helper lemma: `toImpl` preserves addition (where addition on `Raw` includes trimming).
Note: `CPolynomial.Raw.add p q` is defined as `(p.addRaw q).trim`.
`toImpl` produces a trimmed array representing the polynomial.
So this states that adding the array representations and trimming yields the array
representation of the sum.
-/
lemma toImpl_add {R : Type*} [BEq R] [LawfulBEq R] [Ring R] (p q : R[X]) :
    p.toImpl + q.toImpl = (p + q).toImpl := by
      have h_add : (p.toImpl + q.toImpl).toPoly = (p + q).toImpl.toPoly := by
        have h_add : (p.toImpl + q.toImpl).toPoly = p.toImpl.toPoly + q.toImpl.toPoly := by
          convert CPolynomial.Raw.toPoly_add p.toImpl q.toImpl using 1
        convert h_add using 1
        rw [ CPolynomial.Raw.toPoly_toImpl, CPolynomial.Raw.toPoly_toImpl,
          CPolynomial.Raw.toPoly_toImpl ]
      have h_add_trim : ∀ p q : CPolynomial.Raw R,
          p.toPoly = q.toPoly → p.trim = q.trim := by
        intros p q h_eq
        have h_coeff : ∀ n, p.coeff n = q.coeff n := by
          intro n; exact (by
          convert congr_arg (fun f => f.coeff n) h_eq using 1 <;>
            simp +decide [ CPolynomial.Raw.coeff_toPoly ])
        exact CPolynomial.Raw.Trim.eq_of_equiv h_coeff
      convert h_add_trim _ _ h_add using 1
      · have h_add_trim : ∀ p q : CPolynomial.Raw R,
            (p + q).toPoly = p.toPoly + q.toPoly → (p + q).trim = p.trim + q.trim := by
          intros p q h_add
          apply ‹∀ (p q : CompPoly.CPolynomial.Raw R),
              p.toPoly = q.toPoly → p.trim = q.trim›
          grind
        grind
      · exact Eq.symm (CPolynomial.Raw.trim_toImpl (p + q))

/-
Helper lemma: `CPolynomial.monomial` is additive.
Proof: Use extensionality of `CPolynomial` and that coefficients are additive.
-/
lemma CPolynomial_monomial_add {S : Type*} [Ring S] [BEq S] [LawfulBEq S] [DecidableEq S]
    (n : ℕ) (a b : S) :
    CPolynomial.monomial n (a + b) = CPolynomial.monomial n a + CPolynomial.monomial n b := by
      -- By definition of monomial, we know that `coeff (monomial n c) i = if i = n then c else 0`.
      have h_monomial_coeff : ∀ n : ℕ, ∀ c : S, ∀ i,
          CPolynomial.Raw.coeff (CPolynomial.Raw.monomial n c) i = if i = n then c else 0 := by
        unfold CompPoly.CPolynomial.Raw.monomial
        intro n c i
        split_ifs <;> simp_all +decide [ CompPoly.CPolynomial.Raw.coeff ]
        · simp +decide [ Array.push ]
        · grind
      -- So we can apply this to both sides of the equation.
      have h_monomial_coeff_eq : ∀ i,
        CPolynomial.Raw.coeff (CPolynomial.Raw.monomial n (a + b)) i =
        CPolynomial.Raw.coeff (CPolynomial.Raw.monomial n a + CPolynomial.Raw.monomial n b) i := by
          -- Coefficient of the sum is the sum of the coefficients.
          have h_coeff_add : ∀ (p q : CPolynomial.Raw S) (i : ℕ),
              (p + q).coeff i = p.coeff i + q.coeff i := by
            exact fun p q i => CPolynomial.Raw.add_coeff_trimmed p q i
          aesop
      exact CPolynomial.eq_iff_coeff.mpr h_monomial_coeff_eq

lemma ofPoly_add {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p q : R[X][Y]) : ofPoly (p + q) = ofPoly p + ofPoly q := by
      -- Sum of two polynomials is sum of their coefficients; convert back using `ofPoly`.
      have h_ofPoly_add_p : ∀ (p q : Polynomial (Polynomial R)),
          ofPoly (p + q) = ofPoly p + ofPoly q := by
        unfold CompPoly.CBivariate.ofPoly
        intro p q
        rw [ Finset.sum_subset
          ( show (p + q |> Polynomial.support) ⊆ p.support ∪ q.support from fun x hx => ?_ ) ]
        · simp +zetaDelta at *
          rw [ Finset.sum_subset
              (show p.support ⊆ p.support ∪ q.support from Finset.subset_union_left),
            Finset.sum_subset
              (show q.support ⊆ p.support ∪ q.support from Finset.subset_union_right) ]
          · rw [ ← Finset.sum_add_distrib ]
            refine' Finset.sum_congr rfl fun x hx => _
            rw [ ← CPolynomial_monomial_add ]
            congr
            exact Eq.symm (toImpl_add (p.coeff x) (q.coeff x))
          · aesop
          · aesop
        · aesop
        · contrapose! hx
          aesop
      exact h_ofPoly_add_p p q

theorem ofPoly_coeff {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : R[X][Y]) (n : ℕ) : (CompPoly.CPolynomial.coeff (ofPoly p) n).toPoly = p.coeff n := by
      -- By definition of `coeff`, we can express it as a sum over the support of `p`.
      have h_coeff_sum : CompPoly.CPolynomial.coeff (CompPoly.CBivariate.ofPoly p) n =
          Finset.sum (Polynomial.support p) (fun j =>
            CompPoly.CPolynomial.coeff
              (CompPoly.CPolynomial.monomial j
                ⟨Polynomial.toImpl (Polynomial.coeff p j),
                  CompPoly.CPolynomial.Raw.trim_toImpl (Polynomial.coeff p j)⟩) n) := by
        unfold CompPoly.CBivariate.ofPoly
        induction' p.support using Finset.induction with j s hj ih
        · exact CPolynomial.eq_iff_coeff.mpr (congrFun rfl)
        · rw [ Finset.sum_insert hj, CompPoly.CPolynomial.coeff_add, ih, Finset.sum_insert hj ]
      rw [ h_coeff_sum, Finset.sum_eq_single n ]
      · rw [ CompPoly.CPolynomial.coeff_monomial ]
        simp +decide [ CompPoly.CPolynomial.toPoly ]
        exact CPolynomial.Raw.toPoly_toImpl
      · simp +decide [ CompPoly.CPolynomial.coeff, CompPoly.CPolynomial.monomial ]
        unfold CompPoly.CPolynomial.Raw.monomial
        grind
      · aesop

theorem toPoly_coeff {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p : CBivariate R) (n : ℕ) : (toPoly p).coeff n = (CompPoly.CPolynomial.coeff p n).toPoly := by
      rw [ CBivariate.toPoly, Polynomial.finset_sum_coeff ]
      rw [ Finset.sum_eq_single n ] <;> simp +contextual [ Polynomial.coeff_monomial ]
      simp_all +decide [ CompPoly.CPolynomial.mem_support_iff ]
      aesop

/-- Round-trip from Mathlib: converting a polynomial to `CBivariate` and back is the identity. -/
theorem ofPoly_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : R[X][Y]) : toPoly (ofPoly p) = p := by
      induction p using Polynomial.induction_on'
      · rw [ ofPoly_add, toPoly_add,
          ‹(CompPoly.CBivariate.ofPoly _).toPoly = _›, ‹(CompPoly.CBivariate.ofPoly _).toPoly = _› ]
      · rename_i n c
        simp +decide [ ofPoly_monomial, toPoly_monomial ]
        exact congr_arg _ ( CompPoly.CPolynomial.Raw.toPoly_toImpl )

/-- Round-trip from `CBivariate`: converting to Mathlib and back is the identity. -/
theorem toPoly_ofPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : CBivariate R) : ofPoly (toPoly p) = p := by
      apply CompPoly.CPolynomial.eq_iff_coeff.mpr
      intro i
      -- Since `toPoly` is injective on canonical polynomials, coefficients equal ⇒ poly equal.
      have h_inj : Function.Injective (fun p : CompPoly.CPolynomial R => p.toPoly) := by
        intro p q h_eq
        have := CompPoly.CPolynomial.toImpl_toPoly_of_canonical p
        have := CompPoly.CPolynomial.toImpl_toPoly_of_canonical q
        aesop
      apply h_inj
      convert ofPoly_coeff p.toPoly i using 1
      exact Eq.symm (toPoly_coeff p i)

/-
`toPoly` is equivalent to converting the outer polynomial to a `Polynomial` and then
mapping the inner coefficients using `CPolynomial.toPoly`.
-/
theorem toPoly_eq_map {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p : CBivariate R) :
    toPoly p = (CPolynomial.toPoly p).map (CPolynomial.ringEquiv (R := R)) := by
      convert Polynomial.ext _
      unfold CBivariate.toPoly
      simp +decide [ Polynomial.coeff_monomial ]
      intro n
      split_ifs <;> simp_all +decide [ CompPoly.CPolynomial.toPoly ]
      · erw [ CompPoly.CPolynomial.Raw.coeff_toPoly ]
        unfold CompPoly.CPolynomial.ringEquiv
        aesop
      · rw [ CPolynomial.Raw.coeff_toPoly ]
        simp +decide [ CPolynomial.support, * ] at *
        by_cases h : n < Array.size p.val <;> aesop

/-
`toPoly` preserves addition.
-/
theorem toPoly_add₂ {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p q : CBivariate R) :
    toPoly (p + q) = toPoly p + toPoly q := by
      rw [ CBivariate.toPoly_eq_map, CBivariate.toPoly_eq_map, CBivariate.toPoly_eq_map ]
      rw [ ← Polynomial.map_add ]
      congr
      exact CPolynomial.Raw.toPoly_add _ _

/-
`toPoly` preserves multiplication.
-/
theorem toPoly_mul {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p q : CBivariate R) :
    toPoly (p * q) = toPoly p * toPoly q := by
      have h_mul : (p * q).toPoly =
          (CPolynomial.toPoly (p * q)).map (CPolynomial.ringEquiv (R := R)) := by
        exact toPoly_eq_map (p * q)
      rw [ h_mul, CPolynomial.toPoly_mul ]
      rw [ Polynomial.map_mul, ← toPoly_eq_map, ← toPoly_eq_map ]

/-- Ring equivalence between `CBivariate R` and Mathlib's `R[X][Y]`. -/
noncomputable def ringEquiv
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    CBivariate R ≃+* R[X][Y] where
  toFun := toPoly
  invFun := ofPoly
  left_inv := toPoly_ofPoly
  right_inv := ofPoly_toPoly
  map_mul' := by apply toPoly_mul
  map_add' := by exact fun x y => toPoly_add₂ x y

/-
Evaluation of a canonical polynomial is equal to the sum over its support of
coefficients multiplied by powers of the variable.
-/
theorem CompPoly.CPolynomial.eval_eq_sum_support
    {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] (p : CompPoly.CPolynomial R) (x : R) :
    p.eval x = p.support.sum (fun i => p.coeff i * x ^ i) := by
      -- By definition of polynomial evaluation, we can expand both sides.
      have h_eval_def : p.val.eval x =
          (p.val.zipIdx.toList.map (fun ⟨a, i⟩ => a * x ^ i)).sum := by
        unfold CompPoly.CPolynomial.Raw.eval
        unfold CompPoly.CPolynomial.Raw.eval₂
        simp +decide
        induction p.val
        simp +decide [ * ]
        induction' ‹List R› using List.reverseRecOn with a l ih <;>
          simp +decide [ *, List.zipIdx_append ]
      have h_sum_range : (p.val.zipIdx.toList.map (fun ⟨a, i⟩ => a * x ^ i)).sum =
          (Finset.range p.val.size).sum (fun i => p.val.coeff i * x ^ i) := by
        convert CompPoly.CPolynomial.Raw.sum_zipIdx_eq_sum_range p.val (fun a i => a * x ^ i)
          using 1
      convert h_eval_def.trans h_sum_range using 1
      refine' Finset.sum_subset _ _ <;> intro i hi <;>
        simp_all +decide [ CPolynomial.Raw.coeff ]
      · exact Finset.mem_range.mp (Finset.mem_filter.mp hi |>.1)
      · unfold CPolynomial.support
        aesop

/-
Evaluation (via a ring hom) of a canonical polynomial is the sum over its support
of mapped coefficients multiplied by powers of the variable.
-/
theorem CompPoly.CPolynomial.eval₂_eq_sum_support
    {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] {S : Type*} [Semiring S]
    (f : R →+* S) (p : CompPoly.CPolynomial R) (x : S) :
    p.eval₂ f x = p.support.sum (fun i => f (p.coeff i) * x ^ i) := by
      unfold CompPoly.CPolynomial.support
      convert CompPoly.CPolynomial.Raw.sum_zipIdx_eq_sum_range p.val _ using 1
      rotate_right
      use fun a i => if a != 0 then f a * x ^ i else 0
      all_goals try infer_instance
      · unfold CompPoly.CPolynomial.eval₂
        unfold CompPoly.CPolynomial.Raw.eval₂
        induction' ( Array.zipIdx p.val ) with a ha ih
        simp +decide [ * ]
        induction a using List.reverseRecOn <;> aesop
      · rw [ Finset.sum_filter ]

/-- `toPoly` preserves full evaluation: `evalEval x y f = (toPoly f).evalEval x y`. -/
theorem evalEval_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (x y : R) (f : CBivariate R) :
    @CompPoly.CBivariate.evalEval R _ _ _ _ x y f = (toPoly f).evalEval x y := by
      unfold CompPoly.CBivariate.evalEval Polynomial.evalEval
      -- `toPoly f` has coefficients `f.val.coeff i`.
      have h_toPoly : (toPoly f).eval (Polynomial.C y) = (f.val.eval (CPolynomial.C y)).toPoly := by
        unfold CompPoly.CBivariate.toPoly
        simp +decide [ Polynomial.eval_finset_sum, CompPoly.CPolynomial.Raw.eval ]
        unfold CompPoly.CPolynomial.Raw.eval₂
        simp +decide [ Polynomial.eval₂_finset_sum ]
        -- Rewrite the right-hand side to match the left-hand side.
        have h_foldl : ∀ (arr : Array (CPolynomial R)) (y : R),
            (Array.foldl (fun (acc : CPolynomial R) (x : CPolynomial R × ℕ) =>
              acc + x.1 * CPolynomial.C y ^ x.2) 0 (Array.zipIdx arr) 0 arr.size).toPoly =
            ∑ i ∈ Finset.range arr.size, (arr[i]?.getD 0).toPoly * (Polynomial.C y) ^ i := by
          intro arr y
          induction' arr using Array.recOn with arr ih
          induction' arr using List.reverseRecOn with arr ih
          · rfl
          · simp_all +decide [ Finset.sum_range_succ, Array.zipIdx ]
            rw [ Finset.sum_congr rfl fun i hi => by rw [ List.getElem?_append ] ]
            rw [ Finset.sum_congr rfl fun i hi => by rw [ if_pos (Finset.mem_range.mp hi) ] ]
            convert congr_arg₂ ( · + · ) ‹_› rfl using 1
            convert CPolynomial.Raw.toPoly_add _ _ using 1
            · congr! 1
              -- `toPoly (ih * C y ^ arr.length) = toPoly ih * toPoly (C y ^ arr.length)`.
              have h_toPoly_mul : ∀ (p q : CPolynomial R),
                  (p * q).toPoly = p.toPoly * q.toPoly := by grind
              convert h_toPoly_mul ih (CPolynomial.C y ^ arr.length) |> Eq.symm using 1
              congr! 1
              induction' arr.length with n ih <;> simp_all +decide [ pow_succ ]
              · exact Eq.symm ( CPolynomial.Raw.toPoly_one )
              · congr! 1
                exact Eq.symm (CPolynomial.C_toPoly y)
            · infer_instance
        rw [ h_foldl, Finset.sum_subset ]
        · exact fun i hi => Finset.mem_range.mpr
            (Nat.lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hi |>.1)) (by simp))
        · simp +contextual [ CompPoly.CPolynomial.support ]
          simp +decide [ CompPoly.CPolynomial.toPoly, CompPoly.CPolynomial.Raw.toPoly ]
          unfold CompPoly.CPolynomial.Raw.eval₂
          erw [ Array.foldl_empty ]
          simp
      -- `toPoly (f.val.eval (C y))` equals the polynomial with coefficients `f.val.coeff i`.
      rw [h_toPoly]
      exact CPolynomial.eval_toPoly x (CPolynomial.Raw.eval (CPolynomial.C y) ↑f)

/-- `toPoly` preserves coefficients: coefficient of `X^i Y^j` matches. -/
theorem coeff_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) (i j : ℕ) :
    ((toPoly f).coeff j).coeff i = @CompPoly.CBivariate.coeff R _ _ _ _ f i j := by
      convert CPolynomial.Raw.coeff_toPoly using 1
      rw [ CBivariate.toPoly ]
      simp +decide [ Polynomial.coeff_monomial ]
      split_ifs <;> simp_all +decide [ CPolynomial.support ]
      · congr
      · by_cases h : j < ( f.val.size : ℕ ) <;> aesop

/-
The coefficient of `Y^j` in `toPoly f` is the converted coefficient of `Y^j` in `f`.
-/
theorem coeff_toPoly_outer {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) (j : ℕ) :
    (toPoly f).coeff j = CPolynomial.toPoly (f.val.coeff j) := by
      simp [CompPoly.CBivariate.toPoly]
      rw [ Finset.sum_eq_single j ] <;> simp +decide [ Polynomial.coeff_monomial ]
      · aesop
      · intro hj
        rw [ CompPoly.CPolynomial.support ] at hj
        by_cases hj' : j < f.val.size <;> aesop

/-
`toPoly` maps a canonical polynomial to 0 iff the polynomial is 0.
-/
theorem CompPoly.CPolynomial.toPoly_eq_zero_iff
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] (p : CPolynomial R) :
    p.toPoly = 0 ↔ p = 0 := by
      constructor
      · intro hp
        have h_trivial : p.toPoly.toImpl = p := by
          exact CPolynomial.toImpl_toPoly_of_canonical p
        rw [ eq_comm ] at h_trivial
        aesop
      · aesop

/-
The support of `toPoly f` is the same as the Y-support of `f`.
-/
theorem support_toPoly_outer {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) : (toPoly f).support = f.supportY := by
      ext x
      simp +decide [ CompPoly.CPolynomial.mem_support_iff, CompPoly.CBivariate.supportY ]
      rw [ CompPoly.CBivariate.toPoly ]
      simp +decide [ Polynomial.coeff_monomial ]
      rw [ CPolynomial.mem_support_iff, CompPoly.CPolynomial.toPoly_eq_zero_iff ]
      aesop

/-
The natural degree of a canonical polynomial is the maximum element of its support.
-/
theorem CompPoly.CPolynomial.natDegree_eq_support_sup
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R] (p : CPolynomial R) :
    p.natDegree = p.support.sup (fun n => n) := by
      have := p.2;
      unfold CPolynomial.Raw.trim at this;
      cases h' : (p : CPolynomial.Raw R).lastNonzero <;>
        simp_all +decide [ Array.ext_iff ]
      · -- If the size of the array is zero, then the polynomial is zero.
        have h_zero : p.val = #[] := by
          exact Array.eq_empty_of_size_eq_zero this.symm
        cases p
        simp_all +decide [ CPolynomial.natDegree ]
        unfold CPolynomial.Raw.natDegree CPolynomial.support
        simp +decide
        grind
      · rename_i k
        have h_deg : ∀ n, n ∈ p.support → n ≤ k := by
          intro n hn
          have h_coeff : p.val.coeff n ≠ 0 := by
            exact (CPolynomial.mem_support_iff p n).mp hn
          have h_last : ∀ j, (hj : j < p.val.size) → j > k → p.val[j] = 0 := by
            exact fun j hj₁ hj₂ => by linarith;
          have h_le : n ≤ k := by
            grind
          exact h_le
        have h_deg : k.val ∈ p.support := by
          exact CPolynomial.degree_eq_support_max_aux_mem_support p h'
        rw [ show p.natDegree = k from ?_ ]
        · exact le_antisymm ( Finset.le_sup ( f := fun n => n ) h_deg ) ( Finset.sup_le ‹_› )
        · rw [ CPolynomial.natDegree ]
          unfold CPolynomial.Raw.natDegree
          aesop

/-- `toPoly` preserves Y-degree. -/
theorem natDegreeY_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) : (toPoly f).natDegree = f.natDegreeY := by
      unfold CompPoly.CBivariate.natDegreeY;
      -- The degree of the polynomial is the supremum of the exponents in its support.
      have h_deg : ∀ p : Polynomial (Polynomial R), p.natDegree = p.support.sup id := by
        intro p
        by_cases hp : p = 0;
        · simp +decide [ hp ];
        · refine' le_antisymm _ _;
          · exact Finset.le_sup ( f := id ) ( Polynomial.natDegree_mem_support_of_nonzero hp );
          · exact Finset.sup_le fun i hi => Polynomial.le_natDegree_of_mem_supp _ hi;
      rw [ h_deg, support_toPoly_outer ];
      -- Apply the fact that the degree of a polynomial is equal to the supremum of its support.
      apply Eq.symm; exact (CompPoly.CPolynomial.natDegree_eq_support_sup f)

/- `toPoly` preserves X-degree (max over Y-coefficients of their degree in X). -/
theorem CompPoly.CBivariate.coeff_toPoly_Y {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CompPoly.CBivariate R) (j : ℕ) :
    (CompPoly.CBivariate.toPoly f).coeff j = CompPoly.CPolynomial.toPoly (f.val.coeff j) := by
      erw [ Polynomial.finset_sum_coeff ];
      rw [ Finset.sum_eq_single j ] <;> simp +contextual [ Polynomial.coeff_monomial ]
      intro hj;
      rw [ CompPoly.CPolynomial.support ] at hj;
      by_cases hj' : j < f.val.size <;> simp_all +decide
      · exact (CPolynomial.toPoly_eq_zero_iff 0).mpr rfl
      · exact (CPolynomial.toPoly_eq_zero_iff 0).mpr rfl

/-- `toPoly` preserves X-degree (max over Y-coefficients of their degree in X). -/
theorem degreeX_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) :
    (toPoly f).support.sup (fun j => ((toPoly f).coeff j).natDegree) = f.degreeX := by
      convert ( Finset.sup_congr ?_ ?_ );
      · ext; simp +decide [ CompPoly.CBivariate.coeff_toPoly_Y ];
        rw [ CompPoly.CPolynomial.support ];
        by_cases h : ‹_› < f.val.size <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ];
        · -- Since `toPoly` is injective, if `toPoly (f.coeff j) = 0`, then `f.coeff j = 0`.
          have h_inj : ∀ (p : CompPoly.CPolynomial R), p.toPoly = 0 ↔ p = 0 := by
            intro p; exact ⟨fun hp => by
              apply Subtype.ext;
              apply_fun (fun p => p.toImpl) at hp;
              convert hp using 1;
              exact Eq.symm (CPolynomial.toImpl_toPoly_of_canonical p),
              fun hp => by aesop⟩
          aesop
        · exact (CompPoly.CPolynomial.toPoly_eq_zero_iff 0).mpr rfl
      · intro j hj
        rw [ CompPoly.CBivariate.coeff_toPoly_Y ]
        exact Eq.symm (CPolynomial.natDegree_toPoly (f.val.coeff j))

end CBivariate

-- TODO correctness lemmas for operations and API functions

end CompPoly
