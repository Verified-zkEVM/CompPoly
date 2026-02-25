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

Main definitions:
- `toPoly`: converts `CBivariate R` to `R[X][Y]`
- `ofPoly`: converts `R[X][Y]` back to `CBivariate R`

Main results:
- round-trip identities: `ofPoly_toPoly`, `toPoly_ofPoly`
- ring equivalence: `ringEquiv`
- API correctness lemmas for evaluation, coefficients, support, and degrees
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace CompPoly

namespace CBivariate

/-! Core conversion lemmas between `CBivariate R` and `R[X][Y]`. -/
section ToPolyCore

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

/-- `toPoly` preserves addition. -/
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
        ( show CPolynomial.support (p + q) ⊆
            CPolynomial.support p ∪ CPolynomial.support q from ?_ ) ]
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
        simp_all +decide [ CPolynomial.support ]
        grind

/-- `toPoly` sends a Y-monomial to the corresponding monomial in `R[X][Y]`. -/
lemma toPoly_monomial {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (n : ℕ) (c : CPolynomial R) :
    toPoly (CPolynomial.monomial n c) = monomial n (c.toPoly) := by
      unfold CPolynomial.monomial
      unfold CBivariate.toPoly
      unfold CPolynomial.support
      rw [ Finset.sum_eq_single n ] <;>
        simp +decide [ CPolynomial.Raw.monomial ]
      · split_ifs <;> simp_all +decide [ Array.push ]
      · grind
      · split_ifs <;> simp_all +decide [ Array.push ]
        exact toFinsupp_eq_zero.mp rfl

/-- `ofPoly` sends a Y-monomial in `R[X][Y]` to a bivariate monomial. -/
lemma ofPoly_monomial {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (n : ℕ) (c : R[X]) :
    ofPoly (monomial n c) =
    CPolynomial.monomial n ⟨c.toImpl, CPolynomial.Raw.trim_toImpl c⟩ := by
      unfold CBivariate.ofPoly
      simp +decide
      rw [ Finset.sum_eq_single n ] <;> simp +decide [ Polynomial.coeff_monomial ]
      aesop

/--
`Polynomial.toImpl` preserves addition, accounting for trimming in the raw representation.
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
          apply ‹∀ (p q : CPolynomial.Raw R),
              p.toPoly = q.toPoly → p.trim = q.trim›
          grind
        grind
      · exact Eq.symm (CPolynomial.Raw.trim_toImpl (p + q))

/-- `ofPoly` preserves addition in `R[X][Y]`. -/
lemma ofPoly_add {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p q : R[X][Y]) : ofPoly (p + q) = ofPoly p + ofPoly q := by
      -- Sum of two polynomials is sum of their coefficients; convert back using `ofPoly`.
      have h_ofPoly_add_p : ∀ (p q : Polynomial (Polynomial R)),
          ofPoly (p + q) = ofPoly p + ofPoly q := by
        unfold CBivariate.ofPoly
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
            rw [ ← CPolynomial.monomial_add ]
            congr
            exact Eq.symm (toImpl_add (p.coeff x) (q.coeff x))
          · aesop
          · aesop
        · aesop
        · contrapose! hx
          aesop
      exact h_ofPoly_add_p p q

/-- The outer coefficient of `ofPoly p` converts back to the corresponding `R[X]` coefficient. -/
theorem ofPoly_coeff {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : R[X][Y]) (n : ℕ) : (CPolynomial.coeff (ofPoly p) n).toPoly = p.coeff n := by
      -- By definition of `coeff`, we can express it as a sum over the support of `p`.
      have h_coeff_sum : CPolynomial.coeff (ofPoly p) n =
          Finset.sum (Polynomial.support p) (fun j =>
            CPolynomial.coeff
              (CPolynomial.monomial j
                ⟨Polynomial.toImpl (Polynomial.coeff p j),
                  CPolynomial.Raw.trim_toImpl (Polynomial.coeff p j)⟩) n) := by
        unfold CBivariate.ofPoly
        induction' p.support using Finset.induction with j s hj ih
        · exact CPolynomial.eq_iff_coeff.mpr (congrFun rfl)
        · rw [ Finset.sum_insert hj, CPolynomial.coeff_add, ih, Finset.sum_insert hj ]
      rw [ h_coeff_sum, Finset.sum_eq_single n ]
      · rw [ CPolynomial.coeff_monomial ]
        simp +decide [ CPolynomial.toPoly ]
        exact CPolynomial.Raw.toPoly_toImpl
      · simp +decide [ CPolynomial.coeff, CPolynomial.monomial ]
        unfold CPolynomial.Raw.monomial
        grind
      · aesop

/-- The outer coefficient of `toPoly p` is `CPolynomial.coeff p n` converted to `R[X]`. -/
theorem toPoly_coeff {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p : CBivariate R) (n : ℕ) : (toPoly p).coeff n = (CPolynomial.coeff p n).toPoly := by
      rw [ CBivariate.toPoly, Polynomial.finset_sum_coeff ]
      rw [ Finset.sum_eq_single n ] <;> simp +contextual [ Polynomial.coeff_monomial ]
      simp_all +decide [ CPolynomial.mem_support_iff ]
      aesop

/--
`toPoly` is the map of the outer polynomial via `CPolynomial.ringEquiv`.
-/
theorem toPoly_eq_map {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p : CBivariate R) :
    toPoly p = (CPolynomial.toPoly p).map (CPolynomial.ringEquiv (R := R)) := by
      convert Polynomial.ext _
      unfold CBivariate.toPoly
      simp +decide [ Polynomial.coeff_monomial ]
      intro n
      split_ifs <;> simp_all +decide [ CPolynomial.toPoly ]
      · erw [ CPolynomial.Raw.coeff_toPoly ]
        unfold CPolynomial.ringEquiv
        aesop
      · rw [ CPolynomial.Raw.coeff_toPoly ]
        simp +decide [ CPolynomial.support, * ] at *
        by_cases h : n < Array.size p.val <;> aesop

/-- `toPoly` preserves multiplication. -/
theorem toPoly_mul {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (p q : CBivariate R) :
    toPoly (p * q) = toPoly p * toPoly q := by
      have h_mul : (p * q).toPoly =
          (CPolynomial.toPoly (p * q)).map (CPolynomial.ringEquiv (R := R)) := by
        exact toPoly_eq_map (p * q)
      rw [ h_mul, CPolynomial.toPoly_mul ]
      rw [ Polynomial.map_mul, ← toPoly_eq_map, ← toPoly_eq_map ]

end ToPolyCore

/-! Ring equivalence between bivariate representations. -/
section RingEquiv

/-- Round-trip from Mathlib: converting a polynomial to `CBivariate` and back is the identity. -/
theorem ofPoly_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : R[X][Y]) : toPoly (ofPoly p) = p := by
      induction p using Polynomial.induction_on'
      · rw [ ofPoly_add, toPoly_add,
          ‹(ofPoly _).toPoly = _›, ‹(ofPoly _).toPoly = _› ]
      · rename_i n c
        simp +decide [ ofPoly_monomial, toPoly_monomial ]
        exact congr_arg _ ( CPolynomial.Raw.toPoly_toImpl )

/-- Round-trip from `CBivariate`: converting to Mathlib and back is the identity. -/
theorem toPoly_ofPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p : CBivariate R) : ofPoly (toPoly p) = p := by
      apply CPolynomial.eq_iff_coeff.mpr
      intro i
      -- Since `toPoly` is injective on canonical polynomials, coefficients equal ⇒ poly equal.
      have h_inj : Function.Injective (fun p : CPolynomial R => p.toPoly) := by
        intro p q h_eq
        have := CPolynomial.toImpl_toPoly_of_canonical p
        have := CPolynomial.toImpl_toPoly_of_canonical q
        aesop
      apply h_inj
      convert ofPoly_coeff p.toPoly i using 1
      exact Eq.symm (toPoly_coeff p i)

/-- Ring equivalence between `CBivariate R` and Mathlib's `R[X][Y]`. -/
noncomputable def ringEquiv
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    CBivariate R ≃+* R[X][Y] where
  toFun := toPoly
  invFun := ofPoly
  left_inv := toPoly_ofPoly
  right_inv := ofPoly_toPoly
  map_mul' := by apply toPoly_mul
  map_add' := by exact fun x y => toPoly_add x y

/-- `toPoly` preserves `1`. -/
theorem toPoly_one
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    toPoly (1 : CBivariate R) = 1 := by
  simpa [ringEquiv] using (ringEquiv (R := R)).map_one

/-- `ofPoly` preserves `1`. -/
theorem ofPoly_one
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    ofPoly (1 : R[X][Y]) = 1 := by
  apply (ringEquiv (R := R)).injective
  change toPoly (ofPoly (1 : R[X][Y])) = toPoly (1 : CBivariate R)
  rw [ofPoly_toPoly, toPoly_one]

/-- `toPoly` maps the zero bivariate polynomial to `0`. -/
lemma toPoly_zero {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] :
    toPoly (0 : CBivariate R) = 0 := by
      -- The sum over the empty set is zero.
      simp [CBivariate.toPoly]
      rw [ Finset.sum_eq_zero ]
      aesop

/-- `ofPoly` maps `0` in `R[X][Y]` to the zero bivariate polynomial. -/
lemma ofPoly_zero {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    ofPoly (0 : R[X][Y]) = 0 := by
      unfold CBivariate.ofPoly
      simp +decide [ Polynomial.support ]

/-- Ring hom from computable bivariates to Mathlib bivariates. -/
noncomputable def toPolyRingHom
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    CBivariate R →+* R[X][Y] :=
  (ringEquiv (R := R)).toRingHom

/-- Ring hom from Mathlib bivariates to computable bivariates. -/
noncomputable def ofPolyRingHom
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    R[X][Y] →+* CBivariate R :=
  (ringEquiv (R := R)).symm.toRingHom

/-- `ofPoly` preserves multiplication. -/
theorem ofPoly_mul
    {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R]
    (p q : R[X][Y]) :
    ofPoly (p * q) = ofPoly p * ofPoly q := by
  apply (ringEquiv (R := R)).injective
  change toPoly (ofPoly (p * q)) = toPoly (ofPoly p * ofPoly q)
  rw [ofPoly_toPoly, toPoly_mul, ofPoly_toPoly, ofPoly_toPoly]

end RingEquiv

/-! Correctness lemmas for evaluation, coefficients, support, and degrees. -/
section ImplementationCorrectness

/-- `toPoly` preserves full evaluation: `evalEval x y f = (toPoly f).evalEval x y`. -/
theorem evalEval_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (x y : R) (f : CBivariate R) :
    @CBivariate.evalEval R _ _ _ _ x y f = (toPoly f).evalEval x y := by
      unfold CBivariate.evalEval Polynomial.evalEval
      -- `toPoly f` has coefficients `f.val.coeff i`.
      have h_toPoly : (toPoly f).eval (Polynomial.C y) = (f.val.eval (CPolynomial.C y)).toPoly := by
        unfold CBivariate.toPoly
        simp +decide [ Polynomial.eval_finset_sum, CPolynomial.Raw.eval ]
        unfold CPolynomial.Raw.eval₂
        simp +decide
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
        · simp +contextual [ CPolynomial.support ]
          simp +decide [ CPolynomial.toPoly, CPolynomial.Raw.toPoly ]
          unfold CPolynomial.Raw.eval₂
          erw [ Array.foldl_empty ]
          simp
      -- `toPoly (f.val.eval (C y))` equals the polynomial with coefficients `f.val.coeff i`.
      rw [h_toPoly]
      exact CPolynomial.eval_toPoly x (CPolynomial.Raw.eval (CPolynomial.C y) ↑f)

/-- `toPoly` preserves coefficients: coefficient of `X^i Y^j` matches. -/
theorem coeff_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) (i j : ℕ) :
    ((toPoly f).coeff j).coeff i = @CBivariate.coeff R _ _ _ _ f i j := by
      convert CPolynomial.Raw.coeff_toPoly using 1
      rw [ CBivariate.toPoly ]
      simp +decide [ Polynomial.coeff_monomial ]
      split_ifs <;> simp_all +decide [ CPolynomial.support ]
      · congr
      · by_cases h : j < ( f.val.size : ℕ ) <;> aesop

/-- The outer support of `toPoly f` equals the Y-support of `f`. -/
theorem support_toPoly_outer {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) : (toPoly f).support = f.supportY := by
      ext x
      simp +decide [ CPolynomial.mem_support_iff, CBivariate.supportY ]
      rw [ CBivariate.toPoly ]
      simp +decide [ Polynomial.coeff_monomial ]
      rw [ CPolynomial.mem_support_iff, CPolynomial.toPoly_eq_zero_iff ]
      aesop

/-- `toPoly` preserves Y-degree. -/
theorem natDegreeY_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) : (toPoly f).natDegree = f.natDegreeY := by
      unfold CBivariate.natDegreeY
      -- The degree of the polynomial is the supremum of the exponents in its support.
      have h_deg : ∀ p : Polynomial (Polynomial R), p.natDegree = p.support.sup id := by
        intro p
        by_cases hp : p = 0
        · simp +decide [ hp ]
        · refine' le_antisymm _ _
          · exact Finset.le_sup (f := id) (Polynomial.natDegree_mem_support_of_nonzero hp)
          · exact Finset.sup_le fun i hi => Polynomial.le_natDegree_of_mem_supp _ hi
      rw [ h_deg, support_toPoly_outer ]
      -- Apply the fact that the degree of a polynomial is equal to the supremum of its support.
      apply Eq.symm
      exact CPolynomial.natDegree_eq_support_sup f

/-- The outer `Y`-coefficient formula used for X-degree transport. -/
theorem coeff_toPoly_Y {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) (j : ℕ) :
    (toPoly f).coeff j = CPolynomial.toPoly (f.val.coeff j) := by
      erw [ Polynomial.finset_sum_coeff ]
      rw [ Finset.sum_eq_single j ] <;> simp +contextual [ Polynomial.coeff_monomial ]
      intro hj
      rw [ CPolynomial.support ] at hj
      by_cases hj' : j < f.val.size <;> simp_all +decide
      · exact (CPolynomial.toPoly_eq_zero_iff 0).mpr rfl
      · exact (CPolynomial.toPoly_eq_zero_iff 0).mpr rfl

/-- `toPoly` preserves X-degree (max over Y-coefficients of their degree in X). -/
theorem natDegreeX_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) :
    (toPoly f).support.sup (fun j => ((toPoly f).coeff j).natDegree) = f.natDegreeX := by
      convert (Finset.sup_congr ?_ ?_)
      · ext
        simp +decide [ coeff_toPoly_Y ]
        rw [ CPolynomial.support ]
        by_cases h : ‹_› < f.val.size <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ]
        · -- Since `toPoly` is injective, if `toPoly (f.coeff j) = 0`, then `f.coeff j = 0`.
          have h_inj : ∀ (p : CPolynomial R), p.toPoly = 0 ↔ p = 0 := by
            intro p
            exact ⟨fun hp => by
              apply Subtype.ext
              apply_fun (fun p => p.toImpl) at hp
              convert hp using 1
              exact Eq.symm (CPolynomial.toImpl_toPoly_of_canonical p),
              fun hp => by aesop⟩
          aesop
        · exact (CPolynomial.toPoly_eq_zero_iff 0).mpr rfl
      · intro j hj
        rw [ coeff_toPoly_Y ]
        exact Eq.symm (CPolynomial.natDegree_toPoly (f.val.coeff j))

/--
`CC` corresponds to the nested constant polynomial in `R[X][Y]`.
-/
theorem CC_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] (r : R) :
    toPoly (CC (R := R) r) = Polynomial.C (Polynomial.C r) := by
  rw [ toPoly_eq_map ]
  unfold CBivariate.CC
  simp [ CPolynomial.C_toPoly ]
  change (CPolynomial.C r).toPoly = Polynomial.C r
  exact CPolynomial.C_toPoly r

/--
`X` (inner variable) corresponds to `Polynomial.C Polynomial.X` in `R[X][Y]`.
-/
theorem X_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] :
    toPoly (X (R := R)) = Polynomial.C Polynomial.X := by
  rw [ toPoly_eq_map ]
  simp [ CBivariate.X, CPolynomial.C_toPoly ]
  change (CPolynomial.X : CPolynomial R).toPoly = Polynomial.X
  exact CPolynomial.X_toPoly

/--
`Y` (outer variable) corresponds to `Polynomial.X` in `R[X][Y]`.
-/
theorem Y_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R] [DecidableEq R] :
    toPoly (CBivariate.Y (R := R)) = (Polynomial.X : Polynomial (Polynomial R)) := by
  simpa [CBivariate.Y, CPolynomial.C_toPoly] using
    (toPoly_monomial (R := R) 1 (CPolynomial.C 1))

/--
`monomialXY n m c` corresponds to `Y^m` with inner coefficient `X^n * c`.
-/
theorem monomialXY_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (n m : ℕ) (c : R) :
    toPoly (monomialXY (R := R) n m c) = Polynomial.monomial m (Polynomial.monomial n c) := by
  unfold CBivariate.monomialXY
  rw [ toPoly_monomial ]
  congr
  simpa using CPolynomial.monomial_toPoly (R := R) n c

/--
`supportX` corresponds to the union of inner supports of outer coefficients.
-/
theorem supportX_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) :
    CBivariate.supportX (R := R) f =
      (toPoly f).support.biUnion (fun j => ((toPoly f).coeff j).support) := by
  unfold CBivariate.supportX
  rw [ support_toPoly_outer ]
  refine Finset.biUnion_congr rfl ?_
  intro j hj
  simpa [ toPoly_coeff ] using (CPolynomial.support_toPoly (f.val.coeff j))

/--
`totalDegree` corresponds to the supremum over `j` of `natDegree ((toPoly f).coeff j) + j`.
-/
theorem totalDegree_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) :
    CBivariate.totalDegree (R := R) f =
      (toPoly f).support.sup (fun j => ((toPoly f).coeff j).natDegree + j) := by
  unfold CBivariate.totalDegree
  rw [ support_toPoly_outer ]
  refine Finset.sup_congr rfl ?_
  intro j hj
  rw [ toPoly_coeff ]
  simpa using congrArg (fun n => n + j) (CPolynomial.natDegree_toPoly (f.val.coeff j))

/--
`evalX a` evaluates each inner coefficient at `a`.
-/
theorem evalX_toPoly_coeff {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (a : R) (f : CBivariate R) (j : ℕ) :
    ((evalX (R := R) a f).toPoly).coeff j = ((toPoly f).coeff j).eval a := by
  sorry

/--
`evalX` is compatible with full bivariate evaluation.
-/
theorem evalX_toPoly_eval {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (a y : R) (f : CBivariate R) :
    (evalX (R := R) a f).eval y = (toPoly f).evalEval a y := by
  sorry

/--
`evalY a` corresponds to outer evaluation at `Polynomial.C a`.
-/
theorem evalY_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (a : R) (f : CBivariate R) :
    (evalY (R := R) a f).toPoly = (toPoly f).eval (Polynomial.C a) := by
  unfold CBivariate.evalY
  have h_toPoly : (toPoly f).eval (Polynomial.C a) = (f.val.eval (CPolynomial.C a)).toPoly := by
    unfold CBivariate.toPoly
    simp +decide [ Polynomial.eval_finset_sum, CPolynomial.Raw.eval ]
    unfold CPolynomial.Raw.eval₂
    simp +decide
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
    · simp +contextual [ CPolynomial.support ]
      simp +decide [ CPolynomial.toPoly, CPolynomial.Raw.toPoly ]
      unfold CPolynomial.Raw.eval₂
      erw [ Array.foldl_empty ]
      simp
  exact h_toPoly.symm

/--
`leadingCoeffY` corresponds to the leading coefficient in the outer variable.
-/
theorem leadingCoeffY_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    (f : CBivariate R) :
    (leadingCoeffY (R := R) f).toPoly = (toPoly f).leadingCoeff := by
  have h_leadingCoeffY : (f.val.leadingCoeff).toPoly = (toPoly f).coeff (f.val.natDegree) := by
    rw [ CBivariate.toPoly_coeff ]
    congr
    convert CompPoly.CPolynomial.leadingCoeff_eq_coeff_natDegree f
    exact instDecidableEqOfLawfulBEq
  convert h_leadingCoeffY
  rw [ Polynomial.leadingCoeff, Polynomial.natDegree ]
  by_cases h : f.toPoly = 0 <;> simp_all +decide [ Polynomial.degree_eq_natDegree ]
  rw [ CompPoly.CBivariate.natDegreeY_toPoly ]
  rfl

/--
`swap` exchanges X- and Y-exponents.
-/
theorem swap_toPoly_coeff {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (f : CBivariate R) (i j : ℕ) :
    ((toPoly (swap (R := R) f)).coeff j).coeff i = ((toPoly f).coeff i).coeff j := by
  sorry

/--
`leadingCoeffX` is the Y-leading coefficient of the swapped polynomial.
-/
theorem leadingCoeffX_toPoly {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Ring R]
    [DecidableEq R] (f : CBivariate R) :
    (leadingCoeffX (R := R) f).toPoly = (toPoly (swap (R := R) f)).leadingCoeff := by
  simpa [ CBivariate.leadingCoeffX ] using
    (leadingCoeffY_toPoly (R := R) (f := CBivariate.swap (R := R) f))

end ImplementationCorrectness

end CBivariate

end CompPoly
