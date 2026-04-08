/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
import CompPoly.Univariate.ToPoly.Equiv

/-!
# Proofs of Correctness for CPolynomial Operations, wrt Mathlib Specs

Proofs that operations defined on CPolynomial and CPolynomial.Raw are correct
wrt the mathlib specs, using the ring equivalence
-/

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

section ImplementationCorrectness

variable {R : Type*} [Semiring R]

/-- CPolynomial.monomial is correct wrt the Mathlib spec. -/
theorem monomial_toPoly [DecidableEq R] [LawfulBEq R] (n : ℕ) (c : R) :
    (monomial n c).toPoly = Polynomial.monomial n c := by
  ext i
  simp only [CPolynomial.toPoly, monomial]
  rw [Polynomial.coeff_monomial, coeff_toPoly, CPolynomial.Raw.coeff_monomial]

/-- CPolynomial.C is correct wrt the Mathlib spec. -/
theorem C_toPoly [BEq R] [LawfulBEq R] (r : R) : (C r).toPoly = Polynomial.C r := by
  convert Raw.toPoly_C r
  convert Raw.toPoly_trim
  infer_instance

/-- CPolynomial.X is correct wrt the Mathlib spec. -/
theorem X_toPoly [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).toPoly = Polynomial.X := by
  change (CPolynomial.Raw.X : CPolynomial.Raw R).toPoly = Polynomial.X
  exact CPolynomial.Raw.toPoly_X (R := R)

/-- CPolynomial.eval is correct wrt the Mathlib spec. -/
theorem eval_toPoly [BEq R] [LawfulBEq R] (x : R) (p : CPolynomial R) :
    eval x p = p.toPoly.eval x := by
  convert Raw.eval_toPoly_eq_eval x p.val
  · rw [ Raw.eval_toPoly_eq_eval ]; rfl
  · convert Raw.eval_toPoly_eq_eval x p.val

/-- Raw.eval₂ is correct wrt the Mathlib spec. -/
theorem Raw.eval₂_toPoly {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial.Raw R) :
    p.eval₂ f x = p.toPoly.eval₂ f x := by
  unfold CompPoly.CPolynomial.Raw.toPoly
  rw [CPolynomial.Raw.eval₂_eq_eval₂_naive, CPolynomial.Raw.eval₂_eq_eval₂_naive]
  unfold CompPoly.CPolynomial.Raw.eval₂Naive
  rw [← Array.foldl_hom (fun q : R[X] ↦ q.eval₂ f x)
    (g₁ := fun acc (t : R × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + f a * x ^ i)]
  · simp
  · intro acc t
    rcases t with ⟨a, i⟩
    simp [Polynomial.eval₂_add, Polynomial.C_mul_X_pow_eq_monomial]

/-- CPolynomial.eval₂ is correct wrt the Mathlib spec. -/
theorem eval₂_toPoly {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂ f x p = p.toPoly.eval₂ f x := by
  exact Raw.eval₂_toPoly f x p.val

/-- CPolynomial.coeff is correct wrt the Mathlib spec. -/
theorem coeff_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    p.coeff i = p.toPoly.coeff i := by
  unfold toPoly coeff
  simp [Raw.coeff_toPoly]

/-- CPolynomial.divX is correct wrt the Mathlib spec. -/
theorem divX_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (divX p).toPoly = p.toPoly.divX := by
  ext n
  simp only [CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly, CPolynomial.coeff,
    CompPoly.CPolynomial.coeff_divX, Polynomial.coeff_divX]

/-- CPolynomial.support is correct wrt the Mathlib spec. -/
theorem support_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
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

/-- lemma: toImpl is natDegree's succ -/
private lemma size_toImpl_eq_natDegree_succ {q : R[X]} (hq : q ≠ 0) :
    q.toImpl.size = q.natDegree + 1 := by
  rcases Raw.toImpl_elim q with ⟨hzero, _⟩ | ⟨_, himpl⟩
  · exact (hq hzero).elim
  · simp [himpl]

/-- lemma: size = natDegree's succ -/
private lemma size_eq_toPoly_natDegree_succ [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (hp : p ≠ 0) :
    p.val.size = p.toPoly.natDegree + 1 := by
  have htoPoly : p.toPoly ≠ 0 := (toPoly_eq_zero_iff p).not.mpr hp
  have hsize : p.toPoly.toImpl.size = p.val.size := by
    simpa using congrArg Array.size (toImpl_toPoly_of_canonical p)
  rw [← hsize]
  exact size_toImpl_eq_natDegree_succ htoPoly

/-- CPolynomial.degree is correct wrt the Mathlib spec. -/
theorem degree_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.degree = p.toPoly.degree := by
  by_cases hp : p = 0
  · subst hp
    rw [toPoly_zero, CPolynomial.degree]
    rfl
  · have hsize := size_eq_toPoly_natDegree_succ p hp
    have htoPoly : p.toPoly ≠ 0 := (toPoly_eq_zero_iff p).not.mpr hp
    cases hs : p.val.size with
    | zero =>
        simp [hs] at hsize
    | succ n =>
        have hnat : p.toPoly.natDegree = n := by omega
        simp [CPolynomial.degree, hs, hnat,
          Polynomial.degree_eq_natDegree htoPoly]

/-- CPolynomial.natDegree is correct wrt the Mathlib spec. -/
theorem natDegree_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.natDegree = p.toPoly.natDegree := by
  by_cases hp : p = 0
  · subst hp
    rw [
      toPoly_zero,
      CPolynomial.natDegree
    ]
    rfl
  · have hsize := size_eq_toPoly_natDegree_succ p hp
    cases hs : p.val.size with
    | zero =>
        simp [hs] at hsize
    | succ n =>
        have hnat : p.toPoly.natDegree = n := by omega
        rw [
          hnat,
          CPolynomial.natDegree,
          hs
        ]

/-- CPolynomial.leadingCoeff is correct wrt the Mathlib spec. -/
theorem leadingCoeff_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  by_cases hp : p = 0
  · subst hp
    rw [toPoly_zero, CPolynomial.leadingCoeff]
    rfl
  · have htoPoly : p.toPoly ≠ 0 := (toPoly_eq_zero_iff p).not.mpr hp
    have hpos : p.val.size > 0 := by
      have hsize := size_eq_toPoly_natDegree_succ p hp
      omega
    have hlastImpl :
        p.toPoly.toImpl.getLast (Raw.toImpl_nonzero htoPoly) = p.toPoly.leadingCoeff := by
      simpa using Raw.getLast_toImpl htoPoly
    have hround : p.toPoly.toImpl = (p : CPolynomial.Raw R) := by
      simpa using toImpl_toPoly_of_canonical p
    have hlast : p.val.getLast hpos = p.toPoly.leadingCoeff := by
      simpa [hround] using hlastImpl
    simpa [CPolynomial.leadingCoeff, Array.getLastD, hpos] using hlast

/-- CPolynomial.erase is correct wrt the Mathlib spec. -/
theorem erase_toPoly {R : Type*} [Ring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (p : CPolynomial R) :
    (erase n p).toPoly = p.toPoly.erase n := by
  have h_erase_def : (CPolynomial.erase n p).toPoly
      = p.toPoly - Polynomial.monomial n (p.val.coeff n) := by
    have h_erase_toPoly : ∀ (p q : CPolynomial.Raw R),
        (p - q).toPoly = p.toPoly - q.toPoly := by
      intros p q;
      have h_erase_toPoly : ∀ (p q : CPolynomial.Raw R),
          (p + -q).toPoly = p.toPoly + (-q).toPoly := by
        exact fun p q ↦ Raw.toPoly_add p (-q)
      convert h_erase_toPoly p q using 1
      simp +decide [Raw.toPoly]
      rw [show (-q : CompPoly.CPolynomial.Raw R) = q.map (fun x ↦ -x) from ?_]
      · simp only [CPolynomial.Raw.eval₂_eq_eval₂_naive]
        simp +decide [ Raw.eval₂Naive ]
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

/-- CPolynomial.C r mul CPolynomial.X ^ n is correct wrt the Mathlib spec. -/
theorem C_mul_X_pow_toPoly [BEq R] [LawfulBEq R] [DecidableEq R] [Nontrivial R] (r : R) (n : ℕ) :
    (C r * X ^ n).toPoly = Polynomial.monomial n r := by
  convert C_mul_X_pow_eq_monomial r n using 1
  constructor <;> intro h
  · exact C_mul_X_pow_eq_monomial r n
  · convert monomial_toPoly n r

/-- CPolynomial.lcoeff is correct wrt the Mathlib spec. -/
theorem lcoeff_toPoly [BEq R] [LawfulBEq R] (n : ℕ) (p : CPolynomial R) :
    lcoeff (R := R) n p = Polynomial.lcoeff R n (toPoly p) := by
    simp [lcoeff, Polynomial.lcoeff_apply, ← coeff_toPoly]

/-- CPolynomial.degreeLE is correct wrt the Mathlib spec. -/
theorem degreeLE_toPoly {n : WithBot ℕ} [BEq R] [LawfulBEq R] {p : CPolynomial R} :
    p ∈ degreeLE (R := R) n ↔ p.toPoly ∈ Polynomial.degreeLE R n := by
  rw [Polynomial.mem_degreeLE]
  convert (show p.degree ≤ n ↔ p.toPoly.degree ≤ n by rw [degree_toPoly]) using 1

/-- CPolynomial.degreeLT is correct wrt the Mathlib spec. -/
theorem degreeLT_toPoly {n : ℕ} [BEq R] [LawfulBEq R] {p : CPolynomial R} :
    p ∈ degreeLT (R := R) n ↔ p.toPoly ∈ Polynomial.degreeLT R n := by
  rw [Polynomial.mem_degreeLT]
  convert (show p.degree < n ↔ p.toPoly.degree < n by rw [degree_toPoly]) using 1

end ImplementationCorrectness

end CPolynomial

end CompPoly
