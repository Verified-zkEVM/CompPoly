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
  unfold CompPoly.CPolynomial.Raw.toPoly CompPoly.CPolynomial.Raw.eval₂
  rw [← Array.foldl_hom (fun q : R[X] => q.eval₂ f x)
    (g₁ := fun acc (t : R × ℕ) => acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) => acc + f a * x ^ i)]
  · simp
  · intro acc t
    rcases t with ⟨a, i⟩
    simp [Polynomial.eval₂_add, Polynomial.C_mul_X_pow_eq_monomial]

/-- CPolynomial.eval₂ is correct wrt the Mathlib spec. -/
theorem eval₂_toPoly {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂ f x p = p.toPoly.eval₂ f x := by
  simpa [CompPoly.CPolynomial.eval₂, CompPoly.CPolynomial.toPoly, CompPoly.CPolynomial.Raw.eval₂]
    using
    (Raw.eval₂_toPoly (f := f) (x := x) (p := p.val))

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
  ext i
  rw [← coeff_toPoly, Polynomial.coeff_erase, coeff_erase, ← coeff_toPoly]

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

section EvaluationDivision

variable {R : Type*}

/-- Evaluation preserves multiplication. -/
theorem eval_mul [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (x : R) :
    (p * q).eval x = p.eval x * q.eval x := by
  rw [eval_toPoly, toPoly_mul, Polynomial.eval_mul, ← eval_toPoly, ← eval_toPoly]

namespace Raw

theorem eval_sub_C_mul_X_pow_trim_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial.Raw R) (scale : R)
    (shift : ℕ) {x : R} (hq : q.eval x = 0) :
    ((p - C scale * (q * X ^ shift)).trim).eval x = p.eval x := by
  rw [eval_trim_eq_eval]
  rw [← eval_toPoly_eq_eval x]
  rw [toPoly_sub, toPoly_mul, toPoly_C, toPoly_mul, toPoly_pow, toPoly_X]
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp [eval_toPoly_eq_eval, hq]

theorem eval_divModByMonicAux_go_snd_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] :
    ∀ (fuel : ℕ) (p q : CPolynomial.Raw R) {x : R}, q.eval x = 0 →
      (divModByMonicAux.go fuel p q).2.eval x = p.eval x := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q x hq
      rfl
  | succ fuel ih =>
      intro p q x hq
      unfold divModByMonicAux.go
      by_cases hsize : p.size < q.size
      · simp [hsize]
      · simp [hsize]
        trans ((p - C p.leadingCoeff * (q * X ^ (p.size - q.size))).trim).eval x
        · exact ih _ _ hq
        · exact eval_sub_C_mul_X_pow_trim_eq_self_of_eval_eq_zero p q p.leadingCoeff
            (p.size - q.size) hq

/-- Reducing by a polynomial that vanishes at `x` preserves evaluation at `x`. -/
theorem eval_modByMonic_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial.Raw R) {x : R}
    (hq : q.eval x = 0) :
    (modByMonic p q).eval x = p.eval x :=
  eval_divModByMonicAux_go_snd_eq_self_of_eval_eq_zero p.size p q hq

end Raw

/-- Reducing by a polynomial that vanishes at `x` preserves evaluation at `x`. -/
theorem eval_modByMonic_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) {x : R}
    (hq : q.eval x = 0) :
    (CPolynomial.modByMonic p q).eval x = p.eval x := by
  have hq_raw : q.val.eval x = 0 := by
    simpa [CPolynomial.eval, Raw.eval, Raw.eval₂] using hq
  change ((Raw.modByMonic p.val q.val).trim).eval x = p.val.eval x
  rw [Raw.eval_trim_eq_eval]
  exact Raw.eval_modByMonic_eq_self_of_eval_eq_zero p.val q.val hq_raw

end EvaluationDivision

end CPolynomial

end CompPoly
