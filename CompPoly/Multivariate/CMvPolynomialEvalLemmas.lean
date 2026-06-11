/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Natalia Klaus, Frantisek Silvasi, Derek Sorensen, Andrew Zitek-Estrada
-/
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.MvPolyEquiv.Instances
import CompPoly.Univariate.CMvEquiv

/-!
# simp/grind lemmas for `CPoly.CMvPolynomial.eval`

These lemmas are meant to support proof automation (simp/grind normalization)
when reasoning about polynomial evaluation (e.g. Horner correctness proofs).

The final section provides a degree-bounded eval-extensionality lemma for
single-variable `CMvPolynomial`s over an integral domain (a Schwartz–Zippel
style result specialized to one variable), suitable for soundness proofs in
protocols such as sumcheck.
-/
namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
variable (vals : Fin n → R)

@[simp]
lemma eval_zero : (0 : CMvPolynomial n R).eval vals = 0 := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_zero

@[simp]
lemma eval_one : (1 : CMvPolynomial n R).eval vals = 1 := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_one

@[simp]
lemma eval_C (c : R) : (CMvPolynomial.C c : CMvPolynomial n R).eval vals = c := by
  simp [eval_equiv, fromCMvPolynomial_C]

@[simp]
lemma eval_add (p q : CMvPolynomial n R) :
    (p + q).eval vals = p.eval vals + q.eval vals := by simp [eval_equiv]

@[simp]
lemma eval_mul (p q : CMvPolynomial n R) :
    (p * q).eval vals = p.eval vals * q.eval vals := by simp [eval_equiv]

@[simp]
lemma eval_pow (p : CMvPolynomial n R) (k : ℕ) :
    (p ^ k).eval vals = (p.eval vals) ^ k := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_pow p k

end

section

variable {n : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R]
variable (vals : Fin n → R)

@[simp]
lemma eval_neg (p : CMvPolynomial n R) :
    (-p).eval vals = -(p.eval vals) := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_neg p

@[simp]
lemma eval_sub (p q : CMvPolynomial n R) :
    (p - q).eval vals = p.eval vals - q.eval vals := by
  simpa [eval₂Hom_apply] using (eval₂Hom (RingHom.id R) vals).map_sub p q

end

attribute [grind =]
  eval_zero eval_one eval_C eval_add eval_mul eval_pow eval_neg eval_sub

/-! ### Degree-bounded eval-extensionality (univariate) -/

section EvalExtUnivariate

variable {R : Type*}

/-- **Bridge from univariate eval-extensionality.** Two single-variable
`CMvPolynomial`s over an integral domain that agree on more than $d$ points
of a `Finset S` are equal, when $d$ bounds the `degreeOf 0` of their
difference through the `CPolynomial.cmvEquiv` bridge.

The hypothesis form matches Schwartz–Zippel usage at call sites: callers
typically have a degree bound on the difference polynomial, not on `p` and
`q` individually. -/
theorem CMvPolynomial.eval_ext_univariate
    [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]
    {p q : CMvPolynomial 1 R} {d : ℕ} {S : Finset R}
    (hdeg : (fromCMvPolynomial p - fromCMvPolynomial q).degreeOf 0 ≤ d)
    (hagree :
      d < (S.filter
              (fun r ↦ p.eval (fun _ ↦ r) = q.eval (fun _ ↦ r))).card) :
    p = q := by
  let pUni := (CompPoly.CPolynomial.cmvEquiv (R := R)).symm p
  let qUni := (CompPoly.CPolynomial.cmvEquiv (R := R)).symm q
  have hdegUni : (pUni - qUni).natDegree ≤ d := by
    rw [show pUni = (CompPoly.CPolynomial.cmvEquiv (R := R)).symm p from rfl,
      show qUni = (CompPoly.CPolynomial.cmvEquiv (R := R)).symm q from rfl,
      CompPoly.CPolynomial.natDegree_cmvEquiv_symm_sub]
    exact hdeg
  have hagreeUni :
      d < (S.filter (fun r ↦ pUni.eval r = qUni.eval r)).card := by
    convert hagree using 3
    rw [show pUni = (CompPoly.CPolynomial.cmvEquiv (R := R)).symm p from rfl,
      show qUni = (CompPoly.CPolynomial.cmvEquiv (R := R)).symm q from rfl,
      CompPoly.CPolynomial.eval_cmvEquiv_symm,
      CompPoly.CPolynomial.eval_cmvEquiv_symm]
  have hUni : pUni = qUni :=
    CompPoly.CPolynomial.eval_ext (p := pUni) (q := qUni) hdegUni hagreeUni
  exact (CompPoly.CPolynomial.cmvEquiv (R := R)).symm.injective hUni

end EvalExtUnivariate

end CPoly
