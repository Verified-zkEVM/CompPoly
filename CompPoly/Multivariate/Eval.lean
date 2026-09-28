/-
Copyright (c) 2024-2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import CompPoly.Multivariate.Operations
public import CompPoly.Univariate.CMvEquiv

/-!
  # Evaluation of computable multivariate polynomials, bundled and over `Finset`s

  CompPoly records that `CMvPolynomial.eval vals` respects each ring operation separately
  (`eval_zero`, `eval_one`, `eval_add`, `eval_mul`, `eval_C`, …), which is what `simp`/`grind`
  need to normalize a *fixed* expression. Two things are missing for reasoning about a **family**
  of polynomials: the value of a bare variable, and commutation with `Finset.sum` / `Finset.prod`.

  Both follow at once from bundling: `CMvPolynomial.eval vals` is `eval₂Hom (RingHom.id R) vals`,
  so `map_sum` and `map_prod` apply verbatim. `evalHom` records that bundling; the two `Finset`
  lemmas are its immediate corollaries, stated in unbundled form so that call sites can rewrite
  without unfolding.

-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] (vals : Fin n → R)

/-- Evaluation at a fixed point, bundled as a ring homomorphism — the identity-coefficient case
of `eval₂Hom`. This is what gives evaluation the `map_*` API of a `RingHom`. -/
def evalHom : CMvPolynomial n R →+* R := eval₂Hom (RingHom.id R) vals

@[simp]
theorem evalHom_apply (p : CMvPolynomial n R) : evalHom vals p = p.eval vals := rfl

@[simp]
lemma eval_zero : (0 : CMvPolynomial n R).eval vals = 0 := by
  simp [eval_equiv]

@[simp]
lemma eval_one : (1 : CMvPolynomial n R).eval vals = 1 := by
  simp [eval_equiv]

@[simp]
lemma eval_C (c : R) : (CMvPolynomial.C c : CMvPolynomial n R).eval vals = c := by
  simp [eval_equiv, fromCMvPolynomial_C]

@[simp]
theorem eval_X (i : Fin n) : (X (R := R) i).eval vals = vals i := by
  rw [eval_equiv, fromCMvPolynomial_X, MvPolynomial.eval_X]

@[simp]
lemma eval_add (p q : CMvPolynomial n R) :
    (p + q).eval vals = p.eval vals + q.eval vals := by simp [eval_equiv]

@[simp]
lemma eval_mul (p q : CMvPolynomial n R) :
    (p * q).eval vals = p.eval vals * q.eval vals := by simp [eval_equiv]

@[simp]
lemma eval_pow (p : CMvPolynomial n R) (k : ℕ) :
    (p ^ k).eval vals = (p.eval vals) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, eval_mul, ih, pow_succ]

section

variable {n : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R]
variable (vals : Fin n → R)

@[simp]
lemma eval_neg (p : CMvPolynomial n R) :
    (-p).eval vals = -(p.eval vals) := by
  simp [eval_equiv]

@[simp]
lemma eval_sub (p q : CMvPolynomial n R) :
    (p - q).eval vals = p.eval vals - q.eval vals := by
  rw [sub_eq_add_neg, eval_add, eval_neg, sub_eq_add_neg]

end

/-- Evaluation commutes with a finite sum of polynomials. -/
theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    (∑ i ∈ s, f i).eval vals = ∑ i ∈ s, (f i).eval vals :=
  map_sum (evalHom vals) f s

/-- Evaluation commutes with a finite product of polynomials. -/
theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    (∏ i ∈ s, f i).eval vals = ∏ i ∈ s, (f i).eval vals :=
  map_prod (evalHom vals) f s

/-! ## Transporting a whole polynomial

The lemmas above are enough for statements about *values*. A statement about *degrees* is not
determined by values (two distinct polynomials agree everywhere over a finite field), so it has to
cross the representation boundary at the level of the polynomial itself, through
`fromCMvPolynomial`. That map is the forward direction of `polyRingEquiv`, hence a ring
homomorphism, so it too commutes with `Finset.sum` and `Finset.prod`. -/

end CPoly.CMvPolynomial

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

attribute [grind =]
  eval_zero eval_one eval_C eval_add eval_mul eval_pow eval_neg eval_sub

section EvalExtUnivariate

variable {R : Type*}

/-- **Bridge from univariate eval-extensionality.** Two single-variable
`CMvPolynomial`s over an integral domain that agree on more than $d$ points
of a `Finset S` are equal, when $d$ bounds the `degreeOf 0` of their
difference through the `CPolynomial.cmvEquiv` bridge.

The hypothesis form matches Schwartz–Zippel usage at call sites: callers
typically have a degree bound on the difference polynomial, not on `p` and
`q` individually. -/
theorem eval_ext_univariate
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

end CPoly.CMvPolynomial
