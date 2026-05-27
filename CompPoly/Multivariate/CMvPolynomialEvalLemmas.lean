/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Natalia Klaus, Frantisek Silvasi, Derek Sorensen, Andrew Zitek-Estrada
-/
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.MvPolyEquiv.Instances
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots

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

/-- Bridge a single-variable `MvPolynomial (Fin 1) R` to `Polynomial R` by
sending the unique variable to `Polynomial.X`. -/
private noncomputable def toUnivariate [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) : Polynomial R :=
  MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) p

/-- The map `toUnivariate` factors through `finSuccEquiv` and `isEmptyRingEquiv`.
This is needed to transport degree information from `degreeOf` to `natDegree`. -/
private lemma toUnivariate_eq_map_finSuccEquiv [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) :
    toUnivariate p =
      Polynomial.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
        (MvPolynomial.finSuccEquiv R 0 p) := by
  -- Both sides are ring-homomorphism evaluations of `p`; equate the ring homs
  -- by `MvPolynomial.ringHom_ext` and then evaluate on generators.
  have :
      (MvPolynomial.eval₂Hom Polynomial.C (fun _ : Fin 1 => Polynomial.X) :
          MvPolynomial (Fin 1) R →+* Polynomial R)
        = (Polynomial.mapRingHom
            (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom).comp
            (MvPolynomial.finSuccEquiv R 0).toRingHom := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      simp [MvPolynomial.finSuccEquiv_apply, Polynomial.map_C,
            MvPolynomial.isEmptyRingEquiv]
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [MvPolynomial.finSuccEquiv_X_zero]
  exact congrArg (fun f : MvPolynomial (Fin 1) R →+* Polynomial R => f p) this

/-- `toUnivariate` preserves the (univariate) degree: its `natDegree` matches
the `degreeOf 0` of the original `MvPolynomial (Fin 1) R`. -/
private lemma natDegree_toUnivariate [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) :
    (toUnivariate p).natDegree = p.degreeOf 0 := by
  rw [toUnivariate_eq_map_finSuccEquiv]
  have hmap : (Polynomial.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom
        (MvPolynomial.finSuccEquiv R 0 p)).natDegree =
      (MvPolynomial.finSuccEquiv R 0 p).natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective _
  rw [hmap, MvPolynomial.natDegree_finSuccEquiv]

/-- Evaluating `toUnivariate p` at `x : R` agrees with evaluating the
original `MvPolynomial (Fin 1) R` at the constant assignment `fun _ ↦ x`. -/
private lemma eval_toUnivariate [CommSemiring R]
    (p : MvPolynomial (Fin 1) R) (x : R) :
    (toUnivariate p).eval x = MvPolynomial.eval (fun _ => x) p := by
  -- `Polynomial.eval x (eval₂ Polynomial.C (fun _ => X) p) = eval (fun _ => x) p`.
  show Polynomial.eval x
      (MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) p) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext r; simp
  · funext _; simp

/-- `toUnivariate` reflects non-zeroness: a non-zero `MvPolynomial (Fin 1) R`
maps to a non-zero `Polynomial R`. -/
private lemma toUnivariate_ne_zero [CommSemiring R]
    {p : MvPolynomial (Fin 1) R} (hp : p ≠ 0) : toUnivariate p ≠ 0 := by
  intro h
  apply hp
  rw [toUnivariate_eq_map_finSuccEquiv] at h
  have h2 : MvPolynomial.finSuccEquiv R 0 p = 0 :=
    (Polynomial.map_eq_zero_iff
      (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective).mp h
  exact (MvPolynomial.finSuccEquiv R 0).injective (by simpa using h2)

/-- **Univariate eval-extensionality (degree-bounded).** Two single-variable
`CMvPolynomial`s over an integral domain that agree on more than `d` points
of a `Finset S` are equal, when `d` bounds the `degreeOf 0` of their
difference (viewed through the `MvPolynomial` bridge).

The hypothesis form matches Schwartz–Zippel usage at call sites: callers
typically have a degree bound on the *difference* polynomial, not on `p` and
`q` individually. -/
theorem CMvPolynomial.eval_ext_univariate
    [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]
    {p q : CMvPolynomial 1 R} {d : ℕ} {S : Finset R}
    (hdeg : (fromCMvPolynomial p - fromCMvPolynomial q).degreeOf 0 ≤ d)
    (hagree :
      d < (S.filter
              (fun r => p.eval (fun _ => r) = q.eval (fun _ => r))).card) :
    p = q := by
  rw [eq_iff_fromCMvPolynomial]
  by_contra hne
  set r : MvPolynomial (Fin 1) R :=
    fromCMvPolynomial p - fromCMvPolynomial q with hr
  have hrne : r ≠ 0 := sub_ne_zero.mpr hne
  -- Bridge to `Polynomial R` and collect facts about the univariate image.
  let rPoly : Polynomial R := toUnivariate r
  have hrPolyNe : rPoly ≠ 0 := toUnivariate_ne_zero hrne
  have hrPolyDeg : rPoly.natDegree ≤ d := by
    show (toUnivariate r).natDegree ≤ d
    rw [natDegree_toUnivariate]; exact hdeg
  -- Build the witnessing `Finset` of zeros of `rPoly` from the agreement set.
  let T : Finset R :=
    S.filter (fun x => p.eval (fun _ => x) = q.eval (fun _ => x))
  have hTcard : d < T.card := hagree
  have heval_zero : ∀ x ∈ T, rPoly.eval x = 0 := by
    intro x hx
    have hxeq : p.eval (fun _ => x) = q.eval (fun _ => x) :=
      (Finset.mem_filter.mp hx).2
    show (toUnivariate r).eval x = 0
    rw [eval_toUnivariate]
    have hbridge : MvPolynomial.eval (fun _ => x) (fromCMvPolynomial p) =
           MvPolynomial.eval (fun _ => x) (fromCMvPolynomial q) := by
      rw [← eval_equiv, ← eval_equiv]; exact hxeq
    show MvPolynomial.eval (fun _ => x) r = 0
    have hsub : MvPolynomial.eval (fun _ => x)
        (fromCMvPolynomial p - fromCMvPolynomial q) =
        MvPolynomial.eval (fun _ => x) (fromCMvPolynomial p) -
          MvPolynomial.eval (fun _ => x) (fromCMvPolynomial q) :=
      RingHom.map_sub _ _ _
    rw [hr, hsub, hbridge, sub_self]
  -- Apply the univariate Schwartz–Zippel-style root bound.
  exact hrPolyNe <|
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' rPoly T
      heval_zero (lt_of_le_of_lt hrPolyDeg hTcard)

end EvalExtUnivariate

end CPoly
