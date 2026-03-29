/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Multivariate.Operations

/-!
# Direct Computable `CMvPolynomial 1` / `CPolynomial` Equivalence

This file adds a dedicated one-variable bridge between sparse computable multivariate
polynomials and canonical computable univariate polynomials.

The public maps are implemented directly in CompPoly:

- `CMvPolynomial.toUnivariate` evaluates a `CMvPolynomial 1 R` at the univariate
  indeterminate `CPolynomial.X`.
- `CMvPolynomial.ofUnivariate` evaluates a `CPolynomial R` at the multivariate
  indeterminate `CMvPolynomial.X 0`.

The runtime definitions are computable and avoid the existing noncomputable
`MvPolynomial` / `Polynomial` transport path.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- The constant-polynomial constructor bundled as a ring homomorphism. -/
def CRingHom : R →+* CPolynomial R where
  toFun := C
  map_zero' := by
    apply eq_iff_coeff.2
    intro i
    rw [coeff_C, coeff_zero]
    split_ifs <;> simp
  map_one' := by
    apply eq_iff_coeff.2
    intro i
    rw [coeff_C, coeff_one]
  map_add' x y := by
    apply eq_iff_coeff.2
    intro i
    rw [coeff_C, coeff_add, coeff_C, coeff_C]
    split_ifs <;> simp
  map_mul' x y := by
    apply eq_iff_coeff.2
    intro i
    rw [coeff_C, coeff_C_mul (p := C y) (c := x), coeff_C]
    split_ifs <;> simp

@[simp]
lemma CRingHom_apply (r : R) : CRingHom (R := R) r = C r := rfl

omit [Nontrivial R] in
lemma coeff_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → CPolynomial R) (i : ℕ) :
    coeff (∑ x ∈ s, f x) i = ∑ x ∈ s, coeff (f x) i := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using (coeff_zero (R := R) (i := i))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

lemma coeff_C_mul_X_pow (c : R) :
    ∀ n i : ℕ, coeff (C c * X ^ n) i = if i = n then c else 0
  | 0, i => by
      rw [pow_zero, coeff_C_mul]
      rw [coeff_one]
      split_ifs <;> simp [*]
  | n + 1, 0 => by
      rw [pow_succ, ← mul_assoc, coeff_mul_X_zero]
      simp
  | n + 1, i + 1 => by
      rw [pow_succ, ← mul_assoc, coeff_mul_X_succ]
      simpa using coeff_C_mul_X_pow c n i

end CPolynomial

end CompPoly

namespace CPoly

namespace CMvPolynomial

open CompPoly

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

private def x0 : Fin 1 := ⟨0, by decide⟩

/-- The monomial `X^n` viewed in `CMvPolynomial 1`. -/
def univariateMonomial (n : ℕ) : CMvMonomial 1 :=
  Vector.ofFn (fun _ : Fin 1 => n)

private lemma singleFinsupp_eq (m : Fin 1 →₀ ℕ) :
    m = Finsupp.single x0 (m x0) := by
  apply Finsupp.ext
  intro j
  fin_cases j
  simp [x0]

private lemma singleMonomial_eq (m : CMvMonomial 1) :
    m = univariateMonomial (m.get x0) := by
  apply CMvMonomial.ext
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  rfl

private lemma singleMonomial_eq_ofFinsupp (i : ℕ) :
    univariateMonomial i = CMvMonomial.ofFinsupp (Finsupp.single x0 i) := by
  apply CMvMonomial.ext
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  change i = (Finsupp.single x0 i) x0
  simp [x0]

private lemma singleFinsupp_eq_of_apply_eq {m : Fin 1 →₀ ℕ} {n : ℕ} (h : m x0 = n) :
    m = Finsupp.single x0 n := by
  calc
    m = Finsupp.single x0 (m x0) := singleFinsupp_eq m
    _ = Finsupp.single x0 n := by rw [h]

private def cRingHom : R →+* CMvPolynomial 1 R where
  toFun := CMvPolynomial.C (n := 1)
  map_zero' := by
    exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_zero
  map_one' := by
    exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_one
  map_add' x y := by
    exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_add x y
  map_mul' x y := by
    exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_mul x y

/-- Interpret a sparse one-variable multivariate polynomial as a canonical univariate polynomial. -/
def toUnivariate (p : CMvPolynomial 1 R) : CompPoly.CPolynomial R :=
  eval₂ (CompPoly.CPolynomial.CRingHom (R := R)) (fun _ => CompPoly.CPolynomial.X) p

/-- Interpret a canonical univariate polynomial as a sparse one-variable multivariate polynomial. -/
def ofUnivariate (p : CompPoly.CPolynomial R) : CMvPolynomial 1 R :=
  CompPoly.CPolynomial.eval₂
    cRingHom
    (CMvPolynomial.X (R := R) x0) p

lemma toUnivariate_add (p q : CMvPolynomial 1 R) :
    toUnivariate (p + q) = toUnivariate p + toUnivariate q := by
  simpa [toUnivariate, CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom
      (S := CompPoly.CPolynomial R)
      (CompPoly.CPolynomial.CRingHom (R := R))
      (fun _ => CompPoly.CPolynomial.X)).map_add p q

lemma toUnivariate_mul (p q : CMvPolynomial 1 R) :
    toUnivariate (p * q) = toUnivariate p * toUnivariate q := by
  simpa [toUnivariate, CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom
      (S := CompPoly.CPolynomial R)
      (CompPoly.CPolynomial.CRingHom (R := R))
      (fun _ => CompPoly.CPolynomial.X)).map_mul p q

private lemma toUnivariate_eq_support_sum (p : CMvPolynomial 1 R) :
    toUnivariate p =
      (fromCMvPolynomial p).support.sum
        (fun m =>
          CompPoly.CPolynomial.C ((fromCMvPolynomial p).coeff m) *
            CompPoly.CPolynomial.X ^ m x0) := by
  unfold toUnivariate CMvPolynomial.eval₂
  simp [CompPoly.CPolynomial.CRingHom_apply]
  rw [foldl_eq_sum
      (t := p)
      (f := fun m c =>
        CompPoly.CPolynomial.C c *
          MonoR.evalMonomial (fun _ => CompPoly.CPolynomial.X) m)]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp [MonoR.evalMonomial, CMvMonomial.ofFinsupp, x0, MvPolynomial.coeff]

omit [Nontrivial R] in
private lemma coeff_singleMonomial_C_mul_X_pow (c : R) (n i : ℕ) :
    CMvPolynomial.coeff (univariateMonomial i)
      (CMvPolynomial.C (n := 1) c * (CMvPolynomial.X (R := R) x0) ^ n) =
        if i = n then c else 0 := by
  rw [singleMonomial_eq_ofFinsupp]
  rw [← coeff_eq
    (a := CMvPolynomial.C (n := 1) c * (CMvPolynomial.X (R := R) x0) ^ n)
    (m := Finsupp.single x0 i)]
  have hpow :
      fromCMvPolynomial ((CMvPolynomial.X (R := R) x0 : CMvPolynomial 1 R) ^ n) =
        (MvPolynomial.X x0 : MvPolynomial (Fin 1) R) ^ n := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [pow_succ, CPoly.map_mul, ih, fromCMvPolynomial_X, pow_succ]
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C, hpow]
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  simp [x0, eq_comm]

omit [Nontrivial R] in
private lemma ofUnivariate_eq_support_sum (p : CompPoly.CPolynomial R) :
    ofUnivariate p =
      p.support.sum
        (fun i =>
          CMvPolynomial.C (n := 1) (CompPoly.CPolynomial.coeff p i) *
            (CMvPolynomial.X (R := R) x0) ^ i) := by
  unfold ofUnivariate
  simpa [CompPoly.CPolynomial.CRingHom_apply] using
    (CompPoly.CPolynomial.eval₂_eq_sum_support
      (p := p)
      (f := cRingHom)
      (x := CMvPolynomial.X (R := R) x0))

lemma coeff_toUnivariate (p : CMvPolynomial 1 R) (i : ℕ) :
    CompPoly.CPolynomial.coeff (toUnivariate p) i =
      CMvPolynomial.coeff (univariateMonomial i) p := by
  rw [toUnivariate_eq_support_sum, CompPoly.CPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (Finsupp.single x0 i)]
  · rw [CompPoly.CPolynomial.coeff_C_mul_X_pow]
    simp [coeff_eq, x0, singleMonomial_eq_ofFinsupp]
  · intro m hm hne
    have hmi : m x0 ≠ i := by
      intro h
      apply hne
      exact singleFinsupp_eq_of_apply_eq h
    rw [CompPoly.CPolynomial.coeff_C_mul_X_pow]
    by_cases him : i = m x0
    · exfalso
      exact hmi him.symm
    · simp [him]
  · intro hnot
    have hcoeff0 : (fromCMvPolynomial p).coeff (Finsupp.single x0 i) = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hnot
    rw [CompPoly.CPolynomial.coeff_C_mul_X_pow]
    simp [hcoeff0]

omit [Nontrivial R] in
lemma coeff_ofUnivariate (p : CompPoly.CPolynomial R) (i : ℕ) :
    CMvPolynomial.coeff (univariateMonomial i) (ofUnivariate p) =
      CompPoly.CPolynomial.coeff p i := by
  rw [ofUnivariate_eq_support_sum]
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · rw [coeff_singleMonomial_C_mul_X_pow]
    simp
  · intro j _ hne
    rw [coeff_singleMonomial_C_mul_X_pow]
    by_cases hij : i = j
    · exfalso
      exact hne hij.symm
    · simp [hij]
  · intro hnot
    have hcoeff0 : CompPoly.CPolynomial.coeff p i = 0 := by
      by_contra hne
      exact hnot ((CompPoly.CPolynomial.mem_support_iff p i).2 hne)
    rw [coeff_singleMonomial_C_mul_X_pow]
    simp [hcoeff0]

@[simp]
lemma toUnivariate_ofUnivariate (p : CompPoly.CPolynomial R) :
    toUnivariate (ofUnivariate p) = p := by
  apply CompPoly.CPolynomial.eq_iff_coeff.2
  intro i
  rw [coeff_toUnivariate, coeff_ofUnivariate]

@[simp]
lemma ofUnivariate_toUnivariate (p : CMvPolynomial 1 R) :
    ofUnivariate (toUnivariate p) = p := by
  ext m
  let i := m.get x0
  have h :
      CMvPolynomial.coeff (univariateMonomial i) (ofUnivariate (toUnivariate p)) =
        CMvPolynomial.coeff (univariateMonomial i) p := by
    rw [coeff_ofUnivariate, coeff_toUnivariate]
  have hm : m = univariateMonomial i := by
    dsimp [i]
    exact singleMonomial_eq m
  simpa [hm] using h

/-- Direct computable ring equivalence between sparse one-variable multivariate polynomials
and canonical univariate polynomials. -/
def univariateRingEquiv : CMvPolynomial 1 R ≃+* CompPoly.CPolynomial R where
  toFun := toUnivariate
  invFun := ofUnivariate
  left_inv := ofUnivariate_toUnivariate
  right_inv := toUnivariate_ofUnivariate
  map_mul' := toUnivariate_mul
  map_add' := toUnivariate_add

end CMvPolynomial

end CPoly
