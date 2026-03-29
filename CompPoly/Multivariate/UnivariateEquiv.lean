/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Multivariate.FinSuccEquiv
import CompPoly.Multivariate.Operations
import CompPoly.Univariate.ToPoly.Impl

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
def cRingHom : R →+* CPolynomial R where
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
lemma cRingHom_apply (r : R) : cRingHom (R := R) r = C r := rfl

omit [Nontrivial R] in
/-- Coefficients commute with finite sums of canonical polynomials. -/
lemma coeff_sum {ι : Type*} (s : Finset ι) (f : ι → CPolynomial R) (i : ℕ) :
    coeff (∑ x ∈ s, f x) i = ∑ x ∈ s, coeff (f x) i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (coeff_zero (R := R) (i := i))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

/-- The coefficient of `C c * X^n` is `c` at degree `n` and zero elsewhere. -/
lemma coeff_c_mul_x_pow (c : R) :
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
      simpa using coeff_c_mul_x_pow c n i

end CPolynomial

end CompPoly

namespace CPoly

namespace CMvPolynomial

open CompPoly

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- The monomial `X^n` viewed in `CMvPolynomial 1`. -/
def univariateMonomial (n : ℕ) : CMvMonomial 1 :=
  Vector.ofFn (fun _ : Fin 1 ↦ n)

private lemma single_finsupp_eq (m : Fin 1 →₀ ℕ) :
    m = Finsupp.single 0 (m 0) := by
  apply Finsupp.ext
  intro j
  fin_cases j
  simp

private lemma single_monomial_eq (m : CMvMonomial 1) :
    m = univariateMonomial (m.get 0) := by
  apply CMvMonomial.ext
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  rfl

private lemma single_monomial_eq_of_finsupp (i : ℕ) :
    univariateMonomial i = CMvMonomial.ofFinsupp (Finsupp.single 0 i) := by
  apply CMvMonomial.ext
  intro j hj
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  change i = (Finsupp.single 0 i) 0
  simp

private lemma single_finsupp_eq_of_apply_eq {m : Fin 1 →₀ ℕ} {n : ℕ} (h : m 0 = n) :
    m = Finsupp.single 0 n := by
  calc
    m = Finsupp.single 0 (m 0) := single_finsupp_eq m
    _ = Finsupp.single 0 n := by rw [h]

/-- Interpret a sparse one-variable multivariate polynomial as a canonical univariate polynomial. -/
def toUnivariate (p : CMvPolynomial 1 R) : CompPoly.CPolynomial R :=
  eval₂ (CompPoly.CPolynomial.cRingHom (R := R)) (fun _ ↦ CompPoly.CPolynomial.X) p

/-- Interpret a canonical univariate polynomial as a sparse one-variable multivariate polynomial. -/
def ofUnivariate (p : CompPoly.CPolynomial R) : CMvPolynomial 1 R :=
  let cRingHom : R →+* CMvPolynomial 1 R := {
    toFun := CMvPolynomial.C (n := 1)
    map_zero' := by
      exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_zero
    map_one' := by
      exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_one
    map_add' := by
      intros x y
      exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_add x y
    map_mul' := by
      intros x y
      exact (CMvPolynomial.CRingHom (n := 1) (R := R)).map_mul x y
  }
  CompPoly.CPolynomial.eval₂ cRingHom (CMvPolynomial.X (R := R) 0) p

lemma to_univariate_add (p q : CMvPolynomial 1 R) :
    toUnivariate (p + q) = toUnivariate p + toUnivariate q := by
  simpa [toUnivariate, CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom
      (S := CompPoly.CPolynomial R)
      (CompPoly.CPolynomial.cRingHom (R := R))
      (fun _ ↦ CompPoly.CPolynomial.X)).map_add p q

lemma to_univariate_mul (p q : CMvPolynomial 1 R) :
    toUnivariate (p * q) = toUnivariate p * toUnivariate q := by
  simpa [toUnivariate, CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom
      (S := CompPoly.CPolynomial R)
      (CompPoly.CPolynomial.cRingHom (R := R))
      (fun _ ↦ CompPoly.CPolynomial.X)).map_mul p q

private lemma to_univariate_eq_support_sum (p : CMvPolynomial 1 R) :
    toUnivariate p =
      (fromCMvPolynomial p).support.sum
        (fun m ↦
          CompPoly.CPolynomial.C ((fromCMvPolynomial p).coeff m) *
            CompPoly.CPolynomial.X ^ m 0) := by
  unfold toUnivariate CMvPolynomial.eval₂
  simp [CompPoly.CPolynomial.cRingHom_apply]
  rw [foldl_eq_sum
      (t := p)
      (f := fun m c ↦
        CompPoly.CPolynomial.C c *
          MonoR.evalMonomial (fun _ ↦ CompPoly.CPolynomial.X) m)]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp [MonoR.evalMonomial, CMvMonomial.ofFinsupp, MvPolynomial.coeff]

omit [Nontrivial R] in
private lemma coeff_single_monomial_c_mul_x_pow (c : R) (n i : ℕ) :
    CMvPolynomial.coeff (univariateMonomial i)
      (CMvPolynomial.C (n := 1) c * (CMvPolynomial.X (R := R) 0) ^ n) =
        if i = n then c else 0 := by
  rw [single_monomial_eq_of_finsupp]
  rw [← coeff_eq
    (a := CMvPolynomial.C (n := 1) c * (CMvPolynomial.X (R := R) 0) ^ n)
    (m := Finsupp.single 0 i)]
  have hpow :
      fromCMvPolynomial ((CMvPolynomial.X (R := R) 0 : CMvPolynomial 1 R) ^ n) =
        (MvPolynomial.X 0 : MvPolynomial (Fin 1) R) ^ n := by
    show
      (CPoly.polyRingEquiv (n := 1) (R := R)).toRingHom
        ((CMvPolynomial.X (R := R) 0 : CMvPolynomial 1 R) ^ n) =
          (MvPolynomial.X 0 : MvPolynomial (Fin 1) R) ^ n
    rw [RingHom.map_pow]
    change fromCMvPolynomial (CMvPolynomial.X (R := R) 0) ^ n =
      (MvPolynomial.X 0 : MvPolynomial (Fin 1) R) ^ n
    rw [fromCMvPolynomial_X]
  rw [CPoly.map_mul, CMvPolynomial.fromCMvPolynomial_C, hpow]
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  simp [eq_comm]

omit [Nontrivial R] in
private lemma of_univariate_eq_support_sum (p : CompPoly.CPolynomial R) :
    ofUnivariate p =
      p.support.sum
        (fun i ↦
          CMvPolynomial.C (n := 1) (CompPoly.CPolynomial.coeff p i) *
            (CMvPolynomial.X (R := R) 0) ^ i) := by
  unfold ofUnivariate
  simpa using
    (CompPoly.CPolynomial.eval₂_eq_sum_support
      (p := p)
      (f := CMvPolynomial.CRingHom (n := 1) (R := R))
      (x := CMvPolynomial.X (R := R) 0))

lemma coeff_to_univariate (p : CMvPolynomial 1 R) (i : ℕ) :
    CompPoly.CPolynomial.coeff (toUnivariate p) i =
      CMvPolynomial.coeff (univariateMonomial i) p := by
  rw [to_univariate_eq_support_sum, CompPoly.CPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (Finsupp.single 0 i)]
  · rw [CompPoly.CPolynomial.coeff_c_mul_x_pow]
    simp [coeff_eq, single_monomial_eq_of_finsupp]
  · intro m hm hne
    have hmi : m 0 ≠ i := by
      intro h
      apply hne
      exact single_finsupp_eq_of_apply_eq h
    rw [CompPoly.CPolynomial.coeff_c_mul_x_pow]
    by_cases him : i = m 0
    · exfalso
      exact hmi him.symm
    · simp [him]
  · intro hnot
    have hcoeff0 : (fromCMvPolynomial p).coeff (Finsupp.single 0 i) = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hnot
    rw [CompPoly.CPolynomial.coeff_c_mul_x_pow]
    simp [hcoeff0]

omit [Nontrivial R] in
lemma coeff_of_univariate (p : CompPoly.CPolynomial R) (i : ℕ) :
    CMvPolynomial.coeff (univariateMonomial i) (ofUnivariate p) =
      CompPoly.CPolynomial.coeff p i := by
  rw [of_univariate_eq_support_sum]
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · rw [coeff_single_monomial_c_mul_x_pow]
    simp
  · intro j _ hne
    rw [coeff_single_monomial_c_mul_x_pow]
    by_cases hij : i = j
    · exfalso
      exact hne hij.symm
    · simp [hij]
  · intro hnot
    have hcoeff0 : CompPoly.CPolynomial.coeff p i = 0 := by
      by_contra hne
      exact hnot ((CompPoly.CPolynomial.mem_support_iff p i).2 hne)
    rw [coeff_single_monomial_c_mul_x_pow]
    simp [hcoeff0]

@[simp]
lemma to_univariate_of_univariate (p : CompPoly.CPolynomial R) :
    toUnivariate (ofUnivariate p) = p := by
  apply CompPoly.CPolynomial.eq_iff_coeff.2
  intro i
  rw [coeff_to_univariate, coeff_of_univariate]

@[simp]
lemma of_univariate_to_univariate (p : CMvPolynomial 1 R) :
    ofUnivariate (toUnivariate p) = p := by
  ext m
  let i := m.get 0
  have h :
      CMvPolynomial.coeff (univariateMonomial i) (ofUnivariate (toUnivariate p)) =
        CMvPolynomial.coeff (univariateMonomial i) p := by
    rw [coeff_of_univariate, coeff_to_univariate]
  have hm : m = univariateMonomial i := by
    dsimp [i]
    exact single_monomial_eq m
  simpa [hm] using h

/-- The direct forward map agrees with the existing `finSucc` transport path after converting
to Mathlib `Polynomial`. -/
private theorem to_univariate_to_poly_eq_fin_succ_composite (p : CMvPolynomial 1 R) :
    (CompPoly.CPolynomial.ringEquiv (R := R)) (toUnivariate p) =
      (Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R)))
        (CPoly.CMvPolynomial.finSuccEquiv (n := 0) (R := R) p) := by
  ext i
  change (toUnivariate p).toPoly.coeff i =
    ((Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R)))
      (CPoly.CMvPolynomial.finSuccEquiv (n := 0) (R := R) p)).coeff i
  rw [← CompPoly.CPolynomial.coeff_toPoly, coeff_to_univariate]
  simp [CPoly.CMvPolynomial.finSuccEquiv, CPoly.polynomialCMvPolyEquiv,
    CMvPolynomial.isEmptyRingEquiv, Polynomial.coeff_map]
  symm
  change MvPolynomial.isEmptyRingEquiv R (Fin 0)
      (((MvPolynomial.finSuccEquiv R 0) (CPoly.polyRingEquiv p)).coeff i) =
    coeff (univariateMonomial i) p
  rw [MvPolynomial.isEmptyRingEquiv_eq_coeff_zero]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  change MvPolynomial.coeff (Finsupp.cons i 0) (fromCMvPolynomial p) =
    coeff (univariateMonomial i) p
  rw [coeff_eq]
  have hcons : (Finsupp.cons i 0 : Fin 1 →₀ ℕ) = Finsupp.single 0 i := by
    ext j
    fin_cases j
    simp [Finsupp.cons]
  simp [hcons, single_monomial_eq_of_finsupp]

/-- Direct computable ring equivalence between sparse one-variable multivariate polynomials
and canonical univariate polynomials. -/
def univariateRingEquiv : CMvPolynomial 1 R ≃+* CompPoly.CPolynomial R where
  toFun := toUnivariate
  invFun := ofUnivariate
  left_inv := of_univariate_to_univariate
  right_inv := to_univariate_of_univariate
  map_mul' := to_univariate_mul
  map_add' := to_univariate_add

/-- The direct computable one-variable bridge agrees with the existing `finSucc` transport
composite. -/
theorem univariate_ring_equiv_eq_fin_succ_composite :
    univariateRingEquiv (R := R) =
      (CPoly.CMvPolynomial.finSuccEquiv (n := 0) (R := R)).trans
        ((Polynomial.mapEquiv (CMvPolynomial.isEmptyRingEquiv (R := R))).trans
          (CompPoly.CPolynomial.ringEquiv (R := R)).symm) := by
  apply RingEquiv.ext
  intro p
  apply (CompPoly.CPolynomial.ringEquiv (R := R)).injective
  simpa [univariateRingEquiv, RingEquiv.trans_apply] using
    to_univariate_to_poly_eq_fin_succ_composite (R := R) p

end CMvPolynomial

end CPoly
