/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Common
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Combinations

/-!
# Lee-O'Sullivan Basis Correctness Helpers

Multiplicity, triangularity, and algebraic closure facts for Lee-O'Sullivan basis polynomials.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace LeeOSullivan

open PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

theorem foldl_range_add_eq_sum {α : Type*} [AddCommMonoid α]
    (f : Nat → α) :
    ∀ n, (List.range n).foldl (fun acc i ↦ acc + f i) 0 =
      ∑ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

theorem cpoly_natDegree_mul_le_semiring {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] (P Q : CPolynomial R) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul_le

theorem cpoly_natDegree_pow_le {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P : CPolynomial R) {d : Nat} (hP : P.natDegree ≤ d) :
    ∀ n, (P ^ n).natDegree ≤ n * d := by
  intro n
  induction n with
  | zero =>
      rw [pow_zero, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one]
      simp
  | succ n ih =>
      rw [pow_succ]
      calc
        (P ^ n * P).natDegree ≤ (P ^ n).natDegree + P.natDegree :=
          cpoly_natDegree_mul_le_semiring (P ^ n) P
        _ ≤ n * d + d := Nat.add_le_add ih hP
        _ = (n + 1) * d := by rw [Nat.succ_mul]

private theorem cbivariate_Y_eq_outer_X :
    (CBivariate.Y : CBivariate F) = (CPolynomial.X : CBivariate F) := by
  have h := CPolynomial.C_mul_X_pow_eq_monomial
    (R := CPolynomial F) (r := (1 : CPolynomial F)) (n := 1)
  have hC :
      (CPolynomial.C (1 : CPolynomial F) : CPolynomial (CPolynomial F)) = 1 := by
    apply (CPolynomial.eq_iff_coeff).mpr
    intro i
    rw [CPolynomial.coeff_C, CPolynomial.coeff_one]
  have hCinner : (CPolynomial.C (1 : F) : CPolynomial F) = 1 := by
    apply (CPolynomial.eq_iff_coeff).mpr
    intro i
    rw [CPolynomial.coeff_C, CPolynomial.coeff_one]
  rw [pow_one, hC, CPolynomial.one_mul] at h
  simpa [CBivariate.Y, hCinner] using h.symm

private theorem coeff_Y_mul_zero
    (Q : CBivariate F) (i : Nat) :
    CBivariate.coeff ((CBivariate.Y : CBivariate F) * Q) i 0 = 0 := by
  have houter :
      CPolynomial.coeff (((CBivariate.Y : CBivariate F) * Q : CBivariate F)) 0 =
        0 := by
    rw [cbivariate_Y_eq_outer_X]
    exact CPolynomial.coeff_X_mul_zero (R := CPolynomial F) (p := Q)
  change CPolynomial.coeff
    (CPolynomial.coeff (((CBivariate.Y : CBivariate F) * Q : CBivariate F)) 0) i = 0
  rw [houter, CPolynomial.coeff_zero]

private theorem coeff_Y_mul_succ
    (Q : CBivariate F) (i j : Nat) :
    CBivariate.coeff ((CBivariate.Y : CBivariate F) * Q) i (j + 1) =
      CBivariate.coeff Q i j := by
  have houter :
      CPolynomial.coeff (((CBivariate.Y : CBivariate F) * Q : CBivariate F)) (j + 1) =
        CPolynomial.coeff Q j := by
    rw [cbivariate_Y_eq_outer_X]
    exact CPolynomial.coeff_X_mul_succ (R := CPolynomial F) (p := Q) (n := j)
  change CPolynomial.coeff
    (CPolynomial.coeff (((CBivariate.Y : CBivariate F) * Q : CBivariate F)) (j + 1)) i =
      CPolynomial.coeff (CPolynomial.coeff Q j) i
  rw [houter]

private theorem evalEval_Y_mul
    (x y : F) (Q : CBivariate F) :
    CBivariate.evalEval x y ((CBivariate.Y : CBivariate F) * Q) =
      y * CBivariate.evalEval x y Q := by
  rw [CBivariate.evalEval_toPoly, CBivariate.evalEval_toPoly, CBivariate.toPoly_mul,
    CBivariate.Y_toPoly]
  simp [Polynomial.evalEval]

private theorem hasseDerivative_Y_mul_zero_yOrder
    (a : Nat) (Q : CBivariate F) :
    CBivariate.hasseDerivative a 0 ((CBivariate.Y : CBivariate F) * Q) =
      (CBivariate.Y : CBivariate F) * CBivariate.hasseDerivative a 0 Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  cases j with
  | zero =>
      rw [CBivariate.hasseDerivative_coeff, coeff_Y_mul_zero, coeff_Y_mul_zero]
      simp
  | succ j =>
      rw [CBivariate.hasseDerivative_coeff, coeff_Y_mul_succ, coeff_Y_mul_succ,
        CBivariate.hasseDerivative_coeff]
      simp

private theorem hasseDerivative_Y_mul_succ_yOrder
    (a b : Nat) (Q : CBivariate F) :
    CBivariate.hasseDerivative a (b + 1) ((CBivariate.Y : CBivariate F) * Q) =
      (CBivariate.Y : CBivariate F) * CBivariate.hasseDerivative a (b + 1) Q +
        CBivariate.hasseDerivative a b Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  cases j with
  | zero =>
      rw [CBivariate.hasseDerivative_coeff, CBivariate.coeff_add,
        coeff_Y_mul_zero, CBivariate.hasseDerivative_coeff]
      rw [show 0 + (b + 1) = b.succ by omega]
      rw [coeff_Y_mul_succ]
      rw [show b + 1 = b.succ by omega, Nat.choose_self]
      rw [show 0 + b = b by omega, Nat.choose_self]
      ring
  | succ j =>
      rw [CBivariate.hasseDerivative_coeff, CBivariate.coeff_add]
      rw [show j + 1 + (b + 1) = (j + b + 1) + 1 by omega]
      rw [coeff_Y_mul_succ, coeff_Y_mul_succ]
      rw [CBivariate.hasseDerivative_coeff, CBivariate.hasseDerivative_coeff]
      rw [show j + (b + 1) = j + b + 1 by omega]
      rw [show j + 1 + b = j + b + 1 by omega]
      rw [Nat.choose_succ_succ]
      norm_num
      ring_nf

private theorem hasseDerivativeEval_Y_mul_zero_yOrder
    (a : Nat) (x y : F) (Q : CBivariate F) :
    CBivariate.hasseDerivativeEval a 0 x y
        ((CBivariate.Y : CBivariate F) * Q) =
      y * CBivariate.hasseDerivativeEval a 0 x y Q := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [hasseDerivative_Y_mul_zero_yOrder]
  rw [evalEval_Y_mul]
  rw [CBivariate.hasseDerivative_eval_eq_eval]

private theorem hasseDerivativeEval_Y_mul_succ_yOrder
    (a b : Nat) (x y : F) (Q : CBivariate F) :
    CBivariate.hasseDerivativeEval a (b + 1) x y
        ((CBivariate.Y : CBivariate F) * Q) =
      y * CBivariate.hasseDerivativeEval a (b + 1) x y Q +
        CBivariate.hasseDerivativeEval a b x y Q := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [hasseDerivative_Y_mul_succ_yOrder]
  rw [CBivariate.evalEval_add, evalEval_Y_mul]
  rw [CBivariate.hasseDerivative_eval_eq_eval,
    CBivariate.hasseDerivative_eval_eq_eval]

private theorem linearYDivisor_eq_Y_sub_ofYConstant
    (R : CPolynomial F) :
    CBivariate.linearYDivisor R =
      (CBivariate.Y : CBivariate F) - CBivariate.ofYConstant R := by
  rw [CBivariate.linearYDivisor, CBivariate.ofYConstant]
  rw [cbivariate_Y_eq_outer_X]
  rfl

theorem hasMultiplicityAtLeast_Y_mul
    {P : CBivariate F} {x y : F} {m : Nat}
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast
      ((CBivariate.Y : CBivariate F) * P) x y m := by
  intro a b hab
  cases b with
  | zero =>
      rw [hasseDerivativeEval_Y_mul_zero_yOrder]
      rw [hP a 0 hab]
      simp
  | succ b =>
      rw [hasseDerivativeEval_Y_mul_succ_yOrder]
      rw [hP a (b + 1) hab]
      have hprev : CBivariate.hasseDerivativeEval a b x y P = 0 := by
        exact hP a b (by omega)
      rw [hprev]
      simp

theorem hasMultiplicityAtLeast_ofYConstant_mul_eval_zero
    (A : CPolynomial F) {P : CBivariate F} {x y : F} {m : Nat}
    (hEval : CPolynomial.eval x A = 0)
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast (CBivariate.ofYConstant A * P) x y (m + 1) := by
  intro a b hab
  rw [hasseDerivativeEval_ofYConstant_mul_eq_eval_mul_of_lower x y b A P a]
  · rw [hEval]
    simp
  · intro a' ha'
    exact hP a' b (by omega)

theorem hasMultiplicityAtLeast_linearYDivisor_mul
    (R : CPolynomial F) {P : CBivariate F} {x y : F} {m : Nat}
    (hEval : CPolynomial.eval x R = y)
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast
      (CBivariate.linearYDivisor R * P) x y (m + 1) := by
  intro a b hab
  rw [linearYDivisor_eq_Y_sub_ofYConstant, sub_mul,
    CBivariate.hasseDerivativeEval_sub]
  cases b with
  | zero =>
      rw [hasseDerivativeEval_Y_mul_zero_yOrder]
      rw [hasseDerivativeEval_ofYConstant_mul_eq_eval_mul_of_lower x y 0 R P a]
      · rw [hEval]
        ring
      · intro a' ha'
        exact hP a' 0 (by omega)
  | succ b =>
      rw [hasseDerivativeEval_Y_mul_succ_yOrder]
      rw [hasseDerivativeEval_ofYConstant_mul_eq_eval_mul_of_lower x y (b + 1) R P a]
      · have hprev : CBivariate.hasseDerivativeEval a b x y P = 0 := by
          exact hP a b (by omega)
        rw [hEval, hprev]
        ring
      · intro a' ha'
        exact hP a' (b + 1) (by omega)

theorem hasMultiplicityAtLeast_one_zero
    (x y : F) :
    CBivariate.HasMultiplicityAtLeast (1 : CBivariate F) x y 0 := by
  intro a b hab
  omega

theorem hasMultiplicityAtLeast_Y_pow_mul
    (n : Nat) {P : CBivariate F} {x y : F} {m : Nat}
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast
      ((CBivariate.Y : CBivariate F) ^ n * P) x y m := by
  induction n generalizing P with
  | zero =>
      simpa using hP
  | succ n ih =>
      rw [pow_succ, mul_assoc]
      exact ih (hasMultiplicityAtLeast_Y_mul hP)

theorem hasMultiplicityAtLeast_ofYConstant_pow_mul_eval_zero
    (A : CPolynomial F) (n : Nat) {P : CBivariate F} {x y : F} {m : Nat}
    (hEval : CPolynomial.eval x A = 0)
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast
      ((CBivariate.ofYConstant A) ^ n * P) x y (m + n) := by
  induction n generalizing P m with
  | zero =>
      simpa using hP
  | succ n ih =>
      rw [pow_succ, mul_assoc]
      have hnext :
          CBivariate.HasMultiplicityAtLeast
            (CBivariate.ofYConstant A * P) x y (m + 1) :=
        hasMultiplicityAtLeast_ofYConstant_mul_eval_zero A hEval hP
      have hrec :=
        ih (P := CBivariate.ofYConstant A * P) (m := m + 1) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

theorem hasMultiplicityAtLeast_linearYDivisor_pow_mul
    (R : CPolynomial F) (n : Nat) {P : CBivariate F} {x y : F} {m : Nat}
    (hEval : CPolynomial.eval x R = y)
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast
      ((CBivariate.linearYDivisor R) ^ n * P) x y (m + n) := by
  induction n generalizing P m with
  | zero =>
      simpa using hP
  | succ n ih =>
      rw [pow_succ, mul_assoc]
      have hnext :
          CBivariate.HasMultiplicityAtLeast
            (CBivariate.linearYDivisor R * P) x y (m + 1) :=
        hasMultiplicityAtLeast_linearYDivisor_mul R hEval hP
      have hrec :=
        ih (P := CBivariate.linearYDivisor R * P) (m := m + 1) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

theorem leeOSullivanBasisPolynomial_hasMultiplicityAtLeast
    (R G : CPolynomial F) (params : GSInterpParams) (idx : Nat)
    {x y : F}
    (hR : CPolynomial.eval x R = y)
    (hG : CPolynomial.eval x G = 0) :
    CBivariate.HasMultiplicityAtLeast
      (leeOSullivanBasisPolynomial R G params idx) x y params.multiplicity := by
  let t := leeOSullivanT params idx
  let yPow := idx - t
  let gPow := params.multiplicity - t
  have ht : t ≤ params.multiplicity := by
    simp [t, leeOSullivanT]
  have hbase :
      CBivariate.HasMultiplicityAtLeast
        ((CBivariate.ofYConstant G) ^ gPow * (1 : CBivariate F)) x y gPow := by
    simpa using
      hasMultiplicityAtLeast_ofYConstant_pow_mul_eval_zero
        G gPow hG (hasMultiplicityAtLeast_one_zero (F := F) x y)
  have hlinear :
      CBivariate.HasMultiplicityAtLeast
        ((CBivariate.linearYDivisor R) ^ t *
          ((CBivariate.ofYConstant G) ^ gPow * (1 : CBivariate F)))
        x y params.multiplicity := by
    have hraw :=
      hasMultiplicityAtLeast_linearYDivisor_pow_mul
        R t hR hbase
    simpa [gPow, t, Nat.sub_add_cancel ht] using hraw
  have hY :
      CBivariate.HasMultiplicityAtLeast
        ((CBivariate.Y : CBivariate F) ^ yPow *
          ((CBivariate.linearYDivisor R) ^ t *
            ((CBivariate.ofYConstant G) ^ gPow * (1 : CBivariate F))))
        x y params.multiplicity :=
    hasMultiplicityAtLeast_Y_pow_mul yPow hlinear
  simpa [leeOSullivanBasisPolynomial, t, yPow, gPow, mul_assoc] using hY

theorem leeOSullivanBasisPolynomial_satisfiesMultiplicityConstraints
    (R G : CPolynomial F) (params : GSInterpParams) (idx : Nat)
    {points : Array (F × F)}
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2)
    (hG : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 G = 0) :
    CBivariate.SatisfiesMultiplicityConstraints
      (leeOSullivanBasisPolynomial R G params idx) points params.multiplicity := by
  intro point hpoint
  exact leeOSullivanBasisPolynomial_hasMultiplicityAtLeast R G params idx
    (hR point hpoint) (hG point hpoint)

theorem leeOSullivanBasisPolynomials_satisfiesMultiplicityConstraints
    (R G : CPolynomial F) (params : GSInterpParams)
    {points : Array (F × F)}
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2)
    (hG : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 G = 0) :
    ∀ idx, idx < (leeOSullivanBasisPolynomials (F := F) R G params).size →
      CBivariate.SatisfiesMultiplicityConstraints
        ((leeOSullivanBasisPolynomials (F := F) R G params).getD idx 0)
        points params.multiplicity := by
  intro idx hidx
  rw [leeOSullivanBasisPolynomials_getD_of_lt R G params
    (by simpa [leeOSullivanBasisPolynomials_size] using hidx)]
  exact leeOSullivanBasisPolynomial_satisfiesMultiplicityConstraints
    R G params idx hR hG

omit [DecidableEq F] in
theorem ofYConstant_one :
    CBivariate.ofYConstant (1 : CPolynomial F) = (1 : CBivariate F) := by
  apply cpoly_eq_of_toPoly_eq
  change (CPolynomial.C (1 : CPolynomial F)).toPoly =
    (1 : CPolynomial (CPolynomial F)).toPoly
  rw [CPolynomial.C_toPoly, CPolynomial.toPoly_one]
  rfl

omit [DecidableEq F] in
theorem ofYConstant_pow
    (P : CPolynomial F) :
    ∀ n, CBivariate.ofYConstant (P ^ n) =
      (CBivariate.ofYConstant P : CBivariate F) ^ n
  | 0 => by
      rw [pow_zero, pow_zero, ofYConstant_one]
  | n + 1 => by
      rw [pow_succ, pow_succ, ofYConstant_mul, ofYConstant_pow P n]

omit [DecidableEq F] in
theorem coeff_ofYConstant_mul_outer
    (A : CPolynomial F) (P : CBivariate F) (j : Nat) :
    CPolynomial.coeff (CBivariate.ofYConstant A * P) j =
      A * CPolynomial.coeff P j := by
  unfold CBivariate.ofYConstant
  exact CPolynomial.coeff_C_mul (p := P) (c := A) j

private theorem leeOSullivanT_le_idx (params : GSInterpParams) (idx : Nat) :
    leeOSullivanT params idx ≤ idx := by
  simp [leeOSullivanT]

private theorem leeOSullivanBasisPolynomial_monicPart_coeffY_self
    (R : CPolynomial F) (params : GSInterpParams) (idx : Nat) :
    CPolynomial.coeff
        ((CBivariate.Y : CBivariate F) ^ (idx - leeOSullivanT params idx) *
          (CBivariate.linearYDivisor R) ^ leeOSullivanT params idx)
        idx =
      1 := by
  let t := leeOSullivanT params idx
  have ht : t ≤ idx := leeOSullivanT_le_idx params idx
  have hYtoPoly :
      CPolynomial.toPoly (CBivariate.Y : CBivariate F) =
        (Polynomial.X : Polynomial (CPolynomial F)) := by
    rw [cbivariate_Y_eq_outer_X]
    exact CPolynomial.X_toPoly
  have hXmonic :
      (((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t))).Monic :=
    Polynomial.monic_X_pow (idx - t)
  have hXnat :
      (((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t))).natDegree =
        idx - t := by
    simp
  have hLmonic :
      (((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R)).Monic :=
    Polynomial.monic_X_sub_C R
  have hLpowMonic :
      ((((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t)).Monic :=
    hLmonic.pow t
  have hLnat :
      ((((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t)).natDegree =
        t := by
    simpa [Polynomial.natDegree_X_sub_C] using hLmonic.natDegree_pow t
  have hprodMonic :
      ((((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t)) *
        (((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t))).Monic :=
    hXmonic.mul hLpowMonic
  have hprodNat :
      ((((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t)) *
        (((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t))).natDegree =
        idx := by
    rw [hXmonic.natDegree_mul hLpowMonic, hXnat, hLnat]
    exact Nat.sub_add_cancel ht
  have hcoeff :
      ((((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t)) *
          (((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t))).coeff idx =
        1 := by
    have h := hprodMonic.coeff_natDegree
    rwa [hprodNat] at h
  have htoPoly :
      CPolynomial.toPoly
          ((CBivariate.Y : CBivariate F) ^ (idx - t) *
            (CBivariate.linearYDivisor R) ^ t) =
        ((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t)) *
          (((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t) := by
    have hmul := CPolynomial.toPoly_mul
      ((CBivariate.Y : CBivariate F) ^ (idx - t))
      ((CBivariate.linearYDivisor R : CBivariate F) ^ t)
    have hYpow := CPolynomial.toPoly_pow (CBivariate.Y : CBivariate F) (idx - t)
    have hLpow := CPolynomial.toPoly_pow (CBivariate.linearYDivisor R : CBivariate F) t
    have hYpow' :
        CPolynomial.toPoly ((CBivariate.Y : CBivariate F) ^ (idx - t)) =
          CPolynomial.toPoly (CBivariate.Y : CBivariate F) ^ (idx - t) := by
      simpa using hYpow
    have hLpow' :
        CPolynomial.toPoly ((CBivariate.linearYDivisor R : CBivariate F) ^ t) =
          CPolynomial.toPoly (CBivariate.linearYDivisor R : CBivariate F) ^ t := by
      simpa using hLpow
    change CPolynomial.toPoly
        ((CBivariate.Y : CBivariate F) ^ (idx - t) *
          (CBivariate.linearYDivisor R) ^ t) =
      CPolynomial.toPoly ((CBivariate.Y : CBivariate F) ^ (idx - t)) *
        CPolynomial.toPoly ((CBivariate.linearYDivisor R : CBivariate F) ^ t) at hmul
    rw [hYpow', hLpow', hYtoPoly, CBivariate.linearYDivisor_toPoly] at hmul
    exact hmul
  have hcoeffOuter :=
    congrArg (fun P : Polynomial (CPolynomial F) ↦ P.coeff idx) htoPoly
  have hcoeffOuter' :
      (CPolynomial.toPoly
          ((CBivariate.Y : CBivariate F) ^ (idx - t) *
            (CBivariate.linearYDivisor R) ^ t)).coeff idx =
        ((((Polynomial.X : Polynomial (CPolynomial F)) ^ (idx - t)) *
          (((Polynomial.X : Polynomial (CPolynomial F)) - Polynomial.C R) ^ t))).coeff idx := by
    simpa using hcoeffOuter
  rw [← CPolynomial.coeff_toPoly, hcoeff] at hcoeffOuter'
  simpa [t] using hcoeffOuter'

theorem leeOSullivanBasisPolynomial_coeffY_self
    (R G : CPolynomial F) (params : GSInterpParams) (idx : Nat) :
    CPolynomial.coeff (leeOSullivanBasisPolynomial R G params idx) idx =
      G ^ (params.multiplicity - leeOSullivanT params idx) := by
  let t := leeOSullivanT params idx
  let gPow := params.multiplicity - t
  let monicPart : CBivariate F :=
    (CBivariate.Y : CBivariate F) ^ (idx - t) *
      (CBivariate.linearYDivisor R) ^ t
  have hpow :
      (CBivariate.ofYConstant G : CBivariate F) ^ gPow =
        CBivariate.ofYConstant (G ^ gPow) := by
    exact (ofYConstant_pow G gPow).symm
  have hbasis :
      leeOSullivanBasisPolynomial R G params idx =
        CBivariate.ofYConstant (G ^ gPow) * monicPart := by
    rw [leeOSullivanBasisPolynomial, hpow]
    simp [monicPart, t, gPow]
    ring
  rw [hbasis, coeff_ofYConstant_mul_outer]
  rw [show CPolynomial.coeff monicPart idx = 1 by
    simpa [monicPart, t] using
      leeOSullivanBasisPolynomial_monicPart_coeffY_self R params idx]
  simp [gPow, t]

/-- Lee basis polynomials have no `Y` terms above their row index. -/
theorem leeOSullivanBasisPolynomial_coeffY_eq_zero_of_idx_lt
    (R G : CPolynomial F) (params : GSInterpParams) {idx j : Nat}
    (hj : idx < j) :
    CPolynomial.coeff (leeOSullivanBasisPolynomial R G params idx) j = 0 := by
  let t := leeOSullivanT params idx
  let Ypow : CBivariate F := (CBivariate.Y : CBivariate F) ^ (idx - t)
  let Lpow : CBivariate F := CBivariate.linearYDivisor R ^ t
  let Gpow : CBivariate F := CBivariate.ofYConstant G ^ (params.multiplicity - t)
  have hY : (CBivariate.Y : CBivariate F).natDegree ≤ 1 := by
    have hC : (CPolynomial.C (1 : F) : CPolynomial F) ≠ 0 := by
      intro h
      have hc := congrArg (fun p : CPolynomial F ↦ CPolynomial.coeff p 0) h
      change CPolynomial.coeff (CPolynomial.C (1 : F) : CPolynomial F) 0 =
        CPolynomial.coeff (0 : CPolynomial F) 0 at hc
      rw [CPolynomial.coeff_C, if_pos rfl, CPolynomial.coeff_zero] at hc
      exact one_ne_zero hc
    rw [CBivariate.Y, CPolynomial.natDegree_monomial hC]
  have hL : (CBivariate.linearYDivisor R : CBivariate F).natDegree ≤ 1 := by
    rw [CPolynomial.natDegree_toPoly, CBivariate.linearYDivisor_toPoly]
    simp
  have hG : (CBivariate.ofYConstant G : CBivariate F).natDegree ≤ 0 := by
    rw [CPolynomial.natDegree_toPoly]
    simp [CBivariate.ofYConstant, CPolynomial.C_toPoly]
  have hYpow : Ypow.natDegree ≤ idx - t := by
    simpa [Ypow] using
      cpoly_natDegree_pow_le (P := (CBivariate.Y : CBivariate F)) hY (idx - t)
  have hLpow : Lpow.natDegree ≤ t := by
    simpa [Lpow] using
      cpoly_natDegree_pow_le (P := (CBivariate.linearYDivisor R : CBivariate F)) hL t
  have hGpow : Gpow.natDegree ≤ 0 := by
    have hpow := cpoly_natDegree_pow_le
      (P := (CBivariate.ofYConstant G : CBivariate F)) hG
      (params.multiplicity - t)
    simpa [Gpow] using hpow
  have hprod :
      (Ypow * Lpow * Gpow).natDegree ≤ idx := by
    have hYL : (Ypow * Lpow).natDegree ≤ (idx - t) + t := by
      calc
        (Ypow * Lpow).natDegree ≤ Ypow.natDegree + Lpow.natDegree :=
          cpoly_natDegree_mul_le_semiring Ypow Lpow
        _ ≤ (idx - t) + t := Nat.add_le_add hYpow hLpow
    calc
      (Ypow * Lpow * Gpow).natDegree ≤ (Ypow * Lpow).natDegree + Gpow.natDegree :=
        cpoly_natDegree_mul_le_semiring (Ypow * Lpow) Gpow
      _ ≤ ((idx - t) + t) + 0 := Nat.add_le_add hYL hGpow
      _ ≤ idx := by
        have ht : t ≤ idx := by
          simp [t, leeOSullivanT]
        omega
  have hdegree :
      (Ypow * Lpow * Gpow).natDegree < j := lt_of_le_of_lt hprod hj
  have hcoeffY :
      (Ypow * Lpow * Gpow).val.coeff j = 0 := by
    exact cpoly_coeff_eq_zero_of_natDegree_lt hdegree
  rw [show leeOSullivanBasisPolynomial R G params idx = Ypow * Lpow * Gpow by
    simp [leeOSullivanBasisPolynomial, Ypow, Lpow, Gpow, t]]
  exact hcoeffY

omit [DecidableEq F] in
theorem ofYConstant_neg
    (P : CPolynomial F) :
    CBivariate.ofYConstant (-P) = -CBivariate.ofYConstant P := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [CBivariate.coeff_neg, coeff_ofYConstant, coeff_ofYConstant]
  by_cases hj : j = 0
  · subst j
    exact CPolynomial.coeff_neg (p := P) (i := i)
  · simp [hj]

omit [DecidableEq F] in
theorem ofYConstant_sub
    (P Q : CPolynomial F) :
    CBivariate.ofYConstant (P - Q) =
      CBivariate.ofYConstant P - CBivariate.ofYConstant Q := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ofYConstant_add, ofYConstant_neg]

/-- Multiplication by a `Y`-constant polynomial preserves multiplicity
constraints already satisfied by the bivariate factor. -/
theorem hasMultiplicityAtLeast_ofYConstant_mul
    (A : CPolynomial F) {P : CBivariate F} {x y : F} {m : Nat}
    (hP : CBivariate.HasMultiplicityAtLeast P x y m) :
    CBivariate.HasMultiplicityAtLeast (CBivariate.ofYConstant A * P) x y m := by
  intro a b hab
  exact hasseDerivativeEval_ofYConstant_mul_eq_zero_of_lower
    x y b A P a (by
      intro a' ha'
      exact hP a' b (by omega))

theorem hasMultiplicityAtLeast_sub
    {P Q : CBivariate F} {x y : F} {m : Nat}
    (hP : CBivariate.HasMultiplicityAtLeast P x y m)
    (hQ : CBivariate.HasMultiplicityAtLeast Q x y m) :
    CBivariate.HasMultiplicityAtLeast (P - Q) x y m := by
  intro a b hab
  rw [CBivariate.hasseDerivativeEval_sub, hP a b hab, hQ a b hab]
  simp

theorem satisfiesMultiplicityConstraints_sub
    {P Q : CBivariate F} {points : Array (F × F)} {m : Nat}
    (hP : CBivariate.SatisfiesMultiplicityConstraints P points m)
    (hQ : CBivariate.SatisfiesMultiplicityConstraints Q points m) :
    CBivariate.SatisfiesMultiplicityConstraints (P - Q) points m := by
  intro point hpoint
  exact hasMultiplicityAtLeast_sub (hP point hpoint) (hQ point hpoint)

end LeeOSullivan

end GuruswamiSudan

end CompPoly
