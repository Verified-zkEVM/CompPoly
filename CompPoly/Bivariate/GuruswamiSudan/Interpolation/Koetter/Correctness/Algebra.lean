/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness
import CompPoly.Univariate.DivisionCorrectness
import Mathlib.Data.List.Range

/-!
# Koetter Correctness Algebra Helpers

Polynomial, Hasse-derivative, weighted-degree, and initial-basis lemmas used by
Koetter correctness.
-/

namespace CompPoly

theorem cpoly_eval_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (x : F) (P Q : CPolynomial F) :
    CPolynomial.eval x (P + Q) = CPolynomial.eval x P + CPolynomial.eval x Q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

theorem cpoly_eval_X {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] (x : F) :
    CPolynomial.eval x CPolynomial.X = x := by
  rw [CPolynomial.eval_toPoly, CPolynomial.X_toPoly, Polynomial.eval_X]

theorem cpoly_eval_X_mul_divX_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (x : F) (P : CPolynomial F) :
    CPolynomial.eval x P =
      x * CPolynomial.eval x (CPolynomial.divX P) + P.coeff 0 := by
  have hdecomp := CPolynomial.X_mul_divX_add (p := P)
  have heval := congrArg (fun Q : CPolynomial F ↦ CPolynomial.eval x Q) hdecomp
  change CPolynomial.eval x P =
    CPolynomial.eval x (CPolynomial.X * CPolynomial.divX P + CPolynomial.C (P.coeff 0))
      at heval
  rw [cpoly_eval_add, CPolynomial.eval_mul, cpoly_eval_X,
    CPolynomial.eval_C] at heval
  exact heval

theorem cpoly_eq_of_toPoly_eq {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] {P Q : CPolynomial F}
    (h : P.toPoly = Q.toPoly) :
    P = Q := by
  apply (CPolynomial.eq_iff_coeff (p := P) (q := Q)).2
  intro i
  have hcoeff := congrArg (fun p : Polynomial F ↦ p.coeff i) h
  change P.toPoly.coeff i = Q.toPoly.coeff i at hcoeff
  rwa [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly] at hcoeff

theorem cpoly_linearFactor_toPoly {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (x : F) :
    (CPolynomial.linearFactor x).toPoly = Polynomial.X - Polynomial.C x := by
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly]
  rw [sub_eq_add_neg, ← Polynomial.C_neg]
  ring

theorem cpoly_linearFactor_monic {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (x : F) :
    (CPolynomial.linearFactor x).monic = true := by
  rw [CPolynomial.monic_toPoly_iff, cpoly_linearFactor_toPoly]
  simp [Polynomial.Monic]

theorem cpoly_linearFactor_mul_divByMonic_eq_self_of_eval_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (x : F) (P : CPolynomial F)
    (hroot : CPolynomial.eval x P = 0) :
    CPolynomial.linearFactor x * P.divByMonic (CPolynomial.linearFactor x) = P := by
  apply cpoly_eq_of_toPoly_eq
  rw [CPolynomial.toPoly_mul,
    CPolynomial.divByMonic_toPoly_eq_divByMonic _ _
      (cpoly_linearFactor_monic x),
    cpoly_linearFactor_toPoly]
  apply Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
  simpa [Polynomial.IsRoot, CPolynomial.eval_toPoly] using hroot

theorem cpoly_coeff_eq_zero_of_natDegree_lt {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F] {P : CPolynomial F} {i : Nat}
    (h : P.natDegree < i) :
    P.coeff i = 0 := by
  by_contra hne
  exact (Nat.not_lt_of_ge (CPolynomial.le_natDegree_of_ne_zero hne)) h

theorem cpoly_natDegree_mul_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (P Q : CPolynomial F) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul_le

theorem cpoly_coeff_mul_natDegree_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (P Q : CPolynomial F) :
    (P * Q).coeff (P.natDegree + Q.natDegree) =
      P.leadingCoeff * Q.leadingCoeff := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
    Polynomial.coeff_mul_degree_add_degree,
    ← CPolynomial.leadingCoeff_toPoly, ← CPolynomial.leadingCoeff_toPoly]

namespace CBivariate

theorem coeff_neg {R : Type*}
    [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P : CBivariate R) (i j : Nat) :
    coeff (-P) i j = -coeff P i j := by
  change CPolynomial.coeff (CPolynomial.coeff (-P : CBivariate R) j) i =
    -CPolynomial.coeff (CPolynomial.coeff P j) i
  have houter : CPolynomial.coeff (-P : CBivariate R) j =
      -CPolynomial.coeff P j := by
    exact CPolynomial.coeff_neg (p := P) (i := j)
  rw [houter, CPolynomial.coeff_neg]

theorem coeff_sub {R : Type*}
    [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P Q : CBivariate R) (i j : Nat) :
    coeff (P - Q) i j = coeff P i j - coeff Q i j := by
  change CPolynomial.coeff (CPolynomial.coeff (P - Q : CBivariate R) j) i =
    CPolynomial.coeff (CPolynomial.coeff P j) i -
      CPolynomial.coeff (CPolynomial.coeff Q j) i
  have houter : CPolynomial.coeff (P - Q : CBivariate R) j =
      CPolynomial.coeff P j - CPolynomial.coeff Q j := by
    exact CPolynomial.coeff_sub (p := P) (q := Q) (i := j)
  rw [houter, CPolynomial.coeff_sub]

theorem coeff_CC_mul {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (c : R) (Q : CBivariate R) (i j : Nat) :
    coeff (CC c * Q) i j = c * coeff Q i j := by
  change CPolynomial.coeff (CPolynomial.coeff (CC c * Q : CBivariate R) j) i =
    c * CPolynomial.coeff (CPolynomial.coeff Q j) i
  have houter : CPolynomial.coeff (CC c * Q : CBivariate R) j =
      CPolynomial.C c * CPolynomial.coeff Q j := by
    exact CPolynomial.coeff_C_mul (p := Q) (c := CPolynomial.C c) j
  rw [houter, CPolynomial.coeff_C_mul]

theorem coeff_X_mul_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (j : Nat) :
    coeff (X * Q) 0 j = 0 := by
  change CPolynomial.coeff (CPolynomial.coeff (X * Q : CBivariate R) j) 0 = 0
  have houter : CPolynomial.coeff (X * Q : CBivariate R) j =
      CPolynomial.X * CPolynomial.coeff Q j := by
    exact CPolynomial.coeff_C_mul (p := Q) (c := CPolynomial.X) j
  rw [houter, CPolynomial.coeff_X_mul_zero]

theorem coeff_X_mul_succ {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (i j : Nat) :
    coeff (X * Q) (i + 1) j = coeff Q i j := by
  change CPolynomial.coeff (CPolynomial.coeff (X * Q : CBivariate R) j) (i + 1) =
    CPolynomial.coeff (CPolynomial.coeff Q j) i
  have houter : CPolynomial.coeff (X * Q : CBivariate R) j =
      CPolynomial.X * CPolynomial.coeff Q j := by
    exact CPolynomial.coeff_C_mul (p := Q) (c := CPolynomial.X) j
  rw [houter, CPolynomial.coeff_X_mul_succ]

theorem evalEval_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (P Q : CBivariate F) :
    evalEval x y (P - Q) = evalEval x y P - evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, evalEval_toPoly]
  have hsub : toPoly (P - Q) = toPoly P - toPoly Q := by
    simpa [ringEquiv] using (ringEquiv (R := F)).map_sub P Q
  rw [hsub]
  simp [Polynomial.evalEval]

theorem evalEval_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c x y : F) (Q : CBivariate F) :
    evalEval x y (CC c * Q) = c * evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, toPoly_mul, CC_toPoly]
  simp [Polynomial.evalEval]

theorem evalEval_X_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (Q : CBivariate F) :
    evalEval x y (X * Q) = x * evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, toPoly_mul, X_toPoly]
  simp [Polynomial.evalEval]

theorem hasseDerivative_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (P Q : CBivariate F) :
    hasseDerivative a b (P - Q) =
      hasseDerivative a b P - hasseDerivative a b Q := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff, coeff_sub, coeff_sub, hasseDerivative_coeff,
    hasseDerivative_coeff]
  ring

theorem hasseDerivative_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (a b : Nat) (Q : CBivariate F) :
    hasseDerivative a b (CC c * Q) = CC c * hasseDerivative a b Q := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff, coeff_CC_mul, coeff_CC_mul, hasseDerivative_coeff]
  ring

theorem hasseDerivative_X_mul_zero_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (b : Nat) (Q : CBivariate F) :
    hasseDerivative 0 b (X * Q) = X * hasseDerivative 0 b Q := by
  rw [eq_iff_coeff]
  intro i j
  cases i with
  | zero =>
      rw [hasseDerivative_coeff, coeff_X_mul_zero, coeff_X_mul_zero]
      simp
  | succ i =>
      rw [hasseDerivative_coeff, coeff_X_mul_succ, coeff_X_mul_succ,
        hasseDerivative_coeff]
      simp

theorem hasseDerivative_X_mul_succ_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (Q : CBivariate F) :
    hasseDerivative (a + 1) b (X * Q) =
      X * hasseDerivative (a + 1) b Q + hasseDerivative a b Q := by
  rw [eq_iff_coeff]
  intro i j
  cases i with
  | zero =>
      rw [hasseDerivative_coeff, coeff_add, coeff_X_mul_zero, hasseDerivative_coeff]
      rw [show 0 + (a + 1) = a.succ by omega]
      rw [coeff_X_mul_succ]
      rw [show a + 1 = a.succ by omega, Nat.choose_self]
      rw [show 0 + a = a by omega, Nat.choose_self]
      ring
  | succ i =>
      rw [hasseDerivative_coeff, coeff_add, coeff_X_mul_succ,
        hasseDerivative_coeff, hasseDerivative_coeff]
      have hX :
          coeff (X * Q) (i + 1 + (a + 1)) (j + b) =
            coeff Q (i + (a + 1)) (j + b) := by
        convert coeff_X_mul_succ (Q := Q) (i + a + 1) (j + b) using 2
        omega
      rw [hX]
      rw [show i + 1 + (a + 1) = (i + a + 1).succ by omega]
      rw [show i + (a + 1) = i + a + 1 by omega]
      rw [show i + 1 + a = i + a + 1 by omega]
      rw [Nat.choose_succ_succ]
      norm_num
      ring_nf

theorem hasseDerivativeEval_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (x y : F) (P Q : CBivariate F) :
    hasseDerivativeEval a b x y (P - Q) =
      hasseDerivativeEval a b x y P - hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (P - Q)]
  rw [hasseDerivative_sub]
  rw [evalEval_sub]
  rw [hasseDerivative_eval_eq_eval, hasseDerivative_eval_eq_eval]

theorem hasseDerivativeEval_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (a b : Nat) (x y : F) (Q : CBivariate F) :
    hasseDerivativeEval a b x y (CC c * Q) =
      c * hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (CC c * Q)]
  rw [hasseDerivative_CC_mul]
  rw [evalEval_CC_mul]
  rw [hasseDerivative_eval_eq_eval]

theorem hasseDerivativeEval_X_mul_zero_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (b : Nat) (x y : F) (Q : CBivariate F) :
    hasseDerivativeEval 0 b x y (X * Q) =
      x * hasseDerivativeEval 0 b x y Q := by
  rw [← hasseDerivative_eval_eq_eval 0 b x y (X * Q)]
  rw [hasseDerivative_X_mul_zero_xOrder]
  rw [evalEval_X_mul]
  rw [hasseDerivative_eval_eq_eval]

theorem hasseDerivativeEval_X_mul_succ_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (x y : F) (Q : CBivariate F) :
    hasseDerivativeEval (a + 1) b x y (X * Q) =
      x * hasseDerivativeEval (a + 1) b x y Q +
        hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval (a + 1) b x y (X * Q)]
  rw [hasseDerivative_X_mul_succ_xOrder]
  rw [evalEval_add, evalEval_X_mul]
  rw [hasseDerivative_eval_eq_eval, hasseDerivative_eval_eq_eval]

end CBivariate

namespace GuruswamiSudan

namespace CBivariate

theorem hasseDerivativeEval_linearXFactor_mul_zero_xOrder_general {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval 0 b x y (linearXFactor c * Q) =
      (x - c) * CompPoly.CBivariate.hasseDerivativeEval 0 b x y Q := by
  unfold linearXFactor
  rw [sub_mul, CompPoly.CBivariate.hasseDerivativeEval_sub,
    CompPoly.CBivariate.hasseDerivativeEval_X_mul_zero_xOrder,
    CompPoly.CBivariate.hasseDerivativeEval_CC_mul]
  ring

theorem hasseDerivativeEval_linearXFactor_mul_succ_xOrder_general {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (a b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval (a + 1) b x y (linearXFactor c * Q) =
      (x - c) * CompPoly.CBivariate.hasseDerivativeEval (a + 1) b x y Q +
        CompPoly.CBivariate.hasseDerivativeEval a b x y Q := by
  unfold linearXFactor
  rw [sub_mul, CompPoly.CBivariate.hasseDerivativeEval_sub,
    CompPoly.CBivariate.hasseDerivativeEval_X_mul_succ_xOrder,
    CompPoly.CBivariate.hasseDerivativeEval_CC_mul]
  ring

theorem hasseDerivativeEval_linearXFactor_mul_zero_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval 0 b x y (linearXFactor x * Q) = 0 := by
  rw [hasseDerivativeEval_linearXFactor_mul_zero_xOrder_general]
  ring

theorem hasseDerivativeEval_linearXFactor_mul_succ_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval (a + 1) b x y (linearXFactor x * Q) =
      CompPoly.CBivariate.hasseDerivativeEval a b x y Q := by
  rw [hasseDerivativeEval_linearXFactor_mul_succ_xOrder_general]
  ring

end CBivariate

/-- The initial Koetter basis has one entry for each `Y` exponent up to the cap. -/
theorem koetterInitialBasis_size {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) :
    (koetterInitialBasis (F := F) params).size = koetterYCap params + 1 := by
  unfold koetterInitialBasis
  simp

theorem koetterInitialBasis_getD_of_le_yCap {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) {idx : Nat} (hidx : idx ≤ koetterYCap params) :
    (koetterInitialBasis (F := F) params).getD idx 0 =
      CBivariate.monomialXY 0 idx (1 : F) := by
  unfold koetterInitialBasis
  rw [Array.getD_eq_getD_getElem?]
  simp [hidx]

theorem koetterInitialBasis_entry_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) {idx : Nat} (hidx : idx ≤ koetterYCap params) :
    (koetterInitialBasis (F := F) params).getD idx 0 ≠ 0 := by
  rw [koetterInitialBasis_getD_of_le_yCap params hidx]
  intro hzero
  have hcoeff := congrArg (fun Q : CBivariate F ↦ CBivariate.coeff Q 0 idx) hzero
  change CBivariate.coeff (CBivariate.monomialXY 0 idx (1 : F)) 0 idx =
    CBivariate.coeff (0 : CBivariate F) 0 idx at hcoeff
  rw [CBivariate.coeff_monomialXY, CBivariate.coeff_zero] at hcoeff
  simp at hcoeff

theorem koetterInitialBasis_entry_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) {idx : Nat} (hidx : idx ≤ koetterYCap params) :
    CBivariate.natWeightedDegree
      ((koetterInitialBasis (F := F) params).getD idx 0) 1 (yWeight params) ≤
      params.weightedDegreeBound := by
  rw [koetterInitialBasis_getD_of_le_yCap params hidx,
    CBivariate.natWeightedDegree_monomialXY
      (hc := (one_ne_zero : (1 : F) ≠ 0))]
  unfold koetterYCap at hidx
  by_cases hy : yWeight params = 0
  · simp [hy]
  · have hypos : 0 < yWeight params := Nat.pos_of_ne_zero hy
    have hmul : idx * yWeight params ≤ params.weightedDegreeBound :=
      (Nat.le_div_iff_mul_le hypos).mp hidx
    simpa [Nat.mul_comm] using hmul

theorem natWeightedDegree_neg_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (P : CBivariate F) (u v : Nat) :
    CBivariate.natWeightedDegree (-P) u v ≤
      CBivariate.natWeightedDegree P u v := by
  rw [CBivariate.natWeightedDegree_le_iff_coeff]
  intro i j hcoeff
  rw [CBivariate.coeff_neg] at hcoeff
  have hP : CBivariate.coeff P i j ≠ 0 := by
    intro hzero
    exact hcoeff (by rw [hzero]; simp)
  exact (CBivariate.natWeightedDegree_le_iff_coeff P u v
    (CBivariate.natWeightedDegree P u v)).mp le_rfl i j hP

theorem natWeightedDegree_sub_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (P Q : CBivariate F) (u v : Nat) :
    CBivariate.natWeightedDegree (P - Q) u v ≤
      max (CBivariate.natWeightedDegree P u v)
        (CBivariate.natWeightedDegree Q u v) := by
  rw [sub_eq_add_neg]
  exact le_trans (CBivariate.natWeightedDegree_add_le P (-Q) u v)
    (max_le_max le_rfl (natWeightedDegree_neg_le Q u v))

theorem natWeightedDegree_CC_mul_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (P : CBivariate F) (u v : Nat) :
    CBivariate.natWeightedDegree (CBivariate.CC c * P) u v ≤
      CBivariate.natWeightedDegree P u v := by
  rw [CBivariate.natWeightedDegree_le_iff_coeff]
  intro i j hcoeff
  rw [CBivariate.coeff_CC_mul] at hcoeff
  have hP : CBivariate.coeff P i j ≠ 0 := by
    intro hzero
    exact hcoeff (by rw [hzero]; simp)
  exact (CBivariate.natWeightedDegree_le_iff_coeff P u v
    (CBivariate.natWeightedDegree P u v)).mp le_rfl i j hP

theorem natWeightedDegree_X_mul_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (P : CBivariate F) (w : Nat) :
    CBivariate.natWeightedDegree (CBivariate.X * P) 1 w ≤
      CBivariate.natWeightedDegree P 1 w + 1 := by
  rw [CBivariate.natWeightedDegree_le_iff_coeff]
  intro i j hcoeff
  cases i with
  | zero =>
      rw [CBivariate.coeff_X_mul_zero] at hcoeff
      contradiction
  | succ i =>
      rw [CBivariate.coeff_X_mul_succ] at hcoeff
      have hP := (CBivariate.natWeightedDegree_le_iff_coeff P 1 w
        (CBivariate.natWeightedDegree P 1 w)).mp le_rfl i j hcoeff
      omega

theorem natWeightedDegree_linearXFactor_mul_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x : F) (P : CBivariate F) (w : Nat) :
    CBivariate.natWeightedDegree (CBivariate.linearXFactor x * P) 1 w ≤
      CBivariate.natWeightedDegree P 1 w + 1 := by
  unfold CBivariate.linearXFactor
  rw [sub_mul]
  apply le_trans (natWeightedDegree_sub_le (CBivariate.X * P) (CBivariate.CC x * P) 1 w)
  apply max_le
  · exact natWeightedDegree_X_mul_le P w
  · exact le_trans (natWeightedDegree_CC_mul_le x P 1 w) (by omega)

def koetterRowLeadingAt {F : Type*}
    [Zero F] [BEq F] (params : GSInterpParams) (idx : Nat)
    (P : CBivariate F) : Prop :=
  yWeight params * idx ≤ CBivariate.natWeightedDegree P 1 (yWeight params) ∧
    CBivariate.coeff P
        (CBivariate.natWeightedDegree P 1 (yWeight params) - yWeight params * idx)
        idx ≠ 0 ∧
      ∀ i j, idx < j → CBivariate.coeff P i j ≠ 0 →
        i + yWeight params * j <
          CBivariate.natWeightedDegree P 1 (yWeight params)

def koetterBasisWeakLeading {F : Type*}
    [Zero F] [BEq F] (params : GSInterpParams)
    (basis : Array (CBivariate F)) : Prop :=
  ∀ idx, idx < basis.size →
    koetterRowLeadingAt params idx (basis.getD idx default)

theorem koetterRowLeadingAt_ne_zero {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {params : GSInterpParams} {idx : Nat} {P : CBivariate F}
    (h : koetterRowLeadingAt params idx P) :
    P ≠ 0 := by
  intro hzero
  have hcoeff := h.2.1
  rw [hzero, CBivariate.coeff_zero] at hcoeff
  exact hcoeff rfl

theorem koetterRowLeadingAt_coeff_zero_of_weight_gt {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {idx : Nat} {P : CBivariate F}
    (_h : koetterRowLeadingAt params idx P) {i j : Nat}
    (hgt :
      CBivariate.natWeightedDegree P 1 (yWeight params) <
        i + yWeight params * j) :
    CBivariate.coeff P i j = 0 := by
  by_contra hne
  have hle := (CBivariate.natWeightedDegree_le_iff_coeff P 1 (yWeight params)
    (CBivariate.natWeightedDegree P 1 (yWeight params))).mp le_rfl i j hne
  omega

theorem koetterRowLeadingAt_linearXFactor_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {idx : Nat} {P : CBivariate F}
    (x : F) (h : koetterRowLeadingAt params idx P) :
    koetterRowLeadingAt params idx (CBivariate.linearXFactor x * P) := by
  let w := yWeight params
  let d := CBivariate.natWeightedDegree P 1 w
  let leadX := d - w * idx
  have hwidx : w * idx ≤ d := by
    simpa [w, d] using h.1
  have hleadCoeff : CBivariate.coeff P leadX idx ≠ 0 := by
    simpa [w, d, leadX] using h.2.1
  have hnextZero : CBivariate.coeff P (leadX + 1) idx = 0 := by
    apply koetterRowLeadingAt_coeff_zero_of_weight_gt h
    dsimp [leadX, d, w]
    omega
  have hcoeffNew :
      CBivariate.coeff (CBivariate.linearXFactor x * P) (leadX + 1) idx ≠ 0 := by
    unfold CBivariate.linearXFactor
    rw [sub_mul, CBivariate.coeff_sub, CBivariate.coeff_X_mul_succ,
      CBivariate.coeff_CC_mul, hnextZero]
    simpa using hleadCoeff
  have hnewUpper :
      CBivariate.natWeightedDegree (CBivariate.linearXFactor x * P) 1 w ≤ d + 1 := by
    simpa [d] using natWeightedDegree_linearXFactor_mul_le x P w
  have hnewLower :
      d + 1 ≤ CBivariate.natWeightedDegree (CBivariate.linearXFactor x * P) 1 w := by
    have hle := (CBivariate.natWeightedDegree_le_iff_coeff
      (CBivariate.linearXFactor x * P) 1 w
      (CBivariate.natWeightedDegree (CBivariate.linearXFactor x * P) 1 w)).mp le_rfl
        (leadX + 1) idx hcoeffNew
    dsimp [leadX] at hle
    omega
  have hnewDegree :
      CBivariate.natWeightedDegree (CBivariate.linearXFactor x * P) 1 w = d + 1 :=
    le_antisymm hnewUpper hnewLower
  unfold koetterRowLeadingAt
  refine ⟨?_, ?_, ?_⟩
  · rw [hnewDegree]
    dsimp [w] at hwidx ⊢
    omega
  · rw [hnewDegree]
    change CBivariate.coeff (CBivariate.linearXFactor x * P)
      ((d + 1) - w * idx) idx ≠ 0
    rw [show (d + 1) - w * idx = leadX + 1 by dsimp [leadX]; omega]
    exact hcoeffNew
  · intro i j hj hcoeff
    rw [hnewDegree]
    unfold CBivariate.linearXFactor at hcoeff
    rw [sub_mul, CBivariate.coeff_sub] at hcoeff
    have hcase :
        CBivariate.coeff (CBivariate.X * P) i j ≠ 0 ∨
          CBivariate.coeff (CBivariate.CC x * P) i j ≠ 0 := by
      by_cases hX : CBivariate.coeff (CBivariate.X * P) i j = 0
      · right
        intro hCC
        rw [hX, hCC] at hcoeff
        simp at hcoeff
      · exact Or.inl hX
    rcases hcase with hX | hCC
    · cases i with
      | zero =>
          rw [CBivariate.coeff_X_mul_zero] at hX
          exact False.elim (hX rfl)
      | succ i =>
          rw [CBivariate.coeff_X_mul_succ] at hX
          have hold := h.2.2 i j hj hX
          dsimp [d, w] at hold ⊢
          omega
    · rw [CBivariate.coeff_CC_mul] at hCC
      have hP : CBivariate.coeff P i j ≠ 0 := by
        intro hzero
        rw [hzero] at hCC
        simp at hCC
      have hold := h.2.2 i j hj hP
      dsimp [d, w] at hold ⊢
      omega

theorem koetterRowLeadingAt_sub_cc_mul_of_pivot_order {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {idx pivotIdx : Nat}
    {current pivotPoly : CBivariate F} (c : F)
    (hCurrent : koetterRowLeadingAt params idx current)
    (hPivot : koetterRowLeadingAt params pivotIdx pivotPoly)
    (hpivotLe :
      CBivariate.natWeightedDegree pivotPoly 1 (yWeight params) ≤
        CBivariate.natWeightedDegree current 1 (yWeight params))
    (htie :
      CBivariate.natWeightedDegree pivotPoly 1 (yWeight params) =
        CBivariate.natWeightedDegree current 1 (yWeight params) →
          pivotIdx < idx) :
    koetterRowLeadingAt params idx (current - CBivariate.CC c * pivotPoly) := by
  let w := yWeight params
  let d := CBivariate.natWeightedDegree current 1 w
  let pd := CBivariate.natWeightedDegree pivotPoly 1 w
  let leadX := d - w * idx
  have hwidx : w * idx ≤ d := by
    simpa [w, d] using hCurrent.1
  have hleadCoeff : CBivariate.coeff current leadX idx ≠ 0 := by
    simpa [w, d, leadX] using hCurrent.2.1
  have hpivotCoeffAtLead : CBivariate.coeff pivotPoly leadX idx = 0 := by
    by_cases hlt : pd < d
    · apply koetterRowLeadingAt_coeff_zero_of_weight_gt hPivot
      dsimp [leadX, d, pd, w] at hlt ⊢
      omega
    · have hdp : pd = d := by
        apply le_antisymm
        · simpa [pd, d, w] using hpivotLe
        · exact le_of_not_gt hlt
      by_contra hne
      have hpivotLtIdx : pivotIdx < idx := by
        apply htie
        simpa [pd, d, w] using hdp
      have hstrict := hPivot.2.2 leadX idx hpivotLtIdx hne
      dsimp [leadX, d, pd, w] at hstrict hdp ⊢
      omega
  have hnewLead :
      CBivariate.coeff (current - CBivariate.CC c * pivotPoly) leadX idx ≠ 0 := by
    rw [CBivariate.coeff_sub, CBivariate.coeff_CC_mul, hpivotCoeffAtLead]
    simpa using hleadCoeff
  have hnewUpper :
      CBivariate.natWeightedDegree (current - CBivariate.CC c * pivotPoly) 1 w ≤ d := by
    apply le_trans (natWeightedDegree_sub_le current (CBivariate.CC c * pivotPoly) 1 w)
    apply max_le
    · exact le_rfl
    · exact le_trans (natWeightedDegree_CC_mul_le c pivotPoly 1 w)
        (by simpa [pd, d, w] using hpivotLe)
  have hnewLower :
      d ≤ CBivariate.natWeightedDegree (current - CBivariate.CC c * pivotPoly) 1 w := by
    have hle := (CBivariate.natWeightedDegree_le_iff_coeff
      (current - CBivariate.CC c * pivotPoly) 1 w
      (CBivariate.natWeightedDegree (current - CBivariate.CC c * pivotPoly) 1 w)).mp
        le_rfl leadX idx hnewLead
    dsimp [leadX] at hle
    omega
  have hnewDegree :
      CBivariate.natWeightedDegree (current - CBivariate.CC c * pivotPoly) 1 w = d :=
    le_antisymm hnewUpper hnewLower
  unfold koetterRowLeadingAt
  refine ⟨?_, ?_, ?_⟩
  · rw [hnewDegree]
    dsimp [w] at hwidx ⊢
    omega
  · rw [hnewDegree]
    change CBivariate.coeff (current - CBivariate.CC c * pivotPoly)
      (d - w * idx) idx ≠ 0
    rw [show d - w * idx = leadX by rfl]
    exact hnewLead
  · intro i j hj hcoeff
    rw [hnewDegree]
    rw [CBivariate.coeff_sub] at hcoeff
    have hcase :
        CBivariate.coeff current i j ≠ 0 ∨
          CBivariate.coeff (CBivariate.CC c * pivotPoly) i j ≠ 0 := by
      by_cases hcur : CBivariate.coeff current i j = 0
      · right
        intro hpiv
        rw [hcur, hpiv] at hcoeff
        simp at hcoeff
      · exact Or.inl hcur
    rcases hcase with hcur | hpivScaled
    · have hold := hCurrent.2.2 i j hj hcur
      dsimp [d, w] at hold ⊢
      omega
    · rw [CBivariate.coeff_CC_mul] at hpivScaled
      have hpiv : CBivariate.coeff pivotPoly i j ≠ 0 := by
        intro hzero
        rw [hzero] at hpivScaled
        simp at hpivScaled
      by_cases hlt : pd < d
      · have hle := (CBivariate.natWeightedDegree_le_iff_coeff pivotPoly 1 w pd).mp
          le_rfl i j hpiv
        dsimp [pd, d, w] at hlt hle ⊢
        omega
      · have hdp : pd = d := by
          apply le_antisymm
          · simpa [pd, d, w] using hpivotLe
          · exact le_of_not_gt hlt
        have hpivotLtIdx : pivotIdx < idx := by
          apply htie
          simpa [pd, d, w] using hdp
        have hstrict := hPivot.2.2 i j (by omega) hpiv
        dsimp [pd, d, w] at hdp hstrict ⊢
        omega

theorem koetterInitialBasis_rowLeadingAt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) {idx : Nat} (hidx : idx ≤ koetterYCap params) :
    koetterRowLeadingAt params idx
      ((koetterInitialBasis (F := F) params).getD idx 0) := by
  rw [koetterInitialBasis_getD_of_le_yCap params hidx]
  unfold koetterRowLeadingAt
  rw [CBivariate.natWeightedDegree_monomialXY
    (hc := (one_ne_zero : (1 : F) ≠ 0))]
  refine ⟨by omega, ?_, ?_⟩
  · rw [show 0 * 1 + yWeight params * idx - yWeight params * idx = 0 by omega]
    rw [CBivariate.coeff_monomialXY]
    simp
  · intro i j hj hcoeff
    rw [CBivariate.coeff_monomialXY] at hcoeff
    by_cases hmatch : i = 0 ∧ j = idx
    · exact False.elim (by omega)
    · simp [hmatch] at hcoeff

theorem koetterInitialBasis_weakLeading {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) :
    koetterBasisWeakLeading (F := F) params (koetterInitialBasis params) := by
  intro idx hidx
  have hidxCap : idx ≤ koetterYCap params := by
    rw [koetterInitialBasis_size] at hidx
    omega
  exact koetterInitialBasis_rowLeadingAt params hidxCap

end GuruswamiSudan

end CompPoly
