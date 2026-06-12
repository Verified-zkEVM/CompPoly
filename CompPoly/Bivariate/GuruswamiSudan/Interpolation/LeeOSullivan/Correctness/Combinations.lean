/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Common

/-!
# Generic Basis Combination Helpers

Generic finite-Y and basis-combination lemmas used by Lee-O'Sullivan correctness.
-/

namespace CompPoly

theorem cpoly_natDegree_mul_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (P Q : CPolynomial F) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul_le

theorem cpoly_eval_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] (x : F) (P Q : CPolynomial F) :
    CPolynomial.eval x (P + Q) = CPolynomial.eval x P + CPolynomial.eval x Q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

theorem cpoly_eval_X {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] (x : F) :
    CPolynomial.eval x CPolynomial.X = x := by
  rw [CPolynomial.eval_toPoly, CPolynomial.X_toPoly, Polynomial.eval_X]

theorem cpoly_eq_of_toPoly_eq {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] {P Q : CPolynomial F}
    (h : P.toPoly = Q.toPoly) :
    P = Q := by
  apply (CPolynomial.eq_iff_coeff (p := P) (q := Q)).2
  intro i
  have hcoeff := congrArg (fun p : Polynomial F ↦ p.coeff i) h
  change P.toPoly.coeff i = Q.toPoly.coeff i at hcoeff
  rwa [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly] at hcoeff

theorem cpoly_coeff_eq_zero_of_natDegree_lt {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F] {P : CPolynomial F} {i : Nat}
    (h : P.natDegree < i) :
    P.coeff i = 0 := by
  by_contra hne
  exact (Nat.not_lt_of_ge (CPolynomial.le_natDegree_of_ne_zero hne)) h

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

theorem evalEval_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (P Q : CBivariate F) :
    evalEval x y (P - Q) = evalEval x y P - evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, evalEval_toPoly]
  have hsub : toPoly (P - Q) = toPoly P - toPoly Q := by
    simpa [ringEquiv] using (ringEquiv (R := F)).map_sub P Q
  rw [hsub]
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

theorem hasseDerivativeEval_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (a b : Nat) (x y : F) (Q : CBivariate F) :
    hasseDerivativeEval a b x y (CC c * Q) =
      c * hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (CC c * Q)]
  rw [hasseDerivative_CC_mul]
  rw [evalEval_CC_mul]
  rw [hasseDerivative_eval_eq_eval]

theorem hasseDerivativeEval_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (x y : F) (P Q : CBivariate F) :
    hasseDerivativeEval a b x y (P - Q) =
      hasseDerivativeEval a b x y P - hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (P - Q)]
  rw [hasseDerivative_sub]
  rw [evalEval_sub]
  rw [hasseDerivative_eval_eq_eval, hasseDerivative_eval_eq_eval]

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

/-- Finite `Y` cap shared by positive-`Y`-weight interpolation proofs. -/
def koetterYCap (params : GSInterpParams) : Nat :=
  params.weightedDegreeBound / yWeight params

theorem coeff_ofYCoefficient {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (j : Nat) (P : CPolynomial F) (i k : Nat) :
    CBivariate.coeff (CBivariate.ofYCoefficient j P) i k =
      if k = j then P.coeff i else 0 := by
  unfold CBivariate.ofYCoefficient CBivariate.coeff
  have houter :
      CPolynomial.coeff (CPolynomial.monomial j P : CBivariate F) k =
        if k = j then P else 0 := by
    exact CPolynomial.coeff_monomial j k P
  by_cases hk : k = j
  · subst k
    simpa using congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
  · have hcoeff := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    simpa [hk, CPolynomial.coeff_zero] using hcoeff

theorem coeff_ofYConstant {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (P : CPolynomial F) (i j : Nat) :
    CBivariate.coeff (CBivariate.ofYConstant P) i j =
      if j = 0 then P.coeff i else 0 := by
  unfold CBivariate.ofYConstant CBivariate.coeff
  have houter :
      CPolynomial.coeff (CPolynomial.C P : CBivariate F) j =
        if j = 0 then P else 0 := by
    exact CPolynomial.coeff_C P j
  by_cases hj : j = 0
  · subst j
    simpa using congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
  · have hcoeff := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    simpa [hj, CPolynomial.coeff_zero] using hcoeff

theorem coeff_ofYConstant_mul {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (A : CPolynomial F) (P : CBivariate F) (i j : Nat) :
    CBivariate.coeff (CBivariate.ofYConstant A * P) i j =
      (A * P.val.coeff j).coeff i := by
  unfold CBivariate.ofYConstant CBivariate.coeff
  let P' : CPolynomial (CPolynomial F) := P
  change (CPolynomial.coeff (CPolynomial.coeff (CPolynomial.C A * P') j) i) =
    CPolynomial.coeff (A * CPolynomial.coeff P' j) i
  have houter :
      CPolynomial.coeff (CPolynomial.C A * P') j =
        A * CPolynomial.coeff P' j := by
    exact CPolynomial.coeff_C_mul (p := P') (c := A) j
  simpa using congrArg (fun Q : CPolynomial F ↦ Q.coeff i) houter

theorem natWeightedDegree_ofYConstant_mul_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (A : CPolynomial F) (P : CBivariate F) (w : Nat) :
    CBivariate.natWeightedDegree (CBivariate.ofYConstant A * P) 1 w ≤
      A.natDegree + CBivariate.natWeightedDegree P 1 w := by
  rw [CBivariate.natWeightedDegree_le_iff_coeff]
  intro i j hcoeff
  rw [coeff_ofYConstant_mul] at hcoeff
  have hiMul :
      i ≤ (A * P.val.coeff j).natDegree :=
    CPolynomial.le_natDegree_of_ne_zero hcoeff
  have hmul :
      (A * P.val.coeff j).natDegree ≤ A.natDegree + (P.val.coeff j).natDegree :=
    cpoly_natDegree_mul_le A (P.val.coeff j)
  have hrowNe : P.val.coeff j ≠ 0 := by
    intro hzero
    rw [hzero, CPolynomial.mul_zero] at hcoeff
    exact hcoeff (CPolynomial.coeff_zero i)
  have hrowCoeff :
      CBivariate.coeff P (P.val.coeff j).natDegree j ≠ 0 := by
    exact CPolynomial.leadingCoeff_ne_zero hrowNe
  have hrowDeg :
      (P.val.coeff j).natDegree + w * j ≤
        CBivariate.natWeightedDegree P 1 w := by
    have hle := (CBivariate.natWeightedDegree_le_iff_coeff P 1 w
      (CBivariate.natWeightedDegree P 1 w)).mp le_rfl
        (P.val.coeff j).natDegree j hrowCoeff
    simpa using hle
  omega

theorem validWitness_coeffY_eq_zero_of_yCap_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hMessage : ¬ params.messageDegree ≤ 1)
    (hQ : ValidInterpolationWitness points params Q) {j : Nat}
    (hj : koetterYCap params < j) :
    Q.val.coeff j = 0 := by
  by_contra hcoeffY
  rcases hQ with ⟨_hne, hdeg, _hmult⟩
  have hyWeightPos : 0 < yWeight params := by
    unfold yWeight
    omega
  have hcoeff :
      CBivariate.coeff Q (Q.val.coeff j).natDegree j ≠ 0 := by
    have hmem := CPolynomial.natDegree_mem_support_of_nonzero hcoeffY
    exact (CPolynomial.mem_support_iff (Q.val.coeff j) _).mp hmem
  have hterm :=
    (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params)
      params.weightedDegreeBound).mp hdeg (Q.val.coeff j).natDegree j hcoeff
  have hyMul : yWeight params * j ≤ params.weightedDegreeBound := by
    omega
  have hjle : j ≤ koetterYCap params := by
    unfold koetterYCap
    exact (Nat.le_div_iff_mul_le hyWeightPos).2 (by
      simpa [Nat.mul_comm] using hyMul)
  exact (Nat.not_lt_of_ge hjle) hj

theorem ofYConstant_zero {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] :
    CBivariate.ofYConstant (0 : CPolynomial F) = 0 := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [coeff_ofYConstant, CBivariate.coeff_zero]
  by_cases hj : j = 0
  · subst j
    exact CPolynomial.coeff_zero i
  · simp [hj]

theorem ofYConstant_add {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (P Q : CPolynomial F) :
    CBivariate.ofYConstant (P + Q) =
      CBivariate.ofYConstant P + CBivariate.ofYConstant Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [CBivariate.coeff_add, coeff_ofYConstant, coeff_ofYConstant, coeff_ofYConstant]
  by_cases hj : j = 0
  · subst j
    exact CPolynomial.coeff_add P Q i
  · simp [hj]

theorem ofYConstant_C {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] (c : F) :
    CBivariate.ofYConstant (CPolynomial.C c) = CBivariate.CC c := by
  rfl

theorem ofYConstant_mul {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (P Q : CPolynomial F) :
    CBivariate.ofYConstant (P * Q) =
      CBivariate.ofYConstant P * CBivariate.ofYConstant Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  unfold CBivariate.ofYConstant CBivariate.coeff
  have hleftOuter :
      CPolynomial.coeff (CPolynomial.C (P * Q) : CBivariate F) j =
        if j = 0 then P * Q else 0 := by
    exact CPolynomial.coeff_C (P * Q) j
  have houter :
      CPolynomial.coeff (CPolynomial.C P * CPolynomial.C Q : CBivariate F) j =
        P * CPolynomial.coeff (CPolynomial.C Q : CBivariate F) j := by
    exact CPolynomial.coeff_C_mul (p := (CPolynomial.C Q : CBivariate F))
      (c := P) j
  by_cases hj : j = 0
  · subst j
    have hleft := congrArg (fun P : CPolynomial F ↦ P.coeff i) hleftOuter
    have hright := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    rw [CPolynomial.coeff_C] at hright
    simpa using hleft.trans hright.symm
  · have hleft := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    have hleftOuterCoeff := congrArg (fun P : CPolynomial F ↦ P.coeff i) hleftOuter
    rw [CPolynomial.coeff_C] at hleft
    simp [hj] at hleft hleftOuterCoeff ⊢
    exact hleftOuterCoeff.trans hleft.symm

theorem ofYConstant_X_mul {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (P : CPolynomial F) :
    CBivariate.ofYConstant (CPolynomial.X * P) =
      CBivariate.X * CBivariate.ofYConstant P := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  unfold CBivariate.ofYConstant CBivariate.X CBivariate.coeff
  have hleftOuter :
      CPolynomial.coeff (CPolynomial.C (CPolynomial.X * P) : CBivariate F) j =
        if j = 0 then CPolynomial.X * P else 0 := by
    exact CPolynomial.coeff_C (CPolynomial.X * P) j
  have houter :
      CPolynomial.coeff
          (CPolynomial.C CPolynomial.X * CPolynomial.C P : CBivariate F) j =
        CPolynomial.X * CPolynomial.coeff (CPolynomial.C P : CBivariate F) j := by
    exact CPolynomial.coeff_C_mul (p := (CPolynomial.C P : CBivariate F))
      (c := CPolynomial.X) j
  by_cases hj : j = 0
  · subst j
    have hleft := congrArg (fun P : CPolynomial F ↦ P.coeff i) hleftOuter
    have hright := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    rw [CPolynomial.coeff_C] at hright
    simpa using hleft.trans hright.symm
  · have hright := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    have hleft := congrArg (fun P : CPolynomial F ↦ P.coeff i) hleftOuter
    rw [CPolynomial.coeff_C] at hright
    simp [hj] at hright hleft ⊢
    exact hleft.trans hright.symm

theorem cpoly_eq_zero_of_val_size_eq_zero {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F] (P : CPolynomial F)
    (hsize : P.val.size = 0) :
    P = 0 := by
  apply (CPolynomial.eq_zero_iff_coeff_zero (p := P)).2
  intro i
  unfold CPolynomial.coeff CPolynomial.Raw.coeff
  rw [Array.getD_eq_getD_getElem?]
  have hnone : P.val[i]? = none := by
    exact Array.getElem?_eq_none (by omega)
  simp [hnone]

theorem hasseDerivativeEval_ofYConstant_mul_eq_eval_mul_of_lower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (b : Nat) :
    ∀ (A : CPolynomial F) (P : CBivariate F) (order : Nat),
      (∀ a, a < order → CBivariate.hasseDerivativeEval a b x y P = 0) →
        CBivariate.hasseDerivativeEval order b x y
            (CBivariate.ofYConstant A * P) =
          CPolynomial.eval x A * CBivariate.hasseDerivativeEval order b x y P := by
  have hmain :
      ∀ n, ∀ (A : CPolynomial F), A.val.size = n → ∀ (P : CBivariate F) (order : Nat),
        (∀ a, a < order → CBivariate.hasseDerivativeEval a b x y P = 0) →
          CBivariate.hasseDerivativeEval order b x y
              (CBivariate.ofYConstant A * P) =
            CPolynomial.eval x A * CBivariate.hasseDerivativeEval order b x y P := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A hsize P order hLower
        by_cases hzeroSize : A.val.size = 0
        · rw [cpoly_eq_zero_of_val_size_eq_zero A hzeroSize, ofYConstant_zero]
          rw [zero_mul, CBivariate.hasseDerivativeEval_zero, CPolynomial.eval_toPoly,
            CPolynomial.toPoly_zero, Polynomial.eval_zero]
          simp
        · have hpos : A.val.size > 0 := by omega
          have hdivSize : (CPolynomial.divX A).val.size < n := by
            have hlt := CPolynomial.divX_size_lt (p := A) hpos
            omega
          have ihDiv := ih (CPolynomial.divX A).val.size hdivSize
            (CPolynomial.divX A) rfl
          have hA := CPolynomial.X_mul_divX_add (p := A)
          rw [hA, ofYConstant_add, ofYConstant_X_mul, ofYConstant_C, add_mul,
            CBivariate.hasseDerivativeEval_add, mul_assoc]
          cases order with
          | zero =>
              rw [CBivariate.hasseDerivativeEval_X_mul_zero_xOrder,
                ihDiv P 0 (by intro a ha; omega),
                CBivariate.hasseDerivativeEval_CC_mul,
                cpoly_eval_add, CPolynomial.eval_mul, cpoly_eval_X, CPolynomial.eval_C]
              ring
          | succ order =>
              have hLowerCurrent :
                  ∀ a, a < order + 1 →
                    CBivariate.hasseDerivativeEval a b x y P = 0 := hLower
              have hLowerPrev :
                  ∀ a, a < order →
                    CBivariate.hasseDerivativeEval a b x y P = 0 := by
                intro a ha
                exact hLower a (by omega)
              rw [CBivariate.hasseDerivativeEval_X_mul_succ_xOrder,
                ihDiv P (order + 1) hLowerCurrent,
                ihDiv P order hLowerPrev,
                hLower order (by omega),
                CBivariate.hasseDerivativeEval_CC_mul,
                cpoly_eval_add, CPolynomial.eval_mul, cpoly_eval_X, CPolynomial.eval_C]
              ring
  intro A P order hLower
  exact hmain A.val.size A rfl P order hLower

theorem hasseDerivativeEval_ofYConstant_mul_eq_zero_of_lower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (b : Nat) (A : CPolynomial F) (P : CBivariate F) (order : Nat)
    (hLower : ∀ a, a ≤ order →
      CBivariate.hasseDerivativeEval a b x y P = 0) :
    CBivariate.hasseDerivativeEval order b x y (CBivariate.ofYConstant A * P) = 0 := by
  rw [hasseDerivativeEval_ofYConstant_mul_eq_eval_mul_of_lower]
  · rw [hLower order (by omega)]
    simp
  · intro a ha
    exact hLower a (by omega)

theorem foldl_add_congr_terms {α : Type*} [Add α]
    (xs : List Nat) (f g : Nat → α) (z : α)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.foldl (fun out x ↦ out + f x) z =
      xs.foldl (fun out x ↦ out + g x) z := by
  induction xs generalizing z with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [h x (by simp)]
      exact ih (z + g x) (fun y hy ↦ h y (by simp [hy]))

theorem foldl_add_distrib_terms_aux {α : Type*} [AddCommMonoid α]
    (xs : List Nat) (f g : Nat → α) (a b : α) :
    xs.foldl (fun out x ↦ out + (f x + g x)) (a + b) =
      xs.foldl (fun out x ↦ out + f x) a +
        xs.foldl (fun out x ↦ out + g x) b := by
  induction xs generalizing a b with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [show a + b + (f x + g x) = (a + f x) + (b + g x) by ac_rfl]
      exact ih (a + f x) (b + g x)

theorem foldl_add_distrib_terms {α : Type*} [AddCommMonoid α]
    (xs : List Nat) (f g : Nat → α) :
    xs.foldl (fun out x ↦ out + (f x + g x)) 0 =
      xs.foldl (fun out x ↦ out + f x) 0 +
        xs.foldl (fun out x ↦ out + g x) 0 := by
  simpa using foldl_add_distrib_terms_aux xs f g (0 : α) (0 : α)

theorem foldl_add_single_beq_of_not_mem {α : Type*} [AddCommMonoid α]
    (xs : List Nat) (target : Nat) (term acc : α)
    (hnot : target ∉ xs) :
    xs.foldl (fun out idx ↦ out + if idx == target then term else 0) acc =
      acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons idx xs ih =>
      simp only [List.foldl_cons]
      have hidx : ¬ idx == target := by
        intro hbeq
        exact hnot (by simp [LawfulBEq.eq_of_beq hbeq])
      rw [if_neg hidx, add_zero]
      exact ih acc (by
        intro hmem
        exact hnot (by simp [hmem]))

theorem foldl_add_single_beq_of_nodup_mem {α : Type*} [AddCommMonoid α]
    (xs : List Nat) (target : Nat) (term : α)
    (hnodup : xs.Nodup) (hmem : target ∈ xs) :
    xs.foldl (fun out idx ↦ out + if idx == target then term else 0) 0 =
      term := by
  induction xs with
  | nil =>
      simp at hmem
  | cons idx xs ih =>
      simp only [List.foldl_cons]
      rw [List.nodup_cons] at hnodup
      rcases hnodup with ⟨hidxNotMem, hxsNodup⟩
      by_cases hidx : idx == target
      · rw [if_pos hidx, zero_add]
        have hidxEq : idx = target := LawfulBEq.eq_of_beq hidx
        subst idx
        exact foldl_add_single_beq_of_not_mem xs target term term hidxNotMem
      · rw [if_neg hidx, add_zero]
        have hmemTail : target ∈ xs := by
          rcases (List.mem_cons.mp hmem) with hhead | htail
          · subst idx
            simp at hidx
          · exact htail
        exact ih hxsNodup hmemTail

def koetterBasisCombination {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F)) : CBivariate F :=
  (List.range basis.size).foldl
    (fun out idx ↦ out + CBivariate.ofYConstant (weights idx) * basis.getD idx 0) 0

def koetterBasisSpanContains {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array (CBivariate F)) (Q : CBivariate F) : Prop :=
  ∃ weights : Nat → CPolynomial F, koetterBasisCombination weights basis = Q

theorem koetterBasisCombination_eq_zero_of_weights_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F))
    (hzero : ∀ idx, idx < basis.size → weights idx = 0) :
    koetterBasisCombination weights basis = 0 := by
  unfold koetterBasisCombination
  let step : CBivariate F → Nat → CBivariate F :=
    fun out idx ↦ out + CBivariate.ofYConstant (weights idx) * basis.getD idx 0
  have hfold :
      ∀ xs : List Nat, (∀ idx, idx ∈ xs → idx < basis.size) →
        xs.foldl step 0 = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro _hidx
        simp
    | cons idx xs ih =>
        intro hidx
        simp only [List.foldl_cons]
        have hi : idx < basis.size := hidx idx (by simp)
        unfold step
        rw [hzero idx hi, ofYConstant_zero, zero_mul, add_zero]
        exact ih (fun j hj ↦ hidx j (by simp [hj]))
  simpa [step] using hfold (List.range basis.size)
    (fun idx hmem ↦ List.mem_range.mp hmem)

theorem coeff_koetterBasisCombination {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F))
    (i j : Nat) :
    CBivariate.coeff (koetterBasisCombination weights basis) i j =
      (List.range basis.size).foldl
        (fun out idx ↦
          out + CBivariate.coeff
            (CBivariate.ofYConstant (weights idx) * basis.getD idx 0) i j)
        0 := by
  unfold koetterBasisCombination
  let term : Nat → CBivariate F :=
    fun idx ↦ CBivariate.ofYConstant (weights idx) * basis.getD idx 0
  have hfold : ∀ xs : List Nat, ∀ acc,
      CBivariate.coeff (xs.foldl (fun out idx ↦ out + term idx) acc) i j =
        xs.foldl
          (fun out idx ↦ out + CBivariate.coeff (term idx) i j)
          (CBivariate.coeff acc i j) := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons idx xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        rw [CBivariate.coeff_add]
  simpa [term, CBivariate.coeff_zero] using hfold (List.range basis.size) (0 : CBivariate F)


end GuruswamiSudan

end CompPoly
