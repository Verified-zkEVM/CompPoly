/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_32.Prelude
import Mathlib.Tactic.NormNum

/-!
# GF(2^32) Modular Frobenius Certificate

Kernel-safe certificate data for repeated squaring of `X` modulo
`X ^ 32 + X ^ 22 + X ^ 2 + X + 1`.
-/

namespace GF2_32

open Polynomial

set_option maxRecDepth 1500

/-- Certificate exponents fit in the doubled-width checker. -/
lemma certificateExponents_bound :
    ∀ exponent ∈ definingPolynomialExponents,
      extensionDegree + exponent ≤ 2 * extensionDegree := by
  unfold definingPolynomialExponents extensionDegree
  decide

/-- Soundness wrapper specialized to the GF32 defining polynomial. -/
private theorem verify_square_step {rPrev q rNext : B32}
    (h :
      BinaryField.Extension.checkSquareStep extensionDegree definingPolynomialExponents
        rPrev q rNext = true) :
    (BinaryField.toPoly rPrev) ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q) *
        definingPolynomial + BinaryField.toPoly rNext := by
  rw [← sparsePolynomial_definingPolynomialExponents]
  exact BinaryField.Extension.checkSquareStep_correct certificateExponents_bound
    rPrev q rNext h

def r0Val : B32 := BitVec.ofNat extensionDegree 2
noncomputable def r0 : Polynomial (ZMod 2) := BinaryField.toPoly r0Val

def q1Val : B32 := BitVec.ofNat extensionDegree 0
def r1Val : B32 := BitVec.ofNat extensionDegree 4
noncomputable def r1 : Polynomial (ZMod 2) := BinaryField.toPoly r1Val

def q2Val : B32 := BitVec.ofNat extensionDegree 0
def r2Val : B32 := BitVec.ofNat extensionDegree 16
noncomputable def r2 : Polynomial (ZMod 2) := BinaryField.toPoly r2Val

def q3Val : B32 := BitVec.ofNat extensionDegree 0
def r3Val : B32 := BitVec.ofNat extensionDegree 256
noncomputable def r3 : Polynomial (ZMod 2) := BinaryField.toPoly r3Val

def q4Val : B32 := BitVec.ofNat extensionDegree 0
def r4Val : B32 := BitVec.ofNat extensionDegree 65536
noncomputable def r4 : Polynomial (ZMod 2) := BinaryField.toPoly r4Val

def q5Val : B32 := BitVec.ofNat extensionDegree 1
def r5Val : B32 := BitVec.ofNat extensionDegree 4194311
noncomputable def r5 : Polynomial (ZMod 2) := BinaryField.toPoly r5Val

def q6Val : B32 := BitVec.ofNat extensionDegree 4100
def r6Val : B32 := BitVec.ofNat extensionDegree 16805897
noncomputable def r6 : Polynomial (ZMod 2) := BinaryField.toPoly r6Val

def q7Val : B32 := BitVec.ofNat extensionDegree 65600
def r7Val : B32 := BitVec.ofNat extensionDegree 84345217
noncomputable def r7 : Polynomial (ZMod 2) := BinaryField.toPoly r7Val

def q8Val : B32 := BitVec.ofNat extensionDegree 1115220
def r8Val : B32 := BitVec.ofNat extensionDegree 360078765
noncomputable def r8 : Polynomial (ZMod 2) := BinaryField.toPoly r8Val

def q9Val : B32 := BitVec.ofNat extensionDegree 17912128
def r9Val : B32 := BitVec.ofNat extensionDegree 1177023121
noncomputable def r9 : Polynomial (ZMod 2) := BinaryField.toPoly r9Val

def q10Val : B32 := BitVec.ofNat extensionDegree 269484053
def r10Val : B32 := BitVec.ofNat extensionDegree 540295530
noncomputable def r10 : Polynomial (ZMod 2) := BinaryField.toPoly r10Val

def q11Val : B32 := BitVec.ofNat extensionDegree 67175761
def r11Val : B32 := BitVec.ofNat extensionDegree 1480986355
noncomputable def r11 : Polynomial (ZMod 2) := BinaryField.toPoly r11Val

def q12Val : B32 := BitVec.ofNat extensionDegree 289685764
def r12Val : B32 := BitVec.ofNat extensionDegree 931762713
noncomputable def r12 : Polynomial (ZMod 2) := BinaryField.toPoly r12Val

def q13Val : B32 := BitVec.ofNat extensionDegree 85198144
def r13Val : B32 := BitVec.ofNat extensionDegree 174594945
noncomputable def r13 : Polynomial (ZMod 2) := BinaryField.toPoly r13Val

def q14Val : B32 := BitVec.ofNat extensionDegree 4457793
def r14Val : B32 := BitVec.ofNat extensionDegree 1356421830
noncomputable def r14 : Polynomial (ZMod 2) := BinaryField.toPoly r14Val

def q15Val : B32 := BitVec.ofNat extensionDegree 285478981
def r15Val : B32 := BitVec.ofNat extensionDegree 1998070223
noncomputable def r15 : Polynomial (ZMod 2) := BinaryField.toPoly r15Val

def q16Val : B32 := BitVec.ofNat extensionDegree 353387857
def r16Val : B32 := BitVec.ofNat extensionDegree 993037026
noncomputable def r16 : Polynomial (ZMod 2) := BinaryField.toPoly r16Val

def q17Val : B32 := BitVec.ofNat extensionDegree 88364053
def r17Val : B32 := BitVec.ofNat extensionDegree 1608120431
noncomputable def r17 : Polynomial (ZMod 2) := BinaryField.toPoly r17Val

def q18Val : B32 := BitVec.ofNat extensionDegree 290522368
def r18Val : B32 := BitVec.ofNat extensionDegree 1677135701
noncomputable def r18 : Polynomial (ZMod 2) := BinaryField.toPoly r18Val

def q19Val : B32 := BitVec.ofNat extensionDegree 335566080
def r19Val : B32 := BitVec.ofNat extensionDegree 743750161
noncomputable def r19 : Polynomial (ZMod 2) := BinaryField.toPoly r19Val

def q20Val : B32 := BitVec.ofNat extensionDegree 72418641
def r20Val : B32 := BitVec.ofNat extensionDegree 213064630
noncomputable def r20 : Polynomial (ZMod 2) := BinaryField.toPoly r20Val

def q21Val : B32 := BitVec.ofNat extensionDegree 5263633
def r21Val : B32 := BitVec.ofNat extensionDegree 1152709219
noncomputable def r21 : Polynomial (ZMod 2) := BinaryField.toPoly r21Val

def q22Val : B32 := BitVec.ofNat extensionDegree 269762560
def r22Val : B32 := BitVec.ofNat extensionDegree 627692549
noncomputable def r22 : Polynomial (ZMod 2) := BinaryField.toPoly r22Val

def q23Val : B32 := BitVec.ofNat extensionDegree 68161605
def r23Val : B32 := BitVec.ofNat extensionDegree 1545630154
noncomputable def r23 : Polynomial (ZMod 2) := BinaryField.toPoly r23Val

def q24Val : B32 := BitVec.ofNat extensionDegree 290738452
def r24Val : B32 := BitVec.ofNat extensionDegree 648865576
noncomputable def r24 : Polynomial (ZMod 2) := BinaryField.toPoly r24Val

def q25Val : B32 := BitVec.ofNat extensionDegree 68501760
def r25Val : B32 := BitVec.ofNat extensionDegree 142590784
noncomputable def r25 : Polynomial (ZMod 2) := BinaryField.toPoly r25Val

def q26Val : B32 := BitVec.ofNat extensionDegree 4195668
def r26Val : B32 := BitVec.ofNat extensionDegree 80022188
noncomputable def r26 : Polynomial (ZMod 2) := BinaryField.toPoly r26Val

def q27Val : B32 := BitVec.ofNat extensionDegree 1070084
def r27Val : B32 := BitVec.ofNat extensionDegree 20310092
noncomputable def r27 : Polynomial (ZMod 2) := BinaryField.toPoly r27Val

def q28Val : B32 := BitVec.ofNat extensionDegree 66896
def r28Val : B32 := BitVec.ofNat extensionDegree 4655840
noncomputable def r28 : Polynomial (ZMod 2) := BinaryField.toPoly r28Val

def q29Val : B32 := BitVec.ofNat extensionDegree 4113
def r29Val : B32 := BitVec.ofNat extensionDegree 67380343
noncomputable def r29 : Polynomial (ZMod 2) := BinaryField.toPoly r29Val

def q30Val : B32 := BitVec.ofNat extensionDegree 1049617
def r30Val : B32 := BitVec.ofNat extensionDegree 2099554
noncomputable def r30 : Polynomial (ZMod 2) := BinaryField.toPoly r30Val

def q31Val : B32 := BitVec.ofNat extensionDegree 1025
def r31Val : B32 := BitVec.ofNat extensionDegree 67587
noncomputable def r31 : Polynomial (ZMod 2) := BinaryField.toPoly r31Val

def q32Val : B32 := BitVec.ofNat extensionDegree 1
def r32Val : B32 := BitVec.ofNat extensionDegree 2
noncomputable def r32 : Polynomial (ZMod 2) := BinaryField.toPoly r32Val

/-- The initial remainder denotes `X`. -/
lemma r0_eq_X : r0 = X := by
  rw [r0, r0Val, extensionDegree]
  have h : (BitVec.ofNat 32 2 : BitVec 32) = (1 <<< 1 : BitVec 32) := by
    decide
  rw [h]
  simpa only [pow_one] using
    BinaryField.Extension.toPoly_one_shiftLeft (w := 32) 1 (by decide)

/-- The final remainder after 32 Frobenius steps denotes `X`. -/
lemma r32_eq_X : r32 = X := by
  rw [r32, r32Val, extensionDegree]
  have h : (BitVec.ofNat 32 2 : BitVec 32) = (1 <<< 1 : BitVec 32) := by
    decide
  rw [h]
  simpa only [pow_one] using
    BinaryField.Extension.toPoly_one_shiftLeft (w := 32) 1 (by decide)

/-- Certificate step 1: square and reduce modulo the GF32 polynomial. -/
lemma step_1 :
    r0 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q1Val) *
        definingPolynomial + r1 := by
  change (BinaryField.toPoly r0Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q1Val) *
      definingPolynomial + BinaryField.toPoly r1Val
  exact verify_square_step (rPrev := r0Val) (q := q1Val)
    (rNext := r1Val) (by rfl)

/-- Certificate step 2: square and reduce modulo the GF32 polynomial. -/
lemma step_2 :
    r1 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q2Val) *
        definingPolynomial + r2 := by
  change (BinaryField.toPoly r1Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q2Val) *
      definingPolynomial + BinaryField.toPoly r2Val
  exact verify_square_step (rPrev := r1Val) (q := q2Val)
    (rNext := r2Val) (by rfl)

/-- Certificate step 3: square and reduce modulo the GF32 polynomial. -/
lemma step_3 :
    r2 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q3Val) *
        definingPolynomial + r3 := by
  change (BinaryField.toPoly r2Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q3Val) *
      definingPolynomial + BinaryField.toPoly r3Val
  exact verify_square_step (rPrev := r2Val) (q := q3Val)
    (rNext := r3Val) (by rfl)

/-- Certificate step 4: square and reduce modulo the GF32 polynomial. -/
lemma step_4 :
    r3 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q4Val) *
        definingPolynomial + r4 := by
  change (BinaryField.toPoly r3Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q4Val) *
      definingPolynomial + BinaryField.toPoly r4Val
  exact verify_square_step (rPrev := r3Val) (q := q4Val)
    (rNext := r4Val) (by rfl)

/-- Certificate step 5: square and reduce modulo the GF32 polynomial. -/
lemma step_5 :
    r4 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q5Val) *
        definingPolynomial + r5 := by
  change (BinaryField.toPoly r4Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q5Val) *
      definingPolynomial + BinaryField.toPoly r5Val
  exact verify_square_step (rPrev := r4Val) (q := q5Val)
    (rNext := r5Val) (by rfl)

/-- Certificate step 6: square and reduce modulo the GF32 polynomial. -/
lemma step_6 :
    r5 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q6Val) *
        definingPolynomial + r6 := by
  change (BinaryField.toPoly r5Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q6Val) *
      definingPolynomial + BinaryField.toPoly r6Val
  exact verify_square_step (rPrev := r5Val) (q := q6Val)
    (rNext := r6Val) (by rfl)

/-- Certificate step 7: square and reduce modulo the GF32 polynomial. -/
lemma step_7 :
    r6 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q7Val) *
        definingPolynomial + r7 := by
  change (BinaryField.toPoly r6Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q7Val) *
      definingPolynomial + BinaryField.toPoly r7Val
  exact verify_square_step (rPrev := r6Val) (q := q7Val)
    (rNext := r7Val) (by rfl)

/-- Certificate step 8: square and reduce modulo the GF32 polynomial. -/
lemma step_8 :
    r7 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q8Val) *
        definingPolynomial + r8 := by
  change (BinaryField.toPoly r7Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q8Val) *
      definingPolynomial + BinaryField.toPoly r8Val
  exact verify_square_step (rPrev := r7Val) (q := q8Val)
    (rNext := r8Val) (by rfl)

/-- Certificate step 9: square and reduce modulo the GF32 polynomial. -/
lemma step_9 :
    r8 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q9Val) *
        definingPolynomial + r9 := by
  change (BinaryField.toPoly r8Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q9Val) *
      definingPolynomial + BinaryField.toPoly r9Val
  exact verify_square_step (rPrev := r8Val) (q := q9Val)
    (rNext := r9Val) (by rfl)

/-- Certificate step 10: square and reduce modulo the GF32 polynomial. -/
lemma step_10 :
    r9 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q10Val) *
        definingPolynomial + r10 := by
  change (BinaryField.toPoly r9Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q10Val) *
      definingPolynomial + BinaryField.toPoly r10Val
  exact verify_square_step (rPrev := r9Val) (q := q10Val)
    (rNext := r10Val) (by rfl)

/-- Certificate step 11: square and reduce modulo the GF32 polynomial. -/
lemma step_11 :
    r10 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q11Val) *
        definingPolynomial + r11 := by
  change (BinaryField.toPoly r10Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q11Val) *
      definingPolynomial + BinaryField.toPoly r11Val
  exact verify_square_step (rPrev := r10Val) (q := q11Val)
    (rNext := r11Val) (by rfl)

/-- Certificate step 12: square and reduce modulo the GF32 polynomial. -/
lemma step_12 :
    r11 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q12Val) *
        definingPolynomial + r12 := by
  change (BinaryField.toPoly r11Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q12Val) *
      definingPolynomial + BinaryField.toPoly r12Val
  exact verify_square_step (rPrev := r11Val) (q := q12Val)
    (rNext := r12Val) (by rfl)

/-- Certificate step 13: square and reduce modulo the GF32 polynomial. -/
lemma step_13 :
    r12 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q13Val) *
        definingPolynomial + r13 := by
  change (BinaryField.toPoly r12Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q13Val) *
      definingPolynomial + BinaryField.toPoly r13Val
  exact verify_square_step (rPrev := r12Val) (q := q13Val)
    (rNext := r13Val) (by rfl)

/-- Certificate step 14: square and reduce modulo the GF32 polynomial. -/
lemma step_14 :
    r13 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q14Val) *
        definingPolynomial + r14 := by
  change (BinaryField.toPoly r13Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q14Val) *
      definingPolynomial + BinaryField.toPoly r14Val
  exact verify_square_step (rPrev := r13Val) (q := q14Val)
    (rNext := r14Val) (by rfl)

/-- Certificate step 15: square and reduce modulo the GF32 polynomial. -/
lemma step_15 :
    r14 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q15Val) *
        definingPolynomial + r15 := by
  change (BinaryField.toPoly r14Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q15Val) *
      definingPolynomial + BinaryField.toPoly r15Val
  exact verify_square_step (rPrev := r14Val) (q := q15Val)
    (rNext := r15Val) (by rfl)

/-- Certificate step 16: square and reduce modulo the GF32 polynomial. -/
lemma step_16 :
    r15 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q16Val) *
        definingPolynomial + r16 := by
  change (BinaryField.toPoly r15Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q16Val) *
      definingPolynomial + BinaryField.toPoly r16Val
  exact verify_square_step (rPrev := r15Val) (q := q16Val)
    (rNext := r16Val) (by rfl)

/-- Certificate step 17: square and reduce modulo the GF32 polynomial. -/
lemma step_17 :
    r16 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q17Val) *
        definingPolynomial + r17 := by
  change (BinaryField.toPoly r16Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q17Val) *
      definingPolynomial + BinaryField.toPoly r17Val
  exact verify_square_step (rPrev := r16Val) (q := q17Val)
    (rNext := r17Val) (by rfl)

/-- Certificate step 18: square and reduce modulo the GF32 polynomial. -/
lemma step_18 :
    r17 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q18Val) *
        definingPolynomial + r18 := by
  change (BinaryField.toPoly r17Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q18Val) *
      definingPolynomial + BinaryField.toPoly r18Val
  exact verify_square_step (rPrev := r17Val) (q := q18Val)
    (rNext := r18Val) (by rfl)

/-- Certificate step 19: square and reduce modulo the GF32 polynomial. -/
lemma step_19 :
    r18 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q19Val) *
        definingPolynomial + r19 := by
  change (BinaryField.toPoly r18Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q19Val) *
      definingPolynomial + BinaryField.toPoly r19Val
  exact verify_square_step (rPrev := r18Val) (q := q19Val)
    (rNext := r19Val) (by rfl)

/-- Certificate step 20: square and reduce modulo the GF32 polynomial. -/
lemma step_20 :
    r19 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q20Val) *
        definingPolynomial + r20 := by
  change (BinaryField.toPoly r19Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q20Val) *
      definingPolynomial + BinaryField.toPoly r20Val
  exact verify_square_step (rPrev := r19Val) (q := q20Val)
    (rNext := r20Val) (by rfl)

/-- Certificate step 21: square and reduce modulo the GF32 polynomial. -/
lemma step_21 :
    r20 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q21Val) *
        definingPolynomial + r21 := by
  change (BinaryField.toPoly r20Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q21Val) *
      definingPolynomial + BinaryField.toPoly r21Val
  exact verify_square_step (rPrev := r20Val) (q := q21Val)
    (rNext := r21Val) (by rfl)

/-- Certificate step 22: square and reduce modulo the GF32 polynomial. -/
lemma step_22 :
    r21 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q22Val) *
        definingPolynomial + r22 := by
  change (BinaryField.toPoly r21Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q22Val) *
      definingPolynomial + BinaryField.toPoly r22Val
  exact verify_square_step (rPrev := r21Val) (q := q22Val)
    (rNext := r22Val) (by rfl)

/-- Certificate step 23: square and reduce modulo the GF32 polynomial. -/
lemma step_23 :
    r22 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q23Val) *
        definingPolynomial + r23 := by
  change (BinaryField.toPoly r22Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q23Val) *
      definingPolynomial + BinaryField.toPoly r23Val
  exact verify_square_step (rPrev := r22Val) (q := q23Val)
    (rNext := r23Val) (by rfl)

/-- Certificate step 24: square and reduce modulo the GF32 polynomial. -/
lemma step_24 :
    r23 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q24Val) *
        definingPolynomial + r24 := by
  change (BinaryField.toPoly r23Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q24Val) *
      definingPolynomial + BinaryField.toPoly r24Val
  exact verify_square_step (rPrev := r23Val) (q := q24Val)
    (rNext := r24Val) (by rfl)

/-- Certificate step 25: square and reduce modulo the GF32 polynomial. -/
lemma step_25 :
    r24 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q25Val) *
        definingPolynomial + r25 := by
  change (BinaryField.toPoly r24Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q25Val) *
      definingPolynomial + BinaryField.toPoly r25Val
  exact verify_square_step (rPrev := r24Val) (q := q25Val)
    (rNext := r25Val) (by rfl)

/-- Certificate step 26: square and reduce modulo the GF32 polynomial. -/
lemma step_26 :
    r25 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q26Val) *
        definingPolynomial + r26 := by
  change (BinaryField.toPoly r25Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q26Val) *
      definingPolynomial + BinaryField.toPoly r26Val
  exact verify_square_step (rPrev := r25Val) (q := q26Val)
    (rNext := r26Val) (by rfl)

/-- Certificate step 27: square and reduce modulo the GF32 polynomial. -/
lemma step_27 :
    r26 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q27Val) *
        definingPolynomial + r27 := by
  change (BinaryField.toPoly r26Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q27Val) *
      definingPolynomial + BinaryField.toPoly r27Val
  exact verify_square_step (rPrev := r26Val) (q := q27Val)
    (rNext := r27Val) (by rfl)

/-- Certificate step 28: square and reduce modulo the GF32 polynomial. -/
lemma step_28 :
    r27 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q28Val) *
        definingPolynomial + r28 := by
  change (BinaryField.toPoly r27Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q28Val) *
      definingPolynomial + BinaryField.toPoly r28Val
  exact verify_square_step (rPrev := r27Val) (q := q28Val)
    (rNext := r28Val) (by rfl)

/-- Certificate step 29: square and reduce modulo the GF32 polynomial. -/
lemma step_29 :
    r28 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q29Val) *
        definingPolynomial + r29 := by
  change (BinaryField.toPoly r28Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q29Val) *
      definingPolynomial + BinaryField.toPoly r29Val
  exact verify_square_step (rPrev := r28Val) (q := q29Val)
    (rNext := r29Val) (by rfl)

/-- Certificate step 30: square and reduce modulo the GF32 polynomial. -/
lemma step_30 :
    r29 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q30Val) *
        definingPolynomial + r30 := by
  change (BinaryField.toPoly r29Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q30Val) *
      definingPolynomial + BinaryField.toPoly r30Val
  exact verify_square_step (rPrev := r29Val) (q := q30Val)
    (rNext := r30Val) (by rfl)

/-- Certificate step 31: square and reduce modulo the GF32 polynomial. -/
lemma step_31 :
    r30 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q31Val) *
        definingPolynomial + r31 := by
  change (BinaryField.toPoly r30Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q31Val) *
      definingPolynomial + BinaryField.toPoly r31Val
  exact verify_square_step (rPrev := r30Val) (q := q31Val)
    (rNext := r31Val) (by rfl)

/-- Certificate step 32: square and reduce modulo the GF32 polynomial. -/
lemma step_32 :
    r31 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q32Val) *
        definingPolynomial + r32 := by
  change (BinaryField.toPoly r31Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q32Val) *
      definingPolynomial + BinaryField.toPoly r32Val
  exact verify_square_step (rPrev := r31Val) (q := q32Val)
    (rNext := r32Val) (by rfl)


/-- The degree-one polynomial `X` is already reduced modulo the GF32 polynomial. -/
lemma X_mod_definingPolynomial :
    X % definingPolynomial = X := by
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact definingPolynomial_ne_zero)]
  rw [definingPolynomial_degree]
  unfold extensionDegree
  norm_num [degree_X]

lemma X_pow_2_pow_0_mod_eq :
    X ^ (2 ^ 0) % definingPolynomial = r0 % definingPolynomial := by
  rw [pow_zero, pow_one, r0_eq_X]

lemma X_pow_2_pow_1_mod_eq :
    X ^ (2 ^ 1) % definingPolynomial = r1 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 0) X_pow_2_pow_0_mod_eq step_1

lemma X_pow_2_pow_2_mod_eq :
    X ^ (2 ^ 2) % definingPolynomial = r2 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 1) X_pow_2_pow_1_mod_eq step_2

lemma X_pow_2_pow_3_mod_eq :
    X ^ (2 ^ 3) % definingPolynomial = r3 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 2) X_pow_2_pow_2_mod_eq step_3

lemma X_pow_2_pow_4_mod_eq :
    X ^ (2 ^ 4) % definingPolynomial = r4 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 3) X_pow_2_pow_3_mod_eq step_4

lemma X_pow_2_pow_5_mod_eq :
    X ^ (2 ^ 5) % definingPolynomial = r5 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 4) X_pow_2_pow_4_mod_eq step_5

lemma X_pow_2_pow_6_mod_eq :
    X ^ (2 ^ 6) % definingPolynomial = r6 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 5) X_pow_2_pow_5_mod_eq step_6

lemma X_pow_2_pow_7_mod_eq :
    X ^ (2 ^ 7) % definingPolynomial = r7 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 6) X_pow_2_pow_6_mod_eq step_7

lemma X_pow_2_pow_8_mod_eq :
    X ^ (2 ^ 8) % definingPolynomial = r8 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 7) X_pow_2_pow_7_mod_eq step_8

lemma X_pow_2_pow_9_mod_eq :
    X ^ (2 ^ 9) % definingPolynomial = r9 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 8) X_pow_2_pow_8_mod_eq step_9

lemma X_pow_2_pow_10_mod_eq :
    X ^ (2 ^ 10) % definingPolynomial = r10 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 9) X_pow_2_pow_9_mod_eq step_10

lemma X_pow_2_pow_11_mod_eq :
    X ^ (2 ^ 11) % definingPolynomial = r11 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 10) X_pow_2_pow_10_mod_eq step_11

lemma X_pow_2_pow_12_mod_eq :
    X ^ (2 ^ 12) % definingPolynomial = r12 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 11) X_pow_2_pow_11_mod_eq step_12

lemma X_pow_2_pow_13_mod_eq :
    X ^ (2 ^ 13) % definingPolynomial = r13 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 12) X_pow_2_pow_12_mod_eq step_13

lemma X_pow_2_pow_14_mod_eq :
    X ^ (2 ^ 14) % definingPolynomial = r14 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 13) X_pow_2_pow_13_mod_eq step_14

lemma X_pow_2_pow_15_mod_eq :
    X ^ (2 ^ 15) % definingPolynomial = r15 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 14) X_pow_2_pow_14_mod_eq step_15

lemma X_pow_2_pow_16_mod_eq :
    X ^ (2 ^ 16) % definingPolynomial = r16 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 15) X_pow_2_pow_15_mod_eq step_16

lemma X_pow_2_pow_17_mod_eq :
    X ^ (2 ^ 17) % definingPolynomial = r17 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 16) X_pow_2_pow_16_mod_eq step_17

lemma X_pow_2_pow_18_mod_eq :
    X ^ (2 ^ 18) % definingPolynomial = r18 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 17) X_pow_2_pow_17_mod_eq step_18

lemma X_pow_2_pow_19_mod_eq :
    X ^ (2 ^ 19) % definingPolynomial = r19 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 18) X_pow_2_pow_18_mod_eq step_19

lemma X_pow_2_pow_20_mod_eq :
    X ^ (2 ^ 20) % definingPolynomial = r20 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 19) X_pow_2_pow_19_mod_eq step_20

lemma X_pow_2_pow_21_mod_eq :
    X ^ (2 ^ 21) % definingPolynomial = r21 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 20) X_pow_2_pow_20_mod_eq step_21

lemma X_pow_2_pow_22_mod_eq :
    X ^ (2 ^ 22) % definingPolynomial = r22 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 21) X_pow_2_pow_21_mod_eq step_22

lemma X_pow_2_pow_23_mod_eq :
    X ^ (2 ^ 23) % definingPolynomial = r23 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 22) X_pow_2_pow_22_mod_eq step_23

lemma X_pow_2_pow_24_mod_eq :
    X ^ (2 ^ 24) % definingPolynomial = r24 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 23) X_pow_2_pow_23_mod_eq step_24

lemma X_pow_2_pow_25_mod_eq :
    X ^ (2 ^ 25) % definingPolynomial = r25 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 24) X_pow_2_pow_24_mod_eq step_25

lemma X_pow_2_pow_26_mod_eq :
    X ^ (2 ^ 26) % definingPolynomial = r26 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 25) X_pow_2_pow_25_mod_eq step_26

lemma X_pow_2_pow_27_mod_eq :
    X ^ (2 ^ 27) % definingPolynomial = r27 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 26) X_pow_2_pow_26_mod_eq step_27

lemma X_pow_2_pow_28_mod_eq :
    X ^ (2 ^ 28) % definingPolynomial = r28 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 27) X_pow_2_pow_27_mod_eq step_28

lemma X_pow_2_pow_29_mod_eq :
    X ^ (2 ^ 29) % definingPolynomial = r29 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 28) X_pow_2_pow_28_mod_eq step_29

lemma X_pow_2_pow_30_mod_eq :
    X ^ (2 ^ 30) % definingPolynomial = r30 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 29) X_pow_2_pow_29_mod_eq step_30

lemma X_pow_2_pow_31_mod_eq :
    X ^ (2 ^ 31) % definingPolynomial = r31 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 30) X_pow_2_pow_30_mod_eq step_31

lemma X_pow_2_pow_32_mod_eq :
    X ^ (2 ^ 32) % definingPolynomial = r32 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 31) X_pow_2_pow_31_mod_eq step_32

/-- Rabin trace-condition remainder for the GF32 candidate polynomial. -/
lemma X_pow_2_pow_32_add_X_mod_eq_zero :
    (X ^ (2 ^ 32) + X) % definingPolynomial = 0 := by
  rw [CanonicalEuclideanDomain.add_mod_eq (hn := definingPolynomial_ne_zero)]
  rw [X_pow_2_pow_32_mod_eq, r32_eq_X, X_mod_definingPolynomial]
  simp only [CharTwo.add_self_eq_zero, EuclideanDomain.zero_mod]

/-- Rabin trace divisibility condition for the GF32 candidate polynomial. -/
lemma X_pow_2_pow_32_add_X_dvd :
    definingPolynomial ∣ X ^ (2 ^ 32) + X := by
  rw [← EuclideanDomain.mod_eq_zero]
  exact X_pow_2_pow_32_add_X_mod_eq_zero

end GF2_32
