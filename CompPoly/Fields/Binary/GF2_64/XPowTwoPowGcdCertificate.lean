/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_64.XPowTwoPowModCertificate

/-!
# GF(2^64) Rabin GCD Certificate

Kernel-safe Euclidean-division certificate for the Rabin gcd check of
`X ^ 64 + X ^ 4 + X ^ 3 + X + 1`.
-/

namespace GF2_64

open Polynomial

set_option maxRecDepth 1500

private abbrev B128 : Type := BitVec (2 * extensionDegree)

def gcdPVal : B128 := BitVec.ofNat (2 * extensionDegree) 18446744073709551643

/-- Numeric 128-bit encoding of the GF64 defining polynomial. -/
lemma definingPolynomial_eq_gcdPVal :
    definingPolynomial = BinaryField.toPoly gcdPVal := by
  rw [definingPolynomial_eq_P_val]
  have h : P_val = gcdPVal := by
    decide
  rw [h]

/-- Any GF64-width polynomial is already reduced modulo the defining polynomial. -/
lemma toPoly_mod_definingPolynomial_eq_self (v : B64) :
    BinaryField.toPoly v % definingPolynomial = BinaryField.toPoly v := by
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact definingPolynomial_ne_zero)]
  rw [definingPolynomial_degree]
  exact BinaryField.toPoly_degree_lt_w
    (w := extensionDegree) (h_w_pos := by unfold extensionDegree; omega) v

/-- Soundness wrapper specialized to 128-bit Euclidean-division certificates. -/
private theorem verify_div_step {a q b r : B128}
    (h : BinaryField.Extension.checkDivStep (2 * extensionDegree) a q b r = true) :
    BinaryField.toPoly a = BinaryField.toPoly q * BinaryField.toPoly b +
      BinaryField.toPoly r := by
  exact BinaryField.Extension.checkDivStep_correct a q b r h

private theorem toPoly_ne_zero {v : B128} (h : v ≠ 0) :
    BinaryField.toPoly v ≠ 0 :=
  (BinaryField.toPoly_ne_zero_iff_ne_zero v).mpr h

/-- Initial Rabin gcd remainder for exponent `32`. -/
def gcd32_b1Val : B128 := BitVec.ofNat (2 * extensionDegree) 6656922126492271879

lemma gcd32_b1Val_eq_zeroExtend :
    gcd32_b1Val = BitVec.zeroExtend (2 * extensionDegree) (r32Val ^^^ r0Val) := by
  decide

def gcd32_a1Val : B128 := gcdPVal
def gcd32_q1Val : B128 := BitVec.ofNat (2 * extensionDegree) 5
def gcd32_r1Val : B128 := BitVec.ofNat (2 * extensionDegree) 3308649267891572992

def gcd32_a2Val : B128 := gcd32_b1Val
def gcd32_b2Val : B128 := gcd32_r1Val
def gcd32_q2Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r2Val : B128 := BitVec.ofNat (2 * extensionDegree) 556052245088806663

def gcd32_a3Val : B128 := gcd32_b2Val
def gcd32_b3Val : B128 := gcd32_r2Val
def gcd32_q3Val : B128 := BitVec.ofNat (2 * extensionDegree) 14
def gcd32_r3Val : B128 := BitVec.ofNat (2 * extensionDegree) 135773225131735850

def gcd32_a4Val : B128 := gcd32_b3Val
def gcd32_b4Val : B128 := gcd32_r3Val
def gcd32_q4Val : B128 := BitVec.ofNat (2 * extensionDegree) 4
def gcd32_r4Val : B128 := BitVec.ofNat (2 * extensionDegree) 17463060920945583

def gcd32_a5Val : B128 := gcd32_b4Val
def gcd32_b5Val : B128 := gcd32_r4Val
def gcd32_q5Val : B128 := BitVec.ofNat (2 * extensionDegree) 8
def gcd32_r5Val : B128 := BitVec.ofNat (2 * extensionDegree) 5076972710274642

def gcd32_a6Val : B128 := gcd32_b5Val
def gcd32_b6Val : B128 := gcd32_r5Val
def gcd32_q6Val : B128 := BitVec.ofNat (2 * extensionDegree) 3
def gcd32_r6Val : B128 := BitVec.ofNat (2 * extensionDegree) 2270494763000153

def gcd32_a7Val : B128 := gcd32_b6Val
def gcd32_b7Val : B128 := gcd32_r6Val
def gcd32_q7Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r7Val : B128 := BitVec.ofNat (2 * extensionDegree) 610758598485216

def gcd32_a8Val : B128 := gcd32_b7Val
def gcd32_b8Val : B128 := gcd32_r7Val
def gcd32_q8Val : B128 := BitVec.ofNat (2 * extensionDegree) 4
def gcd32_r8Val : B128 := BitVec.ofNat (2 * extensionDegree) 207728323179225

def gcd32_a9Val : B128 := gcd32_b8Val
def gcd32_b9Val : B128 := gcd32_r8Val
def gcd32_q9Val : B128 := BitVec.ofNat (2 * extensionDegree) 5
def gcd32_r9Val : B128 := BitVec.ofNat (2 * extensionDegree) 110091923692893

def gcd32_a10Val : B128 := gcd32_b9Val
def gcd32_b10Val : B128 := gcd32_r9Val
def gcd32_q10Val : B128 := BitVec.ofNat (2 * extensionDegree) 3
def gcd32_r10Val : B128 := BitVec.ofNat (2 * extensionDegree) 18196952945982

def gcd32_a11Val : B128 := gcd32_b10Val
def gcd32_b11Val : B128 := gcd32_r10Val
def gcd32_q11Val : B128 := BitVec.ofNat (2 * extensionDegree) 6
def gcd32_r11Val : B128 := BitVec.ofNat (2 * extensionDegree) 7741149963225

def gcd32_a12Val : B128 := gcd32_b11Val
def gcd32_b12Val : B128 := gcd32_r11Val
def gcd32_q12Val : B128 := BitVec.ofNat (2 * extensionDegree) 6
def gcd32_r12Val : B128 := BitVec.ofNat (2 * extensionDegree) 2961647328744

def gcd32_a13Val : B128 := gcd32_b12Val
def gcd32_b13Val : B128 := gcd32_r12Val
def gcd32_q13Val : B128 := BitVec.ofNat (2 * extensionDegree) 3
def gcd32_r13Val : B128 := BitVec.ofNat (2 * extensionDegree) 931744581089

def gcd32_a14Val : B128 := gcd32_b13Val
def gcd32_b14Val : B128 := gcd32_r13Val
def gcd32_q14Val : B128 := BitVec.ofNat (2 * extensionDegree) 6
def gcd32_r14Val : B128 := BitVec.ofNat (2 * extensionDegree) 428125962670

def gcd32_a15Val : B128 := gcd32_b14Val
def gcd32_b15Val : B128 := gcd32_r14Val
def gcd32_q15Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r15Val : B128 := BitVec.ofNat (2 * extensionDegree) 136043923133

def gcd32_a16Val : B128 := gcd32_b15Val
def gcd32_b16Val : B128 := gcd32_r15Val
def gcd32_q16Val : B128 := BitVec.ofNat (2 * extensionDegree) 5
def gcd32_r16Val : B128 := BitVec.ofNat (2 * extensionDegree) 11575516647

def gcd32_a17Val : B128 := gcd32_b16Val
def gcd32_b17Val : B128 := gcd32_r16Val
def gcd32_q17Val : B128 := BitVec.ofNat (2 * extensionDegree) 12
def gcd32_r17Val : B128 := BitVec.ofNat (2 * extensionDegree) 3836354073

def gcd32_a18Val : B128 := gcd32_b17Val
def gcd32_b18Val : B128 := gcd32_r17Val
def gcd32_q18Val : B128 := BitVec.ofNat (2 * extensionDegree) 7
def gcd32_r18Val : B128 := BitVec.ofNat (2 * extensionDegree) 245499816

def gcd32_a19Val : B128 := gcd32_b18Val
def gcd32_b19Val : B128 := gcd32_r18Val
def gcd32_q19Val : B128 := BitVec.ofNat (2 * extensionDegree) 17
def gcd32_r19Val : B128 := BitVec.ofNat (2 * extensionDegree) 2646833

def gcd32_a20Val : B128 := gcd32_b19Val
def gcd32_b20Val : B128 := gcd32_r19Val
def gcd32_q20Val : B128 := BitVec.ofNat (2 * extensionDegree) 110
def gcd32_r20Val : B128 := BitVec.ofNat (2 * extensionDegree) 327398

def gcd32_a21Val : B128 := gcd32_b20Val
def gcd32_b21Val : B128 := gcd32_r20Val
def gcd32_q21Val : B128 := BitVec.ofNat (2 * extensionDegree) 11
def gcd32_r21Val : B128 := BitVec.ofNat (2 * extensionDegree) 169771

def gcd32_a22Val : B128 := gcd32_b21Val
def gcd32_b22Val : B128 := gcd32_r21Val
def gcd32_q22Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r22Val : B128 := BitVec.ofNat (2 * extensionDegree) 118960

def gcd32_a23Val : B128 := gcd32_b22Val
def gcd32_b23Val : B128 := gcd32_r22Val
def gcd32_q23Val : B128 := BitVec.ofNat (2 * extensionDegree) 3
def gcd32_r23Val : B128 := BitVec.ofNat (2 * extensionDegree) 59131

def gcd32_a24Val : B128 := gcd32_b23Val
def gcd32_b24Val : B128 := gcd32_r23Val
def gcd32_q24Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r24Val : B128 := BitVec.ofNat (2 * extensionDegree) 7494

def gcd32_a25Val : B128 := gcd32_b24Val
def gcd32_b25Val : B128 := gcd32_r24Val
def gcd32_q25Val : B128 := BitVec.ofNat (2 * extensionDegree) 8
def gcd32_r25Val : B128 := BitVec.ofNat (2 * extensionDegree) 3275

def gcd32_a26Val : B128 := gcd32_b25Val
def gcd32_b26Val : B128 := gcd32_r25Val
def gcd32_q26Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r26Val : B128 := BitVec.ofNat (2 * extensionDegree) 1232

def gcd32_a27Val : B128 := gcd32_b26Val
def gcd32_b27Val : B128 := gcd32_r26Val
def gcd32_q27Val : B128 := BitVec.ofNat (2 * extensionDegree) 3
def gcd32_r27Val : B128 := BitVec.ofNat (2 * extensionDegree) 443

def gcd32_a28Val : B128 := gcd32_b27Val
def gcd32_b28Val : B128 := gcd32_r27Val
def gcd32_q28Val : B128 := BitVec.ofNat (2 * extensionDegree) 7
def gcd32_r28Val : B128 := BitVec.ofNat (2 * extensionDegree) 241

def gcd32_a29Val : B128 := gcd32_b28Val
def gcd32_b29Val : B128 := gcd32_r28Val
def gcd32_q29Val : B128 := BitVec.ofNat (2 * extensionDegree) 2
def gcd32_r29Val : B128 := BitVec.ofNat (2 * extensionDegree) 89

def gcd32_a30Val : B128 := gcd32_b29Val
def gcd32_b30Val : B128 := gcd32_r29Val
def gcd32_q30Val : B128 := BitVec.ofNat (2 * extensionDegree) 3
def gcd32_r30Val : B128 := BitVec.ofNat (2 * extensionDegree) 26

def gcd32_a31Val : B128 := gcd32_b30Val
def gcd32_b31Val : B128 := gcd32_r30Val
def gcd32_q31Val : B128 := BitVec.ofNat (2 * extensionDegree) 6
def gcd32_r31Val : B128 := BitVec.ofNat (2 * extensionDegree) 5

def gcd32_a32Val : B128 := gcd32_b31Val
def gcd32_b32Val : B128 := gcd32_r31Val
def gcd32_q32Val : B128 := BitVec.ofNat (2 * extensionDegree) 7
def gcd32_r32Val : B128 := BitVec.ofNat (2 * extensionDegree) 1

def gcd32_a33Val : B128 := gcd32_b32Val
def gcd32_b33Val : B128 := gcd32_r32Val
def gcd32_q33Val : B128 := BitVec.ofNat (2 * extensionDegree) 5
def gcd32_r33Val : B128 := BitVec.ofNat (2 * extensionDegree) 0

/-- Reduce the exponent `32` Rabin gcd to the generated Euclidean trace. -/
lemma gcd32_start_reduction :
    EuclideanDomain.gcd (X ^ (2 ^ 32) + X) definingPolynomial =
      EuclideanDomain.gcd definingPolynomial (BinaryField.toPoly gcd32_b1Val) := by
  rw [ZMod2Poly.euclidean_gcd_comm]
  rw [EuclideanDomain.gcd_val]
  conv_lhs =>
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := definingPolynomial_ne_zero)]
    rw [X_pow_2_pow_32_mod_eq]
    rw [r32]
    rw [toPoly_mod_definingPolynomial_eq_self r32Val, X_mod_definingPolynomial]
    rw [← r0_eq_X]
    rw [r0]
    rw [← BinaryField.toPoly_xor]
    rw [toPoly_mod_definingPolynomial_eq_self (r32Val ^^^ r0Val)]
    rw [← BinaryField.Extension.toPoly_zeroExtend
      (show extensionDegree ≤ 2 * extensionDegree by unfold extensionDegree; norm_num)
      (r32Val ^^^ r0Val)]
    rw [← gcd32_b1Val_eq_zeroExtend]
    rw [ZMod2Poly.euclidean_gcd_comm]

lemma gcd32_step_1 :
    BinaryField.toPoly gcd32_a1Val =
      BinaryField.toPoly gcd32_q1Val * BinaryField.toPoly gcd32_b1Val +
        BinaryField.toPoly gcd32_r1Val := by
  exact verify_div_step (a := gcd32_a1Val) (q := gcd32_q1Val)
    (b := gcd32_b1Val) (r := gcd32_r1Val) (by rfl)

lemma gcd32_step_2 :
    BinaryField.toPoly gcd32_a2Val =
      BinaryField.toPoly gcd32_q2Val * BinaryField.toPoly gcd32_b2Val +
        BinaryField.toPoly gcd32_r2Val := by
  exact verify_div_step (a := gcd32_a2Val) (q := gcd32_q2Val)
    (b := gcd32_b2Val) (r := gcd32_r2Val) (by rfl)

lemma gcd32_step_3 :
    BinaryField.toPoly gcd32_a3Val =
      BinaryField.toPoly gcd32_q3Val * BinaryField.toPoly gcd32_b3Val +
        BinaryField.toPoly gcd32_r3Val := by
  exact verify_div_step (a := gcd32_a3Val) (q := gcd32_q3Val)
    (b := gcd32_b3Val) (r := gcd32_r3Val) (by rfl)

lemma gcd32_step_4 :
    BinaryField.toPoly gcd32_a4Val =
      BinaryField.toPoly gcd32_q4Val * BinaryField.toPoly gcd32_b4Val +
        BinaryField.toPoly gcd32_r4Val := by
  exact verify_div_step (a := gcd32_a4Val) (q := gcd32_q4Val)
    (b := gcd32_b4Val) (r := gcd32_r4Val) (by rfl)

lemma gcd32_step_5 :
    BinaryField.toPoly gcd32_a5Val =
      BinaryField.toPoly gcd32_q5Val * BinaryField.toPoly gcd32_b5Val +
        BinaryField.toPoly gcd32_r5Val := by
  exact verify_div_step (a := gcd32_a5Val) (q := gcd32_q5Val)
    (b := gcd32_b5Val) (r := gcd32_r5Val) (by rfl)

lemma gcd32_step_6 :
    BinaryField.toPoly gcd32_a6Val =
      BinaryField.toPoly gcd32_q6Val * BinaryField.toPoly gcd32_b6Val +
        BinaryField.toPoly gcd32_r6Val := by
  exact verify_div_step (a := gcd32_a6Val) (q := gcd32_q6Val)
    (b := gcd32_b6Val) (r := gcd32_r6Val) (by rfl)

lemma gcd32_step_7 :
    BinaryField.toPoly gcd32_a7Val =
      BinaryField.toPoly gcd32_q7Val * BinaryField.toPoly gcd32_b7Val +
        BinaryField.toPoly gcd32_r7Val := by
  exact verify_div_step (a := gcd32_a7Val) (q := gcd32_q7Val)
    (b := gcd32_b7Val) (r := gcd32_r7Val) (by rfl)

lemma gcd32_step_8 :
    BinaryField.toPoly gcd32_a8Val =
      BinaryField.toPoly gcd32_q8Val * BinaryField.toPoly gcd32_b8Val +
        BinaryField.toPoly gcd32_r8Val := by
  exact verify_div_step (a := gcd32_a8Val) (q := gcd32_q8Val)
    (b := gcd32_b8Val) (r := gcd32_r8Val) (by rfl)

lemma gcd32_step_9 :
    BinaryField.toPoly gcd32_a9Val =
      BinaryField.toPoly gcd32_q9Val * BinaryField.toPoly gcd32_b9Val +
        BinaryField.toPoly gcd32_r9Val := by
  exact verify_div_step (a := gcd32_a9Val) (q := gcd32_q9Val)
    (b := gcd32_b9Val) (r := gcd32_r9Val) (by rfl)

lemma gcd32_step_10 :
    BinaryField.toPoly gcd32_a10Val =
      BinaryField.toPoly gcd32_q10Val * BinaryField.toPoly gcd32_b10Val +
        BinaryField.toPoly gcd32_r10Val := by
  exact verify_div_step (a := gcd32_a10Val) (q := gcd32_q10Val)
    (b := gcd32_b10Val) (r := gcd32_r10Val) (by rfl)

lemma gcd32_step_11 :
    BinaryField.toPoly gcd32_a11Val =
      BinaryField.toPoly gcd32_q11Val * BinaryField.toPoly gcd32_b11Val +
        BinaryField.toPoly gcd32_r11Val := by
  exact verify_div_step (a := gcd32_a11Val) (q := gcd32_q11Val)
    (b := gcd32_b11Val) (r := gcd32_r11Val) (by rfl)

lemma gcd32_step_12 :
    BinaryField.toPoly gcd32_a12Val =
      BinaryField.toPoly gcd32_q12Val * BinaryField.toPoly gcd32_b12Val +
        BinaryField.toPoly gcd32_r12Val := by
  exact verify_div_step (a := gcd32_a12Val) (q := gcd32_q12Val)
    (b := gcd32_b12Val) (r := gcd32_r12Val) (by rfl)

lemma gcd32_step_13 :
    BinaryField.toPoly gcd32_a13Val =
      BinaryField.toPoly gcd32_q13Val * BinaryField.toPoly gcd32_b13Val +
        BinaryField.toPoly gcd32_r13Val := by
  exact verify_div_step (a := gcd32_a13Val) (q := gcd32_q13Val)
    (b := gcd32_b13Val) (r := gcd32_r13Val) (by rfl)

lemma gcd32_step_14 :
    BinaryField.toPoly gcd32_a14Val =
      BinaryField.toPoly gcd32_q14Val * BinaryField.toPoly gcd32_b14Val +
        BinaryField.toPoly gcd32_r14Val := by
  exact verify_div_step (a := gcd32_a14Val) (q := gcd32_q14Val)
    (b := gcd32_b14Val) (r := gcd32_r14Val) (by rfl)

lemma gcd32_step_15 :
    BinaryField.toPoly gcd32_a15Val =
      BinaryField.toPoly gcd32_q15Val * BinaryField.toPoly gcd32_b15Val +
        BinaryField.toPoly gcd32_r15Val := by
  exact verify_div_step (a := gcd32_a15Val) (q := gcd32_q15Val)
    (b := gcd32_b15Val) (r := gcd32_r15Val) (by rfl)

lemma gcd32_step_16 :
    BinaryField.toPoly gcd32_a16Val =
      BinaryField.toPoly gcd32_q16Val * BinaryField.toPoly gcd32_b16Val +
        BinaryField.toPoly gcd32_r16Val := by
  exact verify_div_step (a := gcd32_a16Val) (q := gcd32_q16Val)
    (b := gcd32_b16Val) (r := gcd32_r16Val) (by rfl)

lemma gcd32_step_17 :
    BinaryField.toPoly gcd32_a17Val =
      BinaryField.toPoly gcd32_q17Val * BinaryField.toPoly gcd32_b17Val +
        BinaryField.toPoly gcd32_r17Val := by
  exact verify_div_step (a := gcd32_a17Val) (q := gcd32_q17Val)
    (b := gcd32_b17Val) (r := gcd32_r17Val) (by rfl)

lemma gcd32_step_18 :
    BinaryField.toPoly gcd32_a18Val =
      BinaryField.toPoly gcd32_q18Val * BinaryField.toPoly gcd32_b18Val +
        BinaryField.toPoly gcd32_r18Val := by
  exact verify_div_step (a := gcd32_a18Val) (q := gcd32_q18Val)
    (b := gcd32_b18Val) (r := gcd32_r18Val) (by rfl)

lemma gcd32_step_19 :
    BinaryField.toPoly gcd32_a19Val =
      BinaryField.toPoly gcd32_q19Val * BinaryField.toPoly gcd32_b19Val +
        BinaryField.toPoly gcd32_r19Val := by
  exact verify_div_step (a := gcd32_a19Val) (q := gcd32_q19Val)
    (b := gcd32_b19Val) (r := gcd32_r19Val) (by rfl)

lemma gcd32_step_20 :
    BinaryField.toPoly gcd32_a20Val =
      BinaryField.toPoly gcd32_q20Val * BinaryField.toPoly gcd32_b20Val +
        BinaryField.toPoly gcd32_r20Val := by
  exact verify_div_step (a := gcd32_a20Val) (q := gcd32_q20Val)
    (b := gcd32_b20Val) (r := gcd32_r20Val) (by rfl)

lemma gcd32_step_21 :
    BinaryField.toPoly gcd32_a21Val =
      BinaryField.toPoly gcd32_q21Val * BinaryField.toPoly gcd32_b21Val +
        BinaryField.toPoly gcd32_r21Val := by
  exact verify_div_step (a := gcd32_a21Val) (q := gcd32_q21Val)
    (b := gcd32_b21Val) (r := gcd32_r21Val) (by rfl)

lemma gcd32_step_22 :
    BinaryField.toPoly gcd32_a22Val =
      BinaryField.toPoly gcd32_q22Val * BinaryField.toPoly gcd32_b22Val +
        BinaryField.toPoly gcd32_r22Val := by
  exact verify_div_step (a := gcd32_a22Val) (q := gcd32_q22Val)
    (b := gcd32_b22Val) (r := gcd32_r22Val) (by rfl)

lemma gcd32_step_23 :
    BinaryField.toPoly gcd32_a23Val =
      BinaryField.toPoly gcd32_q23Val * BinaryField.toPoly gcd32_b23Val +
        BinaryField.toPoly gcd32_r23Val := by
  exact verify_div_step (a := gcd32_a23Val) (q := gcd32_q23Val)
    (b := gcd32_b23Val) (r := gcd32_r23Val) (by rfl)

lemma gcd32_step_24 :
    BinaryField.toPoly gcd32_a24Val =
      BinaryField.toPoly gcd32_q24Val * BinaryField.toPoly gcd32_b24Val +
        BinaryField.toPoly gcd32_r24Val := by
  exact verify_div_step (a := gcd32_a24Val) (q := gcd32_q24Val)
    (b := gcd32_b24Val) (r := gcd32_r24Val) (by rfl)

lemma gcd32_step_25 :
    BinaryField.toPoly gcd32_a25Val =
      BinaryField.toPoly gcd32_q25Val * BinaryField.toPoly gcd32_b25Val +
        BinaryField.toPoly gcd32_r25Val := by
  exact verify_div_step (a := gcd32_a25Val) (q := gcd32_q25Val)
    (b := gcd32_b25Val) (r := gcd32_r25Val) (by rfl)

lemma gcd32_step_26 :
    BinaryField.toPoly gcd32_a26Val =
      BinaryField.toPoly gcd32_q26Val * BinaryField.toPoly gcd32_b26Val +
        BinaryField.toPoly gcd32_r26Val := by
  exact verify_div_step (a := gcd32_a26Val) (q := gcd32_q26Val)
    (b := gcd32_b26Val) (r := gcd32_r26Val) (by rfl)

lemma gcd32_step_27 :
    BinaryField.toPoly gcd32_a27Val =
      BinaryField.toPoly gcd32_q27Val * BinaryField.toPoly gcd32_b27Val +
        BinaryField.toPoly gcd32_r27Val := by
  exact verify_div_step (a := gcd32_a27Val) (q := gcd32_q27Val)
    (b := gcd32_b27Val) (r := gcd32_r27Val) (by rfl)

lemma gcd32_step_28 :
    BinaryField.toPoly gcd32_a28Val =
      BinaryField.toPoly gcd32_q28Val * BinaryField.toPoly gcd32_b28Val +
        BinaryField.toPoly gcd32_r28Val := by
  exact verify_div_step (a := gcd32_a28Val) (q := gcd32_q28Val)
    (b := gcd32_b28Val) (r := gcd32_r28Val) (by rfl)

lemma gcd32_step_29 :
    BinaryField.toPoly gcd32_a29Val =
      BinaryField.toPoly gcd32_q29Val * BinaryField.toPoly gcd32_b29Val +
        BinaryField.toPoly gcd32_r29Val := by
  exact verify_div_step (a := gcd32_a29Val) (q := gcd32_q29Val)
    (b := gcd32_b29Val) (r := gcd32_r29Val) (by rfl)

lemma gcd32_step_30 :
    BinaryField.toPoly gcd32_a30Val =
      BinaryField.toPoly gcd32_q30Val * BinaryField.toPoly gcd32_b30Val +
        BinaryField.toPoly gcd32_r30Val := by
  exact verify_div_step (a := gcd32_a30Val) (q := gcd32_q30Val)
    (b := gcd32_b30Val) (r := gcd32_r30Val) (by rfl)

lemma gcd32_step_31 :
    BinaryField.toPoly gcd32_a31Val =
      BinaryField.toPoly gcd32_q31Val * BinaryField.toPoly gcd32_b31Val +
        BinaryField.toPoly gcd32_r31Val := by
  exact verify_div_step (a := gcd32_a31Val) (q := gcd32_q31Val)
    (b := gcd32_b31Val) (r := gcd32_r31Val) (by rfl)

lemma gcd32_step_32 :
    BinaryField.toPoly gcd32_a32Val =
      BinaryField.toPoly gcd32_q32Val * BinaryField.toPoly gcd32_b32Val +
        BinaryField.toPoly gcd32_r32Val := by
  exact verify_div_step (a := gcd32_a32Val) (q := gcd32_q32Val)
    (b := gcd32_b32Val) (r := gcd32_r32Val) (by rfl)

lemma gcd32_step_33 :
    BinaryField.toPoly gcd32_a33Val =
      BinaryField.toPoly gcd32_q33Val * BinaryField.toPoly gcd32_b33Val +
        BinaryField.toPoly gcd32_r33Val := by
  exact verify_div_step (a := gcd32_a33Val) (q := gcd32_q33Val)
    (b := gcd32_b33Val) (r := gcd32_r33Val) (by rfl)

/-- Rabin gcd condition for exponent `32`. -/
lemma rabin_gcd_condition_32 :
    EuclideanDomain.gcd (X ^ (2 ^ 32) + X) definingPolynomial = 1 := by
  rw [gcd32_start_reduction]
  rw [definingPolynomial_eq_gcdPVal]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a1Val)
    (BinaryField.toPoly gcd32_b1Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b1Val) (by decide))
    gcd32_step_1]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a2Val)
    (BinaryField.toPoly gcd32_b2Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b2Val) (by decide))
    gcd32_step_2]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a3Val)
    (BinaryField.toPoly gcd32_b3Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b3Val) (by decide))
    gcd32_step_3]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a4Val)
    (BinaryField.toPoly gcd32_b4Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b4Val) (by decide))
    gcd32_step_4]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a5Val)
    (BinaryField.toPoly gcd32_b5Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b5Val) (by decide))
    gcd32_step_5]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a6Val)
    (BinaryField.toPoly gcd32_b6Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b6Val) (by decide))
    gcd32_step_6]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a7Val)
    (BinaryField.toPoly gcd32_b7Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b7Val) (by decide))
    gcd32_step_7]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a8Val)
    (BinaryField.toPoly gcd32_b8Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b8Val) (by decide))
    gcd32_step_8]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a9Val)
    (BinaryField.toPoly gcd32_b9Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b9Val) (by decide))
    gcd32_step_9]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a10Val)
    (BinaryField.toPoly gcd32_b10Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b10Val) (by decide))
    gcd32_step_10]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a11Val)
    (BinaryField.toPoly gcd32_b11Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b11Val) (by decide))
    gcd32_step_11]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a12Val)
    (BinaryField.toPoly gcd32_b12Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b12Val) (by decide))
    gcd32_step_12]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a13Val)
    (BinaryField.toPoly gcd32_b13Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b13Val) (by decide))
    gcd32_step_13]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a14Val)
    (BinaryField.toPoly gcd32_b14Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b14Val) (by decide))
    gcd32_step_14]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a15Val)
    (BinaryField.toPoly gcd32_b15Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b15Val) (by decide))
    gcd32_step_15]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a16Val)
    (BinaryField.toPoly gcd32_b16Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b16Val) (by decide))
    gcd32_step_16]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a17Val)
    (BinaryField.toPoly gcd32_b17Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b17Val) (by decide))
    gcd32_step_17]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a18Val)
    (BinaryField.toPoly gcd32_b18Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b18Val) (by decide))
    gcd32_step_18]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a19Val)
    (BinaryField.toPoly gcd32_b19Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b19Val) (by decide))
    gcd32_step_19]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a20Val)
    (BinaryField.toPoly gcd32_b20Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b20Val) (by decide))
    gcd32_step_20]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a21Val)
    (BinaryField.toPoly gcd32_b21Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b21Val) (by decide))
    gcd32_step_21]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a22Val)
    (BinaryField.toPoly gcd32_b22Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b22Val) (by decide))
    gcd32_step_22]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a23Val)
    (BinaryField.toPoly gcd32_b23Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b23Val) (by decide))
    gcd32_step_23]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a24Val)
    (BinaryField.toPoly gcd32_b24Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b24Val) (by decide))
    gcd32_step_24]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a25Val)
    (BinaryField.toPoly gcd32_b25Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b25Val) (by decide))
    gcd32_step_25]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a26Val)
    (BinaryField.toPoly gcd32_b26Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b26Val) (by decide))
    gcd32_step_26]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a27Val)
    (BinaryField.toPoly gcd32_b27Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b27Val) (by decide))
    gcd32_step_27]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a28Val)
    (BinaryField.toPoly gcd32_b28Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b28Val) (by decide))
    gcd32_step_28]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a29Val)
    (BinaryField.toPoly gcd32_b29Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b29Val) (by decide))
    gcd32_step_29]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a30Val)
    (BinaryField.toPoly gcd32_b30Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b30Val) (by decide))
    gcd32_step_30]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a31Val)
    (BinaryField.toPoly gcd32_b31Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b31Val) (by decide))
    gcd32_step_31]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a32Val)
    (BinaryField.toPoly gcd32_b32Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b32Val) (by decide))
    gcd32_step_32]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd32_a33Val)
    (BinaryField.toPoly gcd32_b33Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd32_b33Val) (by decide))
    gcd32_step_33]
  change EuclideanDomain.gcd
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 1 : B128))
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 0 : B128)) = 1
  rw [BinaryField.toPoly_one_eq_one
    (w := 2 * extensionDegree) (h_w_pos := by unfold extensionDegree; omega)]
  rw [BinaryField.toPoly_zero_eq_zero]
  exact BinaryField.gcd_one_zero

end GF2_64
