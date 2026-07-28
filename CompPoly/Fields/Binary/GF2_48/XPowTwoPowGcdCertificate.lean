/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_48.XPowTwoPowModCertificate

/-!
# GF(2^48) Rabin GCD Certificate

Kernel-safe Euclidean-division certificates for the two Rabin gcd checks of
`X^48 + X^9 + X^7 + X^4 + 1`.
-/

namespace GF2_48

open Polynomial

set_option maxRecDepth 1500

private abbrev B96 : Type := BitVec (2 * extensionDegree)

def gcdPVal : B96 := BitVec.ofNat (2 * extensionDegree) 281474976711313

/-- Numeric 96-bit encoding of the GF48 defining polynomial. -/
lemma definingPolynomial_eq_gcdPVal :
    definingPolynomial = BinaryField.toPoly gcdPVal := by
  rw [definingPolynomial_eq_P_val]
  have h : P_val = gcdPVal := by
    decide
  rw [h]

/-- Any GF48-width polynomial is already reduced modulo the defining polynomial. -/
lemma toPoly_mod_definingPolynomial_eq_self (v : B48) :
    BinaryField.toPoly v % definingPolynomial = BinaryField.toPoly v := by
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact definingPolynomial_ne_zero)]
  rw [definingPolynomial_degree]
  exact BinaryField.toPoly_degree_lt_w
    (w := extensionDegree) (h_w_pos := by unfold extensionDegree; omega) v

/-- Soundness wrapper specialized to 96-bit Euclidean-division certificates. -/
private theorem verify_div_step {a q b r : B96}
    (h : BinaryField.Extension.checkDivStep (2 * extensionDegree) a q b r = true) :
    BinaryField.toPoly a = BinaryField.toPoly q * BinaryField.toPoly b +
      BinaryField.toPoly r := by
  exact BinaryField.Extension.checkDivStep_correct a q b r h

private theorem toPoly_ne_zero {v : B96} (h : v ≠ 0) :
    BinaryField.toPoly v ≠ 0 :=
  (BinaryField.toPoly_ne_zero_iff_ne_zero v).mpr h

/-- Initial Rabin gcd remainder for exponent `24`. -/
def gcd24_b1Val : B96 := BitVec.ofNat (2 * extensionDegree) 221427043524971

lemma gcd24_b1Val_eq_zeroExtend :
    gcd24_b1Val = BitVec.zeroExtend (2 * extensionDegree) (r24Val ^^^ r0Val) := by
  decide

def gcd24_a1Val : B96 := gcdPVal
def gcd24_q1Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r1Val : B96 := BitVec.ofNat (2 * extensionDegree) 100764241240364

def gcd24_a2Val : B96 := gcd24_b1Val
def gcd24_b2Val : B96 := gcd24_r1Val
def gcd24_q2Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r2Val : B96 := BitVec.ofNat (2 * extensionDegree) 41283243967007

def gcd24_a3Val : B96 := gcd24_b2Val
def gcd24_b3Val : B96 := gcd24_r2Val
def gcd24_q3Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r3Val : B96 := BitVec.ofNat (2 * extensionDegree) 18403983172882

def gcd24_a4Val : B96 := gcd24_b3Val
def gcd24_b4Val : B96 := gcd24_r3Val
def gcd24_q4Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r4Val : B96 := BitVec.ofNat (2 * extensionDegree) 5454689585211

def gcd24_a5Val : B96 := gcd24_b4Val
def gcd24_b5Val : B96 := gcd24_r4Val
def gcd24_q5Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r5Val : B96 := BitVec.ofNat (2 * extensionDegree) 3732623721982

def gcd24_a6Val : B96 := gcd24_b5Val
def gcd24_b6Val : B96 := gcd24_r5Val
def gcd24_q6Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r6Val : B96 := BitVec.ofNat (2 * extensionDegree) 1482670720569

def gcd24_a7Val : B96 := gcd24_b6Val
def gcd24_b7Val : B96 := gcd24_r6Val
def gcd24_q7Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r7Val : B96 := BitVec.ofNat (2 * extensionDegree) 611154546613

def gcd24_a8Val : B96 := gcd24_b7Val
def gcd24_b8Val : B96 := gcd24_r7Val
def gcd24_q8Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r8Val : B96 := BitVec.ofNat (2 * extensionDegree) 299058288979

def gcd24_a9Val : B96 := gcd24_b8Val
def gcd24_b9Val : B96 := gcd24_r8Val
def gcd24_q9Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r9Val : B96 := BitVec.ofNat (2 * extensionDegree) 21627993363

def gcd24_a10Val : B96 := gcd24_b9Val
def gcd24_b10Val : B96 := gcd24_r9Val
def gcd24_q10Val : B96 := BitVec.ofNat (2 * extensionDegree) 20
def gcd24_r10Val : B96 := BitVec.ofNat (2 * extensionDegree) 4694441007

def gcd24_a11Val : B96 := gcd24_b10Val
def gcd24_b11Val : B96 := gcd24_r10Val
def gcd24_q11Val : B96 := BitVec.ofNat (2 * extensionDegree) 5
def gcd24_r11Val : B96 := BitVec.ofNat (2 * extensionDegree) 1104310656

def gcd24_a12Val : B96 := gcd24_b11Val
def gcd24_b12Val : B96 := gcd24_r11Val
def gcd24_q12Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r12Val : B96 := BitVec.ofNat (2 * extensionDegree) 277264943

def gcd24_a13Val : B96 := gcd24_b12Val
def gcd24_b13Val : B96 := gcd24_r12Val
def gcd24_q13Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r13Val : B96 := BitVec.ofNat (2 * extensionDegree) 63478076

def gcd24_a14Val : B96 := gcd24_b13Val
def gcd24_b14Val : B96 := gcd24_r13Val
def gcd24_q14Val : B96 := BitVec.ofNat (2 * extensionDegree) 12
def gcd24_r14Val : B96 := BitVec.ofNat (2 * extensionDegree) 31463231

def gcd24_a15Val : B96 := gcd24_b14Val
def gcd24_b15Val : B96 := gcd24_r14Val
def gcd24_q15Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r15Val : B96 := BitVec.ofNat (2 * extensionDegree) 571202

def gcd24_a16Val : B96 := gcd24_b15Val
def gcd24_b16Val : B96 := gcd24_r15Val
def gcd24_q16Val : B96 := BitVec.ofNat (2 * extensionDegree) 63
def gcd24_r16Val : B96 := BitVec.ofNat (2 * extensionDegree) 210305

def gcd24_a17Val : B96 := gcd24_b16Val
def gcd24_b17Val : B96 := gcd24_r16Val
def gcd24_q17Val : B96 := BitVec.ofNat (2 * extensionDegree) 7
def gcd24_r17Val : B96 := BitVec.ofNat (2 * extensionDegree) 81861

def gcd24_a18Val : B96 := gcd24_b17Val
def gcd24_b18Val : B96 := gcd24_r17Val
def gcd24_q18Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r18Val : B96 := BitVec.ofNat (2 * extensionDegree) 30158

def gcd24_a19Val : B96 := gcd24_b18Val
def gcd24_b19Val : B96 := gcd24_r18Val
def gcd24_q19Val : B96 := BitVec.ofNat (2 * extensionDegree) 6
def gcd24_r19Val : B96 := BitVec.ofNat (2 * extensionDegree) 865

def gcd24_a20Val : B96 := gcd24_b19Val
def gcd24_b20Val : B96 := gcd24_r19Val
def gcd24_q20Val : B96 := BitVec.ofNat (2 * extensionDegree) 41
def gcd24_r20Val : B96 := BitVec.ofNat (2 * extensionDegree) 391

def gcd24_a21Val : B96 := gcd24_b20Val
def gcd24_b21Val : B96 := gcd24_r20Val
def gcd24_q21Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r21Val : B96 := BitVec.ofNat (2 * extensionDegree) 111

def gcd24_a22Val : B96 := gcd24_b21Val
def gcd24_b22Val : B96 := gcd24_r21Val
def gcd24_q22Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r22Val : B96 := BitVec.ofNat (2 * extensionDegree) 59

def gcd24_a23Val : B96 := gcd24_b22Val
def gcd24_b23Val : B96 := gcd24_r22Val
def gcd24_q23Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r23Val : B96 := BitVec.ofNat (2 * extensionDegree) 25

def gcd24_a24Val : B96 := gcd24_b23Val
def gcd24_b24Val : B96 := gcd24_r23Val
def gcd24_q24Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r24Val : B96 := BitVec.ofNat (2 * extensionDegree) 9

def gcd24_a25Val : B96 := gcd24_b24Val
def gcd24_b25Val : B96 := gcd24_r24Val
def gcd24_q25Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r25Val : B96 := BitVec.ofNat (2 * extensionDegree) 2

def gcd24_a26Val : B96 := gcd24_b25Val
def gcd24_b26Val : B96 := gcd24_r25Val
def gcd24_q26Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r26Val : B96 := BitVec.ofNat (2 * extensionDegree) 1

def gcd24_a27Val : B96 := gcd24_b26Val
def gcd24_b27Val : B96 := gcd24_r26Val
def gcd24_q27Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r27Val : B96 := BitVec.ofNat (2 * extensionDegree) 0

/-- Reduce the exponent `24` Rabin gcd to the generated Euclidean trace. -/
lemma gcd24_start_reduction :
    EuclideanDomain.gcd (X ^ (2 ^ 24) + X) definingPolynomial =
      EuclideanDomain.gcd definingPolynomial (BinaryField.toPoly gcd24_b1Val) := by
  rw [ZMod2Poly.euclidean_gcd_comm]
  rw [EuclideanDomain.gcd_val]
  conv_lhs =>
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := definingPolynomial_ne_zero)]
    rw [X_pow_2_pow_24_mod_eq]
    rw [r24]
    rw [toPoly_mod_definingPolynomial_eq_self r24Val, X_mod_definingPolynomial]
    rw [← r0_eq_X]
    rw [r0]
    rw [← BinaryField.toPoly_xor]
    rw [toPoly_mod_definingPolynomial_eq_self (r24Val ^^^ r0Val)]
    rw [← BinaryField.Extension.toPoly_zeroExtend
      (show extensionDegree ≤ 2 * extensionDegree by unfold extensionDegree; norm_num)
      (r24Val ^^^ r0Val)]
    rw [← gcd24_b1Val_eq_zeroExtend]
    rw [ZMod2Poly.euclidean_gcd_comm]

lemma gcd24_step_1 :
    BinaryField.toPoly gcd24_a1Val =
      BinaryField.toPoly gcd24_q1Val * BinaryField.toPoly gcd24_b1Val +
        BinaryField.toPoly gcd24_r1Val := by
  exact verify_div_step (a := gcd24_a1Val) (q := gcd24_q1Val)
    (b := gcd24_b1Val) (r := gcd24_r1Val) (by rfl)

lemma gcd24_step_2 :
    BinaryField.toPoly gcd24_a2Val =
      BinaryField.toPoly gcd24_q2Val * BinaryField.toPoly gcd24_b2Val +
        BinaryField.toPoly gcd24_r2Val := by
  exact verify_div_step (a := gcd24_a2Val) (q := gcd24_q2Val)
    (b := gcd24_b2Val) (r := gcd24_r2Val) (by rfl)

lemma gcd24_step_3 :
    BinaryField.toPoly gcd24_a3Val =
      BinaryField.toPoly gcd24_q3Val * BinaryField.toPoly gcd24_b3Val +
        BinaryField.toPoly gcd24_r3Val := by
  exact verify_div_step (a := gcd24_a3Val) (q := gcd24_q3Val)
    (b := gcd24_b3Val) (r := gcd24_r3Val) (by rfl)

lemma gcd24_step_4 :
    BinaryField.toPoly gcd24_a4Val =
      BinaryField.toPoly gcd24_q4Val * BinaryField.toPoly gcd24_b4Val +
        BinaryField.toPoly gcd24_r4Val := by
  exact verify_div_step (a := gcd24_a4Val) (q := gcd24_q4Val)
    (b := gcd24_b4Val) (r := gcd24_r4Val) (by rfl)

lemma gcd24_step_5 :
    BinaryField.toPoly gcd24_a5Val =
      BinaryField.toPoly gcd24_q5Val * BinaryField.toPoly gcd24_b5Val +
        BinaryField.toPoly gcd24_r5Val := by
  exact verify_div_step (a := gcd24_a5Val) (q := gcd24_q5Val)
    (b := gcd24_b5Val) (r := gcd24_r5Val) (by rfl)

lemma gcd24_step_6 :
    BinaryField.toPoly gcd24_a6Val =
      BinaryField.toPoly gcd24_q6Val * BinaryField.toPoly gcd24_b6Val +
        BinaryField.toPoly gcd24_r6Val := by
  exact verify_div_step (a := gcd24_a6Val) (q := gcd24_q6Val)
    (b := gcd24_b6Val) (r := gcd24_r6Val) (by rfl)

lemma gcd24_step_7 :
    BinaryField.toPoly gcd24_a7Val =
      BinaryField.toPoly gcd24_q7Val * BinaryField.toPoly gcd24_b7Val +
        BinaryField.toPoly gcd24_r7Val := by
  exact verify_div_step (a := gcd24_a7Val) (q := gcd24_q7Val)
    (b := gcd24_b7Val) (r := gcd24_r7Val) (by rfl)

lemma gcd24_step_8 :
    BinaryField.toPoly gcd24_a8Val =
      BinaryField.toPoly gcd24_q8Val * BinaryField.toPoly gcd24_b8Val +
        BinaryField.toPoly gcd24_r8Val := by
  exact verify_div_step (a := gcd24_a8Val) (q := gcd24_q8Val)
    (b := gcd24_b8Val) (r := gcd24_r8Val) (by rfl)

lemma gcd24_step_9 :
    BinaryField.toPoly gcd24_a9Val =
      BinaryField.toPoly gcd24_q9Val * BinaryField.toPoly gcd24_b9Val +
        BinaryField.toPoly gcd24_r9Val := by
  exact verify_div_step (a := gcd24_a9Val) (q := gcd24_q9Val)
    (b := gcd24_b9Val) (r := gcd24_r9Val) (by rfl)

lemma gcd24_step_10 :
    BinaryField.toPoly gcd24_a10Val =
      BinaryField.toPoly gcd24_q10Val * BinaryField.toPoly gcd24_b10Val +
        BinaryField.toPoly gcd24_r10Val := by
  exact verify_div_step (a := gcd24_a10Val) (q := gcd24_q10Val)
    (b := gcd24_b10Val) (r := gcd24_r10Val) (by rfl)

lemma gcd24_step_11 :
    BinaryField.toPoly gcd24_a11Val =
      BinaryField.toPoly gcd24_q11Val * BinaryField.toPoly gcd24_b11Val +
        BinaryField.toPoly gcd24_r11Val := by
  exact verify_div_step (a := gcd24_a11Val) (q := gcd24_q11Val)
    (b := gcd24_b11Val) (r := gcd24_r11Val) (by rfl)

lemma gcd24_step_12 :
    BinaryField.toPoly gcd24_a12Val =
      BinaryField.toPoly gcd24_q12Val * BinaryField.toPoly gcd24_b12Val +
        BinaryField.toPoly gcd24_r12Val := by
  exact verify_div_step (a := gcd24_a12Val) (q := gcd24_q12Val)
    (b := gcd24_b12Val) (r := gcd24_r12Val) (by rfl)

lemma gcd24_step_13 :
    BinaryField.toPoly gcd24_a13Val =
      BinaryField.toPoly gcd24_q13Val * BinaryField.toPoly gcd24_b13Val +
        BinaryField.toPoly gcd24_r13Val := by
  exact verify_div_step (a := gcd24_a13Val) (q := gcd24_q13Val)
    (b := gcd24_b13Val) (r := gcd24_r13Val) (by rfl)

lemma gcd24_step_14 :
    BinaryField.toPoly gcd24_a14Val =
      BinaryField.toPoly gcd24_q14Val * BinaryField.toPoly gcd24_b14Val +
        BinaryField.toPoly gcd24_r14Val := by
  exact verify_div_step (a := gcd24_a14Val) (q := gcd24_q14Val)
    (b := gcd24_b14Val) (r := gcd24_r14Val) (by rfl)

lemma gcd24_step_15 :
    BinaryField.toPoly gcd24_a15Val =
      BinaryField.toPoly gcd24_q15Val * BinaryField.toPoly gcd24_b15Val +
        BinaryField.toPoly gcd24_r15Val := by
  exact verify_div_step (a := gcd24_a15Val) (q := gcd24_q15Val)
    (b := gcd24_b15Val) (r := gcd24_r15Val) (by rfl)

lemma gcd24_step_16 :
    BinaryField.toPoly gcd24_a16Val =
      BinaryField.toPoly gcd24_q16Val * BinaryField.toPoly gcd24_b16Val +
        BinaryField.toPoly gcd24_r16Val := by
  exact verify_div_step (a := gcd24_a16Val) (q := gcd24_q16Val)
    (b := gcd24_b16Val) (r := gcd24_r16Val) (by rfl)

lemma gcd24_step_17 :
    BinaryField.toPoly gcd24_a17Val =
      BinaryField.toPoly gcd24_q17Val * BinaryField.toPoly gcd24_b17Val +
        BinaryField.toPoly gcd24_r17Val := by
  exact verify_div_step (a := gcd24_a17Val) (q := gcd24_q17Val)
    (b := gcd24_b17Val) (r := gcd24_r17Val) (by rfl)

lemma gcd24_step_18 :
    BinaryField.toPoly gcd24_a18Val =
      BinaryField.toPoly gcd24_q18Val * BinaryField.toPoly gcd24_b18Val +
        BinaryField.toPoly gcd24_r18Val := by
  exact verify_div_step (a := gcd24_a18Val) (q := gcd24_q18Val)
    (b := gcd24_b18Val) (r := gcd24_r18Val) (by rfl)

lemma gcd24_step_19 :
    BinaryField.toPoly gcd24_a19Val =
      BinaryField.toPoly gcd24_q19Val * BinaryField.toPoly gcd24_b19Val +
        BinaryField.toPoly gcd24_r19Val := by
  exact verify_div_step (a := gcd24_a19Val) (q := gcd24_q19Val)
    (b := gcd24_b19Val) (r := gcd24_r19Val) (by rfl)

lemma gcd24_step_20 :
    BinaryField.toPoly gcd24_a20Val =
      BinaryField.toPoly gcd24_q20Val * BinaryField.toPoly gcd24_b20Val +
        BinaryField.toPoly gcd24_r20Val := by
  exact verify_div_step (a := gcd24_a20Val) (q := gcd24_q20Val)
    (b := gcd24_b20Val) (r := gcd24_r20Val) (by rfl)

lemma gcd24_step_21 :
    BinaryField.toPoly gcd24_a21Val =
      BinaryField.toPoly gcd24_q21Val * BinaryField.toPoly gcd24_b21Val +
        BinaryField.toPoly gcd24_r21Val := by
  exact verify_div_step (a := gcd24_a21Val) (q := gcd24_q21Val)
    (b := gcd24_b21Val) (r := gcd24_r21Val) (by rfl)

lemma gcd24_step_22 :
    BinaryField.toPoly gcd24_a22Val =
      BinaryField.toPoly gcd24_q22Val * BinaryField.toPoly gcd24_b22Val +
        BinaryField.toPoly gcd24_r22Val := by
  exact verify_div_step (a := gcd24_a22Val) (q := gcd24_q22Val)
    (b := gcd24_b22Val) (r := gcd24_r22Val) (by rfl)

lemma gcd24_step_23 :
    BinaryField.toPoly gcd24_a23Val =
      BinaryField.toPoly gcd24_q23Val * BinaryField.toPoly gcd24_b23Val +
        BinaryField.toPoly gcd24_r23Val := by
  exact verify_div_step (a := gcd24_a23Val) (q := gcd24_q23Val)
    (b := gcd24_b23Val) (r := gcd24_r23Val) (by rfl)

lemma gcd24_step_24 :
    BinaryField.toPoly gcd24_a24Val =
      BinaryField.toPoly gcd24_q24Val * BinaryField.toPoly gcd24_b24Val +
        BinaryField.toPoly gcd24_r24Val := by
  exact verify_div_step (a := gcd24_a24Val) (q := gcd24_q24Val)
    (b := gcd24_b24Val) (r := gcd24_r24Val) (by rfl)

lemma gcd24_step_25 :
    BinaryField.toPoly gcd24_a25Val =
      BinaryField.toPoly gcd24_q25Val * BinaryField.toPoly gcd24_b25Val +
        BinaryField.toPoly gcd24_r25Val := by
  exact verify_div_step (a := gcd24_a25Val) (q := gcd24_q25Val)
    (b := gcd24_b25Val) (r := gcd24_r25Val) (by rfl)

lemma gcd24_step_26 :
    BinaryField.toPoly gcd24_a26Val =
      BinaryField.toPoly gcd24_q26Val * BinaryField.toPoly gcd24_b26Val +
        BinaryField.toPoly gcd24_r26Val := by
  exact verify_div_step (a := gcd24_a26Val) (q := gcd24_q26Val)
    (b := gcd24_b26Val) (r := gcd24_r26Val) (by rfl)

lemma gcd24_step_27 :
    BinaryField.toPoly gcd24_a27Val =
      BinaryField.toPoly gcd24_q27Val * BinaryField.toPoly gcd24_b27Val +
        BinaryField.toPoly gcd24_r27Val := by
  exact verify_div_step (a := gcd24_a27Val) (q := gcd24_q27Val)
    (b := gcd24_b27Val) (r := gcd24_r27Val) (by rfl)

/-- Rabin gcd condition for exponent `24`. -/
lemma rabin_gcd_condition_24 :
    EuclideanDomain.gcd (X ^ (2 ^ 24) + X) definingPolynomial = 1 := by
  rw [gcd24_start_reduction]
  rw [definingPolynomial_eq_gcdPVal]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a1Val)
    (BinaryField.toPoly gcd24_b1Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b1Val) (by decide))
    gcd24_step_1]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a2Val)
    (BinaryField.toPoly gcd24_b2Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b2Val) (by decide))
    gcd24_step_2]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a3Val)
    (BinaryField.toPoly gcd24_b3Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b3Val) (by decide))
    gcd24_step_3]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a4Val)
    (BinaryField.toPoly gcd24_b4Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b4Val) (by decide))
    gcd24_step_4]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a5Val)
    (BinaryField.toPoly gcd24_b5Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b5Val) (by decide))
    gcd24_step_5]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a6Val)
    (BinaryField.toPoly gcd24_b6Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b6Val) (by decide))
    gcd24_step_6]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a7Val)
    (BinaryField.toPoly gcd24_b7Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b7Val) (by decide))
    gcd24_step_7]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a8Val)
    (BinaryField.toPoly gcd24_b8Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b8Val) (by decide))
    gcd24_step_8]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a9Val)
    (BinaryField.toPoly gcd24_b9Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b9Val) (by decide))
    gcd24_step_9]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a10Val)
    (BinaryField.toPoly gcd24_b10Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b10Val) (by decide))
    gcd24_step_10]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a11Val)
    (BinaryField.toPoly gcd24_b11Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b11Val) (by decide))
    gcd24_step_11]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a12Val)
    (BinaryField.toPoly gcd24_b12Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b12Val) (by decide))
    gcd24_step_12]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a13Val)
    (BinaryField.toPoly gcd24_b13Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b13Val) (by decide))
    gcd24_step_13]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a14Val)
    (BinaryField.toPoly gcd24_b14Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b14Val) (by decide))
    gcd24_step_14]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a15Val)
    (BinaryField.toPoly gcd24_b15Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b15Val) (by decide))
    gcd24_step_15]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a16Val)
    (BinaryField.toPoly gcd24_b16Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b16Val) (by decide))
    gcd24_step_16]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a17Val)
    (BinaryField.toPoly gcd24_b17Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b17Val) (by decide))
    gcd24_step_17]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a18Val)
    (BinaryField.toPoly gcd24_b18Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b18Val) (by decide))
    gcd24_step_18]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a19Val)
    (BinaryField.toPoly gcd24_b19Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b19Val) (by decide))
    gcd24_step_19]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a20Val)
    (BinaryField.toPoly gcd24_b20Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b20Val) (by decide))
    gcd24_step_20]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a21Val)
    (BinaryField.toPoly gcd24_b21Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b21Val) (by decide))
    gcd24_step_21]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a22Val)
    (BinaryField.toPoly gcd24_b22Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b22Val) (by decide))
    gcd24_step_22]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a23Val)
    (BinaryField.toPoly gcd24_b23Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b23Val) (by decide))
    gcd24_step_23]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a24Val)
    (BinaryField.toPoly gcd24_b24Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b24Val) (by decide))
    gcd24_step_24]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a25Val)
    (BinaryField.toPoly gcd24_b25Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b25Val) (by decide))
    gcd24_step_25]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a26Val)
    (BinaryField.toPoly gcd24_b26Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b26Val) (by decide))
    gcd24_step_26]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a27Val)
    (BinaryField.toPoly gcd24_b27Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b27Val) (by decide))
    gcd24_step_27]
  change EuclideanDomain.gcd
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 1 : B96))
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 0 : B96)) = 1
  rw [BinaryField.toPoly_one_eq_one
    (w := 2 * extensionDegree) (h_w_pos := by unfold extensionDegree; omega)]
  rw [BinaryField.toPoly_zero_eq_zero]
  exact BinaryField.gcd_one_zero

/-- Initial Rabin gcd remainder for exponent `16`. -/
def gcd16_b1Val : B96 := BitVec.ofNat (2 * extensionDegree) 197658536369218

lemma gcd16_b1Val_eq_zeroExtend :
    gcd16_b1Val = BitVec.zeroExtend (2 * extensionDegree) (r16Val ^^^ r0Val) := by
  decide

def gcd16_a1Val : B96 := gcdPVal
def gcd16_q1Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r1Val : B96 := BitVec.ofNat (2 * extensionDegree) 113842096028181

def gcd16_a2Val : B96 := gcd16_b1Val
def gcd16_b2Val : B96 := gcd16_r1Val
def gcd16_q2Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r2Val : B96 := BitVec.ofNat (2 * extensionDegree) 30093762761341

def gcd16_a3Val : B96 := gcd16_b2Val
def gcd16_b3Val : B96 := gcd16_r2Val
def gcd16_q3Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd16_r3Val : B96 := BitVec.ofNat (2 * extensionDegree) 12038484653025

def gcd16_a4Val : B96 := gcd16_b3Val
def gcd16_b4Val : B96 := gcd16_r3Val
def gcd16_q4Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r4Val : B96 := BitVec.ofNat (2 * extensionDegree) 4715716806238

def gcd16_a5Val : B96 := gcd16_b4Val
def gcd16_b5Val : B96 := gcd16_r4Val
def gcd16_q5Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r5Val : B96 := BitVec.ofNat (2 * extensionDegree) 2615649369949

def gcd16_a6Val : B96 := gcd16_b5Val
def gcd16_b6Val : B96 := gcd16_r5Val
def gcd16_q6Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r6Val : B96 := BitVec.ofNat (2 * extensionDegree) 601145735396

def gcd16_a7Val : B96 := gcd16_b6Val
def gcd16_b7Val : B96 := gcd16_r6Val
def gcd16_q7Val : B96 := BitVec.ofNat (2 * extensionDegree) 4
def gcd16_r7Val : B96 := BitVec.ofNat (2 * extensionDegree) 338708274381

def gcd16_a8Val : B96 := gcd16_b7Val
def gcd16_b8Val : B96 := gcd16_r7Val
def gcd16_q8Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r8Val : B96 := BitVec.ofNat (2 * extensionDegree) 95802081662

def gcd16_a9Val : B96 := gcd16_b8Val
def gcd16_b9Val : B96 := gcd16_r8Val
def gcd16_q9Val : B96 := BitVec.ofNat (2 * extensionDegree) 5
def gcd16_r9Val : B96 := BitVec.ofNat (2 * extensionDegree) 7152785483

def gcd16_a10Val : B96 := gcd16_b9Val
def gcd16_b10Val : B96 := gcd16_r9Val
def gcd16_q10Val : B96 := BitVec.ofNat (2 * extensionDegree) 25
def gcd16_r10Val : B96 := BitVec.ofNat (2 * extensionDegree) 330457053

def gcd16_a11Val : B96 := gcd16_b10Val
def gcd16_b11Val : B96 := gcd16_r10Val
def gcd16_q11Val : B96 := BitVec.ofNat (2 * extensionDegree) 24
def gcd16_r11Val : B96 := BitVec.ofNat (2 * extensionDegree) 216128371

def gcd16_a12Val : B96 := gcd16_b11Val
def gcd16_b12Val : B96 := gcd16_r11Val
def gcd16_q12Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r12Val : B96 := BitVec.ofNat (2 * extensionDegree) 110113352

def gcd16_a13Val : B96 := gcd16_b12Val
def gcd16_b13Val : B96 := gcd16_r12Val
def gcd16_q13Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r13Val : B96 := BitVec.ofNat (2 * extensionDegree) 29474787

def gcd16_a14Val : B96 := gcd16_b13Val
def gcd16_b14Val : B96 := gcd16_r13Val
def gcd16_q14Val : B96 := BitVec.ofNat (2 * extensionDegree) 5
def gcd16_r14Val : B96 := BitVec.ofNat (2 * extensionDegree) 5730855

def gcd16_a15Val : B96 := gcd16_b14Val
def gcd16_b15Val : B96 := gcd16_r14Val
def gcd16_q15Val : B96 := BitVec.ofNat (2 * extensionDegree) 6
def gcd16_r15Val : B96 := BitVec.ofNat (2 * extensionDegree) 3314481

def gcd16_a16Val : B96 := gcd16_b15Val
def gcd16_b16Val : B96 := gcd16_r15Val
def gcd16_q16Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r16Val : B96 := BitVec.ofNat (2 * extensionDegree) 51060

def gcd16_a17Val : B96 := gcd16_b16Val
def gcd16_b17Val : B96 := gcd16_r16Val
def gcd16_q17Val : B96 := BitVec.ofNat (2 * extensionDegree) 68
def gcd16_r17Val : B96 := BitVec.ofNat (2 * extensionDegree) 21473

def gcd16_a18Val : B96 := gcd16_b17Val
def gcd16_b18Val : B96 := gcd16_r17Val
def gcd16_q18Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r18Val : B96 := BitVec.ofNat (2 * extensionDegree) 13143

def gcd16_a19Val : B96 := gcd16_b18Val
def gcd16_b19Val : B96 := gcd16_r18Val
def gcd16_q19Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r19Val : B96 := BitVec.ofNat (2 * extensionDegree) 1560

def gcd16_a20Val : B96 := gcd16_b19Val
def gcd16_b20Val : B96 := gcd16_r19Val
def gcd16_q20Val : B96 := BitVec.ofNat (2 * extensionDegree) 8
def gcd16_r20Val : B96 := BitVec.ofNat (2 * extensionDegree) 919

def gcd16_a21Val : B96 := gcd16_b20Val
def gcd16_b21Val : B96 := gcd16_r20Val
def gcd16_q21Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r21Val : B96 := BitVec.ofNat (2 * extensionDegree) 310

def gcd16_a22Val : B96 := gcd16_b21Val
def gcd16_b22Val : B96 := gcd16_r21Val
def gcd16_q22Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r22Val : B96 := BitVec.ofNat (2 * extensionDegree) 205

def gcd16_a23Val : B96 := gcd16_b22Val
def gcd16_b23Val : B96 := gcd16_r22Val
def gcd16_q23Val : B96 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r23Val : B96 := BitVec.ofNat (2 * extensionDegree) 97

def gcd16_a24Val : B96 := gcd16_b23Val
def gcd16_b24Val : B96 := gcd16_r23Val
def gcd16_q24Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r24Val : B96 := BitVec.ofNat (2 * extensionDegree) 15

def gcd16_a25Val : B96 := gcd16_b24Val
def gcd16_b25Val : B96 := gcd16_r24Val
def gcd16_q25Val : B96 := BitVec.ofNat (2 * extensionDegree) 10
def gcd16_r25Val : B96 := BitVec.ofNat (2 * extensionDegree) 7

def gcd16_a26Val : B96 := gcd16_b25Val
def gcd16_b26Val : B96 := gcd16_r25Val
def gcd16_q26Val : B96 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r26Val : B96 := BitVec.ofNat (2 * extensionDegree) 1

def gcd16_a27Val : B96 := gcd16_b26Val
def gcd16_b27Val : B96 := gcd16_r26Val
def gcd16_q27Val : B96 := BitVec.ofNat (2 * extensionDegree) 7
def gcd16_r27Val : B96 := BitVec.ofNat (2 * extensionDegree) 0

/-- Reduce the exponent `16` Rabin gcd to the generated Euclidean trace. -/
lemma gcd16_start_reduction :
    EuclideanDomain.gcd (X ^ (2 ^ 16) + X) definingPolynomial =
      EuclideanDomain.gcd definingPolynomial (BinaryField.toPoly gcd16_b1Val) := by
  rw [ZMod2Poly.euclidean_gcd_comm]
  rw [EuclideanDomain.gcd_val]
  conv_lhs =>
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := definingPolynomial_ne_zero)]
    rw [X_pow_2_pow_16_mod_eq]
    rw [r16]
    rw [toPoly_mod_definingPolynomial_eq_self r16Val, X_mod_definingPolynomial]
    rw [← r0_eq_X]
    rw [r0]
    rw [← BinaryField.toPoly_xor]
    rw [toPoly_mod_definingPolynomial_eq_self (r16Val ^^^ r0Val)]
    rw [← BinaryField.Extension.toPoly_zeroExtend
      (show extensionDegree ≤ 2 * extensionDegree by unfold extensionDegree; norm_num)
      (r16Val ^^^ r0Val)]
    rw [← gcd16_b1Val_eq_zeroExtend]
    rw [ZMod2Poly.euclidean_gcd_comm]

lemma gcd16_step_1 :
    BinaryField.toPoly gcd16_a1Val =
      BinaryField.toPoly gcd16_q1Val * BinaryField.toPoly gcd16_b1Val +
        BinaryField.toPoly gcd16_r1Val := by
  exact verify_div_step (a := gcd16_a1Val) (q := gcd16_q1Val)
    (b := gcd16_b1Val) (r := gcd16_r1Val) (by rfl)

lemma gcd16_step_2 :
    BinaryField.toPoly gcd16_a2Val =
      BinaryField.toPoly gcd16_q2Val * BinaryField.toPoly gcd16_b2Val +
        BinaryField.toPoly gcd16_r2Val := by
  exact verify_div_step (a := gcd16_a2Val) (q := gcd16_q2Val)
    (b := gcd16_b2Val) (r := gcd16_r2Val) (by rfl)

lemma gcd16_step_3 :
    BinaryField.toPoly gcd16_a3Val =
      BinaryField.toPoly gcd16_q3Val * BinaryField.toPoly gcd16_b3Val +
        BinaryField.toPoly gcd16_r3Val := by
  exact verify_div_step (a := gcd16_a3Val) (q := gcd16_q3Val)
    (b := gcd16_b3Val) (r := gcd16_r3Val) (by rfl)

lemma gcd16_step_4 :
    BinaryField.toPoly gcd16_a4Val =
      BinaryField.toPoly gcd16_q4Val * BinaryField.toPoly gcd16_b4Val +
        BinaryField.toPoly gcd16_r4Val := by
  exact verify_div_step (a := gcd16_a4Val) (q := gcd16_q4Val)
    (b := gcd16_b4Val) (r := gcd16_r4Val) (by rfl)

lemma gcd16_step_5 :
    BinaryField.toPoly gcd16_a5Val =
      BinaryField.toPoly gcd16_q5Val * BinaryField.toPoly gcd16_b5Val +
        BinaryField.toPoly gcd16_r5Val := by
  exact verify_div_step (a := gcd16_a5Val) (q := gcd16_q5Val)
    (b := gcd16_b5Val) (r := gcd16_r5Val) (by rfl)

lemma gcd16_step_6 :
    BinaryField.toPoly gcd16_a6Val =
      BinaryField.toPoly gcd16_q6Val * BinaryField.toPoly gcd16_b6Val +
        BinaryField.toPoly gcd16_r6Val := by
  exact verify_div_step (a := gcd16_a6Val) (q := gcd16_q6Val)
    (b := gcd16_b6Val) (r := gcd16_r6Val) (by rfl)

lemma gcd16_step_7 :
    BinaryField.toPoly gcd16_a7Val =
      BinaryField.toPoly gcd16_q7Val * BinaryField.toPoly gcd16_b7Val +
        BinaryField.toPoly gcd16_r7Val := by
  exact verify_div_step (a := gcd16_a7Val) (q := gcd16_q7Val)
    (b := gcd16_b7Val) (r := gcd16_r7Val) (by rfl)

lemma gcd16_step_8 :
    BinaryField.toPoly gcd16_a8Val =
      BinaryField.toPoly gcd16_q8Val * BinaryField.toPoly gcd16_b8Val +
        BinaryField.toPoly gcd16_r8Val := by
  exact verify_div_step (a := gcd16_a8Val) (q := gcd16_q8Val)
    (b := gcd16_b8Val) (r := gcd16_r8Val) (by rfl)

lemma gcd16_step_9 :
    BinaryField.toPoly gcd16_a9Val =
      BinaryField.toPoly gcd16_q9Val * BinaryField.toPoly gcd16_b9Val +
        BinaryField.toPoly gcd16_r9Val := by
  exact verify_div_step (a := gcd16_a9Val) (q := gcd16_q9Val)
    (b := gcd16_b9Val) (r := gcd16_r9Val) (by rfl)

lemma gcd16_step_10 :
    BinaryField.toPoly gcd16_a10Val =
      BinaryField.toPoly gcd16_q10Val * BinaryField.toPoly gcd16_b10Val +
        BinaryField.toPoly gcd16_r10Val := by
  exact verify_div_step (a := gcd16_a10Val) (q := gcd16_q10Val)
    (b := gcd16_b10Val) (r := gcd16_r10Val) (by rfl)

lemma gcd16_step_11 :
    BinaryField.toPoly gcd16_a11Val =
      BinaryField.toPoly gcd16_q11Val * BinaryField.toPoly gcd16_b11Val +
        BinaryField.toPoly gcd16_r11Val := by
  exact verify_div_step (a := gcd16_a11Val) (q := gcd16_q11Val)
    (b := gcd16_b11Val) (r := gcd16_r11Val) (by rfl)

lemma gcd16_step_12 :
    BinaryField.toPoly gcd16_a12Val =
      BinaryField.toPoly gcd16_q12Val * BinaryField.toPoly gcd16_b12Val +
        BinaryField.toPoly gcd16_r12Val := by
  exact verify_div_step (a := gcd16_a12Val) (q := gcd16_q12Val)
    (b := gcd16_b12Val) (r := gcd16_r12Val) (by rfl)

lemma gcd16_step_13 :
    BinaryField.toPoly gcd16_a13Val =
      BinaryField.toPoly gcd16_q13Val * BinaryField.toPoly gcd16_b13Val +
        BinaryField.toPoly gcd16_r13Val := by
  exact verify_div_step (a := gcd16_a13Val) (q := gcd16_q13Val)
    (b := gcd16_b13Val) (r := gcd16_r13Val) (by rfl)

lemma gcd16_step_14 :
    BinaryField.toPoly gcd16_a14Val =
      BinaryField.toPoly gcd16_q14Val * BinaryField.toPoly gcd16_b14Val +
        BinaryField.toPoly gcd16_r14Val := by
  exact verify_div_step (a := gcd16_a14Val) (q := gcd16_q14Val)
    (b := gcd16_b14Val) (r := gcd16_r14Val) (by rfl)

lemma gcd16_step_15 :
    BinaryField.toPoly gcd16_a15Val =
      BinaryField.toPoly gcd16_q15Val * BinaryField.toPoly gcd16_b15Val +
        BinaryField.toPoly gcd16_r15Val := by
  exact verify_div_step (a := gcd16_a15Val) (q := gcd16_q15Val)
    (b := gcd16_b15Val) (r := gcd16_r15Val) (by rfl)

lemma gcd16_step_16 :
    BinaryField.toPoly gcd16_a16Val =
      BinaryField.toPoly gcd16_q16Val * BinaryField.toPoly gcd16_b16Val +
        BinaryField.toPoly gcd16_r16Val := by
  exact verify_div_step (a := gcd16_a16Val) (q := gcd16_q16Val)
    (b := gcd16_b16Val) (r := gcd16_r16Val) (by rfl)

lemma gcd16_step_17 :
    BinaryField.toPoly gcd16_a17Val =
      BinaryField.toPoly gcd16_q17Val * BinaryField.toPoly gcd16_b17Val +
        BinaryField.toPoly gcd16_r17Val := by
  exact verify_div_step (a := gcd16_a17Val) (q := gcd16_q17Val)
    (b := gcd16_b17Val) (r := gcd16_r17Val) (by rfl)

lemma gcd16_step_18 :
    BinaryField.toPoly gcd16_a18Val =
      BinaryField.toPoly gcd16_q18Val * BinaryField.toPoly gcd16_b18Val +
        BinaryField.toPoly gcd16_r18Val := by
  exact verify_div_step (a := gcd16_a18Val) (q := gcd16_q18Val)
    (b := gcd16_b18Val) (r := gcd16_r18Val) (by rfl)

lemma gcd16_step_19 :
    BinaryField.toPoly gcd16_a19Val =
      BinaryField.toPoly gcd16_q19Val * BinaryField.toPoly gcd16_b19Val +
        BinaryField.toPoly gcd16_r19Val := by
  exact verify_div_step (a := gcd16_a19Val) (q := gcd16_q19Val)
    (b := gcd16_b19Val) (r := gcd16_r19Val) (by rfl)

lemma gcd16_step_20 :
    BinaryField.toPoly gcd16_a20Val =
      BinaryField.toPoly gcd16_q20Val * BinaryField.toPoly gcd16_b20Val +
        BinaryField.toPoly gcd16_r20Val := by
  exact verify_div_step (a := gcd16_a20Val) (q := gcd16_q20Val)
    (b := gcd16_b20Val) (r := gcd16_r20Val) (by rfl)

lemma gcd16_step_21 :
    BinaryField.toPoly gcd16_a21Val =
      BinaryField.toPoly gcd16_q21Val * BinaryField.toPoly gcd16_b21Val +
        BinaryField.toPoly gcd16_r21Val := by
  exact verify_div_step (a := gcd16_a21Val) (q := gcd16_q21Val)
    (b := gcd16_b21Val) (r := gcd16_r21Val) (by rfl)

lemma gcd16_step_22 :
    BinaryField.toPoly gcd16_a22Val =
      BinaryField.toPoly gcd16_q22Val * BinaryField.toPoly gcd16_b22Val +
        BinaryField.toPoly gcd16_r22Val := by
  exact verify_div_step (a := gcd16_a22Val) (q := gcd16_q22Val)
    (b := gcd16_b22Val) (r := gcd16_r22Val) (by rfl)

lemma gcd16_step_23 :
    BinaryField.toPoly gcd16_a23Val =
      BinaryField.toPoly gcd16_q23Val * BinaryField.toPoly gcd16_b23Val +
        BinaryField.toPoly gcd16_r23Val := by
  exact verify_div_step (a := gcd16_a23Val) (q := gcd16_q23Val)
    (b := gcd16_b23Val) (r := gcd16_r23Val) (by rfl)

lemma gcd16_step_24 :
    BinaryField.toPoly gcd16_a24Val =
      BinaryField.toPoly gcd16_q24Val * BinaryField.toPoly gcd16_b24Val +
        BinaryField.toPoly gcd16_r24Val := by
  exact verify_div_step (a := gcd16_a24Val) (q := gcd16_q24Val)
    (b := gcd16_b24Val) (r := gcd16_r24Val) (by rfl)

lemma gcd16_step_25 :
    BinaryField.toPoly gcd16_a25Val =
      BinaryField.toPoly gcd16_q25Val * BinaryField.toPoly gcd16_b25Val +
        BinaryField.toPoly gcd16_r25Val := by
  exact verify_div_step (a := gcd16_a25Val) (q := gcd16_q25Val)
    (b := gcd16_b25Val) (r := gcd16_r25Val) (by rfl)

lemma gcd16_step_26 :
    BinaryField.toPoly gcd16_a26Val =
      BinaryField.toPoly gcd16_q26Val * BinaryField.toPoly gcd16_b26Val +
        BinaryField.toPoly gcd16_r26Val := by
  exact verify_div_step (a := gcd16_a26Val) (q := gcd16_q26Val)
    (b := gcd16_b26Val) (r := gcd16_r26Val) (by rfl)

lemma gcd16_step_27 :
    BinaryField.toPoly gcd16_a27Val =
      BinaryField.toPoly gcd16_q27Val * BinaryField.toPoly gcd16_b27Val +
        BinaryField.toPoly gcd16_r27Val := by
  exact verify_div_step (a := gcd16_a27Val) (q := gcd16_q27Val)
    (b := gcd16_b27Val) (r := gcd16_r27Val) (by rfl)

/-- Rabin gcd condition for exponent `16`. -/
lemma rabin_gcd_condition_16 :
    EuclideanDomain.gcd (X ^ (2 ^ 16) + X) definingPolynomial = 1 := by
  rw [gcd16_start_reduction]
  rw [definingPolynomial_eq_gcdPVal]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a1Val)
    (BinaryField.toPoly gcd16_b1Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b1Val) (by decide))
    gcd16_step_1]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a2Val)
    (BinaryField.toPoly gcd16_b2Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b2Val) (by decide))
    gcd16_step_2]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a3Val)
    (BinaryField.toPoly gcd16_b3Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b3Val) (by decide))
    gcd16_step_3]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a4Val)
    (BinaryField.toPoly gcd16_b4Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b4Val) (by decide))
    gcd16_step_4]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a5Val)
    (BinaryField.toPoly gcd16_b5Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b5Val) (by decide))
    gcd16_step_5]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a6Val)
    (BinaryField.toPoly gcd16_b6Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b6Val) (by decide))
    gcd16_step_6]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a7Val)
    (BinaryField.toPoly gcd16_b7Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b7Val) (by decide))
    gcd16_step_7]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a8Val)
    (BinaryField.toPoly gcd16_b8Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b8Val) (by decide))
    gcd16_step_8]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a9Val)
    (BinaryField.toPoly gcd16_b9Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b9Val) (by decide))
    gcd16_step_9]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a10Val)
    (BinaryField.toPoly gcd16_b10Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b10Val) (by decide))
    gcd16_step_10]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a11Val)
    (BinaryField.toPoly gcd16_b11Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b11Val) (by decide))
    gcd16_step_11]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a12Val)
    (BinaryField.toPoly gcd16_b12Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b12Val) (by decide))
    gcd16_step_12]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a13Val)
    (BinaryField.toPoly gcd16_b13Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b13Val) (by decide))
    gcd16_step_13]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a14Val)
    (BinaryField.toPoly gcd16_b14Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b14Val) (by decide))
    gcd16_step_14]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a15Val)
    (BinaryField.toPoly gcd16_b15Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b15Val) (by decide))
    gcd16_step_15]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a16Val)
    (BinaryField.toPoly gcd16_b16Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b16Val) (by decide))
    gcd16_step_16]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a17Val)
    (BinaryField.toPoly gcd16_b17Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b17Val) (by decide))
    gcd16_step_17]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a18Val)
    (BinaryField.toPoly gcd16_b18Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b18Val) (by decide))
    gcd16_step_18]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a19Val)
    (BinaryField.toPoly gcd16_b19Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b19Val) (by decide))
    gcd16_step_19]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a20Val)
    (BinaryField.toPoly gcd16_b20Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b20Val) (by decide))
    gcd16_step_20]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a21Val)
    (BinaryField.toPoly gcd16_b21Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b21Val) (by decide))
    gcd16_step_21]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a22Val)
    (BinaryField.toPoly gcd16_b22Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b22Val) (by decide))
    gcd16_step_22]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a23Val)
    (BinaryField.toPoly gcd16_b23Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b23Val) (by decide))
    gcd16_step_23]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a24Val)
    (BinaryField.toPoly gcd16_b24Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b24Val) (by decide))
    gcd16_step_24]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a25Val)
    (BinaryField.toPoly gcd16_b25Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b25Val) (by decide))
    gcd16_step_25]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a26Val)
    (BinaryField.toPoly gcd16_b26Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b26Val) (by decide))
    gcd16_step_26]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd16_a27Val)
    (BinaryField.toPoly gcd16_b27Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd16_b27Val) (by decide))
    gcd16_step_27]
  change EuclideanDomain.gcd
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 1 : B96))
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 0 : B96)) = 1
  rw [BinaryField.toPoly_one_eq_one
    (w := 2 * extensionDegree) (h_w_pos := by unfold extensionDegree; omega)]
  rw [BinaryField.toPoly_zero_eq_zero]
  exact BinaryField.gcd_one_zero

end GF2_48
