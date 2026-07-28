/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_72.XPowTwoPowModCertificate

/-!
# GF(2^72) Rabin GCD Certificate

Kernel-safe Euclidean-division certificates for the two Rabin gcd checks of
`X^72 + X^6 + X^4 + X^3 + X^2 + X + 1`.
-/

namespace GF2_72

open Polynomial

set_option maxRecDepth 2200

private abbrev B144 : Type := BitVec (2 * extensionDegree)

def gcdPVal : B144 := BitVec.ofNat (2 * extensionDegree) 4722366482869645213791

/-- Numeric 144-bit encoding of the GF72 defining polynomial. -/
lemma definingPolynomial_eq_gcdPVal :
    definingPolynomial = BinaryField.toPoly gcdPVal := by
  rw [definingPolynomial_eq_P_val]
  have h : P_val = gcdPVal := by
    decide
  rw [h]

/-- Any GF72-width polynomial is already reduced modulo the defining polynomial. -/
lemma toPoly_mod_definingPolynomial_eq_self (v : B72) :
    BinaryField.toPoly v % definingPolynomial = BinaryField.toPoly v := by
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact definingPolynomial_ne_zero)]
  rw [definingPolynomial_degree]
  exact BinaryField.toPoly_degree_lt_w
    (w := extensionDegree) (h_w_pos := by unfold extensionDegree; omega) v

/-- Soundness wrapper specialized to 144-bit Euclidean-division certificates. -/
private theorem verify_div_step {a q b r : B144}
    (h : BinaryField.Extension.checkDivStep (2 * extensionDegree) a q b r = true) :
    BinaryField.toPoly a = BinaryField.toPoly q * BinaryField.toPoly b +
      BinaryField.toPoly r := by
  exact BinaryField.Extension.checkDivStep_correct a q b r h

private theorem toPoly_ne_zero {v : B144} (h : v ≠ 0) :
    BinaryField.toPoly v ≠ 0 :=
  (BinaryField.toPoly_ne_zero_iff_ne_zero v).mpr h

/-- Initial Rabin gcd remainder for exponent `36`. -/
def gcd36_b1Val : B144 := BitVec.ofNat (2 * extensionDegree) 3130559789706947830732

lemma gcd36_b1Val_eq_zeroExtend :
    gcd36_b1Val = BitVec.zeroExtend (2 * extensionDegree) (r36Val ^^^ r0Val) := by
  decide

def gcd36_a1Val : B144 := gcdPVal
def gcd36_q1Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r1Val : B144 := BitVec.ofNat (2 * extensionDegree) 1538753096544250447815

def gcd36_a2Val : B144 := gcd36_b1Val
def gcd36_b2Val : B144 := gcd36_r1Val
def gcd36_q2Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r2Val : B144 := BitVec.ofNat (2 * extensionDegree) 283746144541738871874

def gcd36_a3Val : B144 := gcd36_b2Val
def gcd36_b3Val : B144 := gcd36_r2Val
def gcd36_q3Val : B144 := BitVec.ofNat (2 * extensionDegree) 15
def gcd36_r3Val : B144 := BitVec.ofNat (2 * extensionDegree) 78472190197577408537

def gcd36_a4Val : B144 := gcd36_b3Val
def gcd36_b4Val : B144 := gcd36_r3Val
def gcd36_q4Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r4Val : B144 := BitVec.ofNat (2 * extensionDegree) 67070847363661368425

def gcd36_a5Val : B144 := gcd36_b4Val
def gcd36_b5Val : B144 := gcd36_r4Val
def gcd36_q5Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r5Val : B144 := BitVec.ofNat (2 * extensionDegree) 11986811782157104290

def gcd36_a6Val : B144 := gcd36_b5Val
def gcd36_b6Val : B144 := gcd36_r5Val
def gcd36_q6Val : B144 := BitVec.ofNat (2 * extensionDegree) 6
def gcd36_r6Val : B144 := BitVec.ofNat (2 * extensionDegree) 8583360565896361893

def gcd36_a7Val : B144 := gcd36_b6Val
def gcd36_b7Val : B144 := gcd36_r6Val
def gcd36_q7Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r7Val : B144 := BitVec.ofNat (2 * extensionDegree) 4574527822564666445

def gcd36_a8Val : B144 := gcd36_b7Val
def gcd36_b8Val : B144 := gcd36_r7Val
def gcd36_q8Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r8Val : B144 := BitVec.ofNat (2 * extensionDegree) 714314599271132991

def gcd36_a9Val : B144 := gcd36_b8Val
def gcd36_b9Val : B144 := gcd36_r8Val
def gcd36_q9Val : B144 := BitVec.ofNat (2 * extensionDegree) 7
def gcd36_r9Val : B144 := BitVec.ofNat (2 * extensionDegree) 209059452027970032

def gcd36_a10Val : B144 := gcd36_b9Val
def gcd36_b10Val : B144 := gcd36_r9Val
def gcd36_q10Val : B144 := BitVec.ofNat (2 * extensionDegree) 5
def gcd36_r10Val : B144 := BitVec.ofNat (2 * extensionDegree) 42101374778624271

def gcd36_a11Val : B144 := gcd36_b10Val
def gcd36_b11Val : B144 := gcd36_r10Val
def gcd36_q11Val : B144 := BitVec.ofNat (2 * extensionDegree) 5
def gcd36_r11Val : B144 := BitVec.ofNat (2 * extensionDegree) 10523856223456451

def gcd36_a12Val : B144 := gcd36_b11Val
def gcd36_b12Val : B144 := gcd36_r11Val
def gcd36_q12Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd36_r12Val : B144 := BitVec.ofNat (2 * extensionDegree) 34544141695491

def gcd36_a13Val : B144 := gcd36_b12Val
def gcd36_b13Val : B144 := gcd36_r12Val
def gcd36_q13Val : B144 := BitVec.ofNat (2 * extensionDegree) 873
def gcd36_r13Val : B144 := BitVec.ofNat (2 * extensionDegree) 17103716524920

def gcd36_a14Val : B144 := gcd36_b13Val
def gcd36_b14Val : B144 := gcd36_r13Val
def gcd36_q14Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r14Val : B144 := BitVec.ofNat (2 * extensionDegree) 508528835827

def gcd36_a15Val : B144 := gcd36_b14Val
def gcd36_b15Val : B144 := gcd36_r14Val
def gcd36_q15Val : B144 := BitVec.ofNat (2 * extensionDegree) 39
def gcd36_r15Val : B144 := BitVec.ofNat (2 * extensionDegree) 6987680705

def gcd36_a16Val : B144 := gcd36_b15Val
def gcd36_b16Val : B144 := gcd36_r15Val
def gcd36_q16Val : B144 := BitVec.ofNat (2 * extensionDegree) 87
def gcd36_r16Val : B144 := BitVec.ofNat (2 * extensionDegree) 533382116

def gcd36_a17Val : B144 := gcd36_b16Val
def gcd36_b17Val : B144 := gcd36_r16Val
def gcd36_q17Val : B144 := BitVec.ofNat (2 * extensionDegree) 23
def gcd36_r17Val : B144 := BitVec.ofNat (2 * extensionDegree) 61341245

def gcd36_a18Val : B144 := gcd36_b17Val
def gcd36_b18Val : B144 := gcd36_r17Val
def gcd36_q18Val : B144 := BitVec.ofNat (2 * extensionDegree) 9
def gcd36_r18Val : B144 := BitVec.ofNat (2 * extensionDegree) 22203441

def gcd36_a19Val : B144 := gcd36_b18Val
def gcd36_b19Val : B144 := gcd36_r18Val
def gcd36_q19Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r19Val : B144 := BitVec.ofNat (2 * extensionDegree) 5286510

def gcd36_a20Val : B144 := gcd36_b19Val
def gcd36_b20Val : B144 := gcd36_r19Val
def gcd36_q20Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd36_r20Val : B144 := BitVec.ofNat (2 * extensionDegree) 1074569

def gcd36_a21Val : B144 := gcd36_b20Val
def gcd36_b21Val : B144 := gcd36_r20Val
def gcd36_q21Val : B144 := BitVec.ofNat (2 * extensionDegree) 5
def gcd36_r21Val : B144 := BitVec.ofNat (2 * extensionDegree) 88515

def gcd36_a22Val : B144 := gcd36_b21Val
def gcd36_b22Val : B144 := gcd36_r21Val
def gcd36_q22Val : B144 := BitVec.ofNat (2 * extensionDegree) 20
def gcd36_r22Val : B144 := BitVec.ofNat (2 * extensionDegree) 40629

def gcd36_a23Val : B144 := gcd36_b22Val
def gcd36_b23Val : B144 := gcd36_r22Val
def gcd36_q23Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r23Val : B144 := BitVec.ofNat (2 * extensionDegree) 25769

def gcd36_a24Val : B144 := gcd36_b23Val
def gcd36_b24Val : B144 := gcd36_r23Val
def gcd36_q24Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r24Val : B144 := BitVec.ofNat (2 * extensionDegree) 13134

def gcd36_a25Val : B144 := gcd36_b24Val
def gcd36_b25Val : B144 := gcd36_r24Val
def gcd36_q25Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r25Val : B144 := BitVec.ofNat (2 * extensionDegree) 565

def gcd36_a26Val : B144 := gcd36_b25Val
def gcd36_b26Val : B144 := gcd36_r25Val
def gcd36_q26Val : B144 := BitVec.ofNat (2 * extensionDegree) 24
def gcd36_r26Val : B144 := BitVec.ofNat (2 * extensionDegree) 438

def gcd36_a27Val : B144 := gcd36_b26Val
def gcd36_b27Val : B144 := gcd36_r26Val
def gcd36_q27Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r27Val : B144 := BitVec.ofNat (2 * extensionDegree) 239

def gcd36_a28Val : B144 := gcd36_b27Val
def gcd36_b28Val : B144 := gcd36_r27Val
def gcd36_q28Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r28Val : B144 := BitVec.ofNat (2 * extensionDegree) 104

def gcd36_a29Val : B144 := gcd36_b28Val
def gcd36_b29Val : B144 := gcd36_r28Val
def gcd36_q29Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r29Val : B144 := BitVec.ofNat (2 * extensionDegree) 63

def gcd36_a30Val : B144 := gcd36_b29Val
def gcd36_b30Val : B144 := gcd36_r29Val
def gcd36_q30Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r30Val : B144 := BitVec.ofNat (2 * extensionDegree) 22

def gcd36_a31Val : B144 := gcd36_b30Val
def gcd36_b31Val : B144 := gcd36_r30Val
def gcd36_q31Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd36_r31Val : B144 := BitVec.ofNat (2 * extensionDegree) 5

def gcd36_a32Val : B144 := gcd36_b31Val
def gcd36_b32Val : B144 := gcd36_r31Val
def gcd36_q32Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd36_r32Val : B144 := BitVec.ofNat (2 * extensionDegree) 2

def gcd36_a33Val : B144 := gcd36_b32Val
def gcd36_b33Val : B144 := gcd36_r32Val
def gcd36_q33Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r33Val : B144 := BitVec.ofNat (2 * extensionDegree) 1

def gcd36_a34Val : B144 := gcd36_b33Val
def gcd36_b34Val : B144 := gcd36_r33Val
def gcd36_q34Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd36_r34Val : B144 := BitVec.ofNat (2 * extensionDegree) 0

/-- Reduce the exponent `36` Rabin gcd to the generated Euclidean trace. -/
lemma gcd36_start_reduction :
    EuclideanDomain.gcd (X ^ (2 ^ 36) + X) definingPolynomial =
      EuclideanDomain.gcd definingPolynomial (BinaryField.toPoly gcd36_b1Val) := by
  rw [ZMod2Poly.euclidean_gcd_comm]
  rw [EuclideanDomain.gcd_val]
  conv_lhs =>
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := definingPolynomial_ne_zero)]
    rw [X_pow_2_pow_36_mod_eq]
    rw [r36]
    rw [toPoly_mod_definingPolynomial_eq_self r36Val, X_mod_definingPolynomial]
    rw [← r0_eq_X]
    rw [r0]
    rw [← BinaryField.toPoly_xor]
    rw [toPoly_mod_definingPolynomial_eq_self (r36Val ^^^ r0Val)]
    rw [← BinaryField.Extension.toPoly_zeroExtend
      (show extensionDegree ≤ 2 * extensionDegree by unfold extensionDegree; norm_num)
      (r36Val ^^^ r0Val)]
    rw [← gcd36_b1Val_eq_zeroExtend]
    rw [ZMod2Poly.euclidean_gcd_comm]

lemma gcd36_step_1 :
    BinaryField.toPoly gcd36_a1Val =
      BinaryField.toPoly gcd36_q1Val * BinaryField.toPoly gcd36_b1Val +
        BinaryField.toPoly gcd36_r1Val := by
  exact verify_div_step (a := gcd36_a1Val) (q := gcd36_q1Val)
    (b := gcd36_b1Val) (r := gcd36_r1Val) (by rfl)

lemma gcd36_step_2 :
    BinaryField.toPoly gcd36_a2Val =
      BinaryField.toPoly gcd36_q2Val * BinaryField.toPoly gcd36_b2Val +
        BinaryField.toPoly gcd36_r2Val := by
  exact verify_div_step (a := gcd36_a2Val) (q := gcd36_q2Val)
    (b := gcd36_b2Val) (r := gcd36_r2Val) (by rfl)

lemma gcd36_step_3 :
    BinaryField.toPoly gcd36_a3Val =
      BinaryField.toPoly gcd36_q3Val * BinaryField.toPoly gcd36_b3Val +
        BinaryField.toPoly gcd36_r3Val := by
  exact verify_div_step (a := gcd36_a3Val) (q := gcd36_q3Val)
    (b := gcd36_b3Val) (r := gcd36_r3Val) (by rfl)

lemma gcd36_step_4 :
    BinaryField.toPoly gcd36_a4Val =
      BinaryField.toPoly gcd36_q4Val * BinaryField.toPoly gcd36_b4Val +
        BinaryField.toPoly gcd36_r4Val := by
  exact verify_div_step (a := gcd36_a4Val) (q := gcd36_q4Val)
    (b := gcd36_b4Val) (r := gcd36_r4Val) (by rfl)

lemma gcd36_step_5 :
    BinaryField.toPoly gcd36_a5Val =
      BinaryField.toPoly gcd36_q5Val * BinaryField.toPoly gcd36_b5Val +
        BinaryField.toPoly gcd36_r5Val := by
  exact verify_div_step (a := gcd36_a5Val) (q := gcd36_q5Val)
    (b := gcd36_b5Val) (r := gcd36_r5Val) (by rfl)

lemma gcd36_step_6 :
    BinaryField.toPoly gcd36_a6Val =
      BinaryField.toPoly gcd36_q6Val * BinaryField.toPoly gcd36_b6Val +
        BinaryField.toPoly gcd36_r6Val := by
  exact verify_div_step (a := gcd36_a6Val) (q := gcd36_q6Val)
    (b := gcd36_b6Val) (r := gcd36_r6Val) (by rfl)

lemma gcd36_step_7 :
    BinaryField.toPoly gcd36_a7Val =
      BinaryField.toPoly gcd36_q7Val * BinaryField.toPoly gcd36_b7Val +
        BinaryField.toPoly gcd36_r7Val := by
  exact verify_div_step (a := gcd36_a7Val) (q := gcd36_q7Val)
    (b := gcd36_b7Val) (r := gcd36_r7Val) (by rfl)

lemma gcd36_step_8 :
    BinaryField.toPoly gcd36_a8Val =
      BinaryField.toPoly gcd36_q8Val * BinaryField.toPoly gcd36_b8Val +
        BinaryField.toPoly gcd36_r8Val := by
  exact verify_div_step (a := gcd36_a8Val) (q := gcd36_q8Val)
    (b := gcd36_b8Val) (r := gcd36_r8Val) (by rfl)

lemma gcd36_step_9 :
    BinaryField.toPoly gcd36_a9Val =
      BinaryField.toPoly gcd36_q9Val * BinaryField.toPoly gcd36_b9Val +
        BinaryField.toPoly gcd36_r9Val := by
  exact verify_div_step (a := gcd36_a9Val) (q := gcd36_q9Val)
    (b := gcd36_b9Val) (r := gcd36_r9Val) (by rfl)

lemma gcd36_step_10 :
    BinaryField.toPoly gcd36_a10Val =
      BinaryField.toPoly gcd36_q10Val * BinaryField.toPoly gcd36_b10Val +
        BinaryField.toPoly gcd36_r10Val := by
  exact verify_div_step (a := gcd36_a10Val) (q := gcd36_q10Val)
    (b := gcd36_b10Val) (r := gcd36_r10Val) (by rfl)

lemma gcd36_step_11 :
    BinaryField.toPoly gcd36_a11Val =
      BinaryField.toPoly gcd36_q11Val * BinaryField.toPoly gcd36_b11Val +
        BinaryField.toPoly gcd36_r11Val := by
  exact verify_div_step (a := gcd36_a11Val) (q := gcd36_q11Val)
    (b := gcd36_b11Val) (r := gcd36_r11Val) (by rfl)

lemma gcd36_step_12 :
    BinaryField.toPoly gcd36_a12Val =
      BinaryField.toPoly gcd36_q12Val * BinaryField.toPoly gcd36_b12Val +
        BinaryField.toPoly gcd36_r12Val := by
  exact verify_div_step (a := gcd36_a12Val) (q := gcd36_q12Val)
    (b := gcd36_b12Val) (r := gcd36_r12Val) (by rfl)

lemma gcd36_step_13 :
    BinaryField.toPoly gcd36_a13Val =
      BinaryField.toPoly gcd36_q13Val * BinaryField.toPoly gcd36_b13Val +
        BinaryField.toPoly gcd36_r13Val := by
  exact verify_div_step (a := gcd36_a13Val) (q := gcd36_q13Val)
    (b := gcd36_b13Val) (r := gcd36_r13Val) (by rfl)

lemma gcd36_step_14 :
    BinaryField.toPoly gcd36_a14Val =
      BinaryField.toPoly gcd36_q14Val * BinaryField.toPoly gcd36_b14Val +
        BinaryField.toPoly gcd36_r14Val := by
  exact verify_div_step (a := gcd36_a14Val) (q := gcd36_q14Val)
    (b := gcd36_b14Val) (r := gcd36_r14Val) (by rfl)

lemma gcd36_step_15 :
    BinaryField.toPoly gcd36_a15Val =
      BinaryField.toPoly gcd36_q15Val * BinaryField.toPoly gcd36_b15Val +
        BinaryField.toPoly gcd36_r15Val := by
  exact verify_div_step (a := gcd36_a15Val) (q := gcd36_q15Val)
    (b := gcd36_b15Val) (r := gcd36_r15Val) (by rfl)

lemma gcd36_step_16 :
    BinaryField.toPoly gcd36_a16Val =
      BinaryField.toPoly gcd36_q16Val * BinaryField.toPoly gcd36_b16Val +
        BinaryField.toPoly gcd36_r16Val := by
  exact verify_div_step (a := gcd36_a16Val) (q := gcd36_q16Val)
    (b := gcd36_b16Val) (r := gcd36_r16Val) (by rfl)

lemma gcd36_step_17 :
    BinaryField.toPoly gcd36_a17Val =
      BinaryField.toPoly gcd36_q17Val * BinaryField.toPoly gcd36_b17Val +
        BinaryField.toPoly gcd36_r17Val := by
  exact verify_div_step (a := gcd36_a17Val) (q := gcd36_q17Val)
    (b := gcd36_b17Val) (r := gcd36_r17Val) (by rfl)

lemma gcd36_step_18 :
    BinaryField.toPoly gcd36_a18Val =
      BinaryField.toPoly gcd36_q18Val * BinaryField.toPoly gcd36_b18Val +
        BinaryField.toPoly gcd36_r18Val := by
  exact verify_div_step (a := gcd36_a18Val) (q := gcd36_q18Val)
    (b := gcd36_b18Val) (r := gcd36_r18Val) (by rfl)

lemma gcd36_step_19 :
    BinaryField.toPoly gcd36_a19Val =
      BinaryField.toPoly gcd36_q19Val * BinaryField.toPoly gcd36_b19Val +
        BinaryField.toPoly gcd36_r19Val := by
  exact verify_div_step (a := gcd36_a19Val) (q := gcd36_q19Val)
    (b := gcd36_b19Val) (r := gcd36_r19Val) (by rfl)

lemma gcd36_step_20 :
    BinaryField.toPoly gcd36_a20Val =
      BinaryField.toPoly gcd36_q20Val * BinaryField.toPoly gcd36_b20Val +
        BinaryField.toPoly gcd36_r20Val := by
  exact verify_div_step (a := gcd36_a20Val) (q := gcd36_q20Val)
    (b := gcd36_b20Val) (r := gcd36_r20Val) (by rfl)

lemma gcd36_step_21 :
    BinaryField.toPoly gcd36_a21Val =
      BinaryField.toPoly gcd36_q21Val * BinaryField.toPoly gcd36_b21Val +
        BinaryField.toPoly gcd36_r21Val := by
  exact verify_div_step (a := gcd36_a21Val) (q := gcd36_q21Val)
    (b := gcd36_b21Val) (r := gcd36_r21Val) (by rfl)

lemma gcd36_step_22 :
    BinaryField.toPoly gcd36_a22Val =
      BinaryField.toPoly gcd36_q22Val * BinaryField.toPoly gcd36_b22Val +
        BinaryField.toPoly gcd36_r22Val := by
  exact verify_div_step (a := gcd36_a22Val) (q := gcd36_q22Val)
    (b := gcd36_b22Val) (r := gcd36_r22Val) (by rfl)

lemma gcd36_step_23 :
    BinaryField.toPoly gcd36_a23Val =
      BinaryField.toPoly gcd36_q23Val * BinaryField.toPoly gcd36_b23Val +
        BinaryField.toPoly gcd36_r23Val := by
  exact verify_div_step (a := gcd36_a23Val) (q := gcd36_q23Val)
    (b := gcd36_b23Val) (r := gcd36_r23Val) (by rfl)

lemma gcd36_step_24 :
    BinaryField.toPoly gcd36_a24Val =
      BinaryField.toPoly gcd36_q24Val * BinaryField.toPoly gcd36_b24Val +
        BinaryField.toPoly gcd36_r24Val := by
  exact verify_div_step (a := gcd36_a24Val) (q := gcd36_q24Val)
    (b := gcd36_b24Val) (r := gcd36_r24Val) (by rfl)

lemma gcd36_step_25 :
    BinaryField.toPoly gcd36_a25Val =
      BinaryField.toPoly gcd36_q25Val * BinaryField.toPoly gcd36_b25Val +
        BinaryField.toPoly gcd36_r25Val := by
  exact verify_div_step (a := gcd36_a25Val) (q := gcd36_q25Val)
    (b := gcd36_b25Val) (r := gcd36_r25Val) (by rfl)

lemma gcd36_step_26 :
    BinaryField.toPoly gcd36_a26Val =
      BinaryField.toPoly gcd36_q26Val * BinaryField.toPoly gcd36_b26Val +
        BinaryField.toPoly gcd36_r26Val := by
  exact verify_div_step (a := gcd36_a26Val) (q := gcd36_q26Val)
    (b := gcd36_b26Val) (r := gcd36_r26Val) (by rfl)

lemma gcd36_step_27 :
    BinaryField.toPoly gcd36_a27Val =
      BinaryField.toPoly gcd36_q27Val * BinaryField.toPoly gcd36_b27Val +
        BinaryField.toPoly gcd36_r27Val := by
  exact verify_div_step (a := gcd36_a27Val) (q := gcd36_q27Val)
    (b := gcd36_b27Val) (r := gcd36_r27Val) (by rfl)

lemma gcd36_step_28 :
    BinaryField.toPoly gcd36_a28Val =
      BinaryField.toPoly gcd36_q28Val * BinaryField.toPoly gcd36_b28Val +
        BinaryField.toPoly gcd36_r28Val := by
  exact verify_div_step (a := gcd36_a28Val) (q := gcd36_q28Val)
    (b := gcd36_b28Val) (r := gcd36_r28Val) (by rfl)

lemma gcd36_step_29 :
    BinaryField.toPoly gcd36_a29Val =
      BinaryField.toPoly gcd36_q29Val * BinaryField.toPoly gcd36_b29Val +
        BinaryField.toPoly gcd36_r29Val := by
  exact verify_div_step (a := gcd36_a29Val) (q := gcd36_q29Val)
    (b := gcd36_b29Val) (r := gcd36_r29Val) (by rfl)

lemma gcd36_step_30 :
    BinaryField.toPoly gcd36_a30Val =
      BinaryField.toPoly gcd36_q30Val * BinaryField.toPoly gcd36_b30Val +
        BinaryField.toPoly gcd36_r30Val := by
  exact verify_div_step (a := gcd36_a30Val) (q := gcd36_q30Val)
    (b := gcd36_b30Val) (r := gcd36_r30Val) (by rfl)

lemma gcd36_step_31 :
    BinaryField.toPoly gcd36_a31Val =
      BinaryField.toPoly gcd36_q31Val * BinaryField.toPoly gcd36_b31Val +
        BinaryField.toPoly gcd36_r31Val := by
  exact verify_div_step (a := gcd36_a31Val) (q := gcd36_q31Val)
    (b := gcd36_b31Val) (r := gcd36_r31Val) (by rfl)

lemma gcd36_step_32 :
    BinaryField.toPoly gcd36_a32Val =
      BinaryField.toPoly gcd36_q32Val * BinaryField.toPoly gcd36_b32Val +
        BinaryField.toPoly gcd36_r32Val := by
  exact verify_div_step (a := gcd36_a32Val) (q := gcd36_q32Val)
    (b := gcd36_b32Val) (r := gcd36_r32Val) (by rfl)

lemma gcd36_step_33 :
    BinaryField.toPoly gcd36_a33Val =
      BinaryField.toPoly gcd36_q33Val * BinaryField.toPoly gcd36_b33Val +
        BinaryField.toPoly gcd36_r33Val := by
  exact verify_div_step (a := gcd36_a33Val) (q := gcd36_q33Val)
    (b := gcd36_b33Val) (r := gcd36_r33Val) (by rfl)

lemma gcd36_step_34 :
    BinaryField.toPoly gcd36_a34Val =
      BinaryField.toPoly gcd36_q34Val * BinaryField.toPoly gcd36_b34Val +
        BinaryField.toPoly gcd36_r34Val := by
  exact verify_div_step (a := gcd36_a34Val) (q := gcd36_q34Val)
    (b := gcd36_b34Val) (r := gcd36_r34Val) (by rfl)

/-- Rabin gcd condition for exponent `36`. -/
lemma rabin_gcd_condition_36 :
    EuclideanDomain.gcd (X ^ (2 ^ 36) + X) definingPolynomial = 1 := by
  rw [gcd36_start_reduction]
  rw [definingPolynomial_eq_gcdPVal]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a1Val)
    (BinaryField.toPoly gcd36_b1Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b1Val) (by decide))
    gcd36_step_1]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a2Val)
    (BinaryField.toPoly gcd36_b2Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b2Val) (by decide))
    gcd36_step_2]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a3Val)
    (BinaryField.toPoly gcd36_b3Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b3Val) (by decide))
    gcd36_step_3]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a4Val)
    (BinaryField.toPoly gcd36_b4Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b4Val) (by decide))
    gcd36_step_4]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a5Val)
    (BinaryField.toPoly gcd36_b5Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b5Val) (by decide))
    gcd36_step_5]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a6Val)
    (BinaryField.toPoly gcd36_b6Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b6Val) (by decide))
    gcd36_step_6]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a7Val)
    (BinaryField.toPoly gcd36_b7Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b7Val) (by decide))
    gcd36_step_7]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a8Val)
    (BinaryField.toPoly gcd36_b8Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b8Val) (by decide))
    gcd36_step_8]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a9Val)
    (BinaryField.toPoly gcd36_b9Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b9Val) (by decide))
    gcd36_step_9]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a10Val)
    (BinaryField.toPoly gcd36_b10Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b10Val) (by decide))
    gcd36_step_10]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a11Val)
    (BinaryField.toPoly gcd36_b11Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b11Val) (by decide))
    gcd36_step_11]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a12Val)
    (BinaryField.toPoly gcd36_b12Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b12Val) (by decide))
    gcd36_step_12]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a13Val)
    (BinaryField.toPoly gcd36_b13Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b13Val) (by decide))
    gcd36_step_13]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a14Val)
    (BinaryField.toPoly gcd36_b14Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b14Val) (by decide))
    gcd36_step_14]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a15Val)
    (BinaryField.toPoly gcd36_b15Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b15Val) (by decide))
    gcd36_step_15]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a16Val)
    (BinaryField.toPoly gcd36_b16Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b16Val) (by decide))
    gcd36_step_16]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a17Val)
    (BinaryField.toPoly gcd36_b17Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b17Val) (by decide))
    gcd36_step_17]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a18Val)
    (BinaryField.toPoly gcd36_b18Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b18Val) (by decide))
    gcd36_step_18]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a19Val)
    (BinaryField.toPoly gcd36_b19Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b19Val) (by decide))
    gcd36_step_19]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a20Val)
    (BinaryField.toPoly gcd36_b20Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b20Val) (by decide))
    gcd36_step_20]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a21Val)
    (BinaryField.toPoly gcd36_b21Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b21Val) (by decide))
    gcd36_step_21]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a22Val)
    (BinaryField.toPoly gcd36_b22Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b22Val) (by decide))
    gcd36_step_22]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a23Val)
    (BinaryField.toPoly gcd36_b23Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b23Val) (by decide))
    gcd36_step_23]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a24Val)
    (BinaryField.toPoly gcd36_b24Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b24Val) (by decide))
    gcd36_step_24]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a25Val)
    (BinaryField.toPoly gcd36_b25Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b25Val) (by decide))
    gcd36_step_25]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a26Val)
    (BinaryField.toPoly gcd36_b26Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b26Val) (by decide))
    gcd36_step_26]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a27Val)
    (BinaryField.toPoly gcd36_b27Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b27Val) (by decide))
    gcd36_step_27]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a28Val)
    (BinaryField.toPoly gcd36_b28Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b28Val) (by decide))
    gcd36_step_28]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a29Val)
    (BinaryField.toPoly gcd36_b29Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b29Val) (by decide))
    gcd36_step_29]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a30Val)
    (BinaryField.toPoly gcd36_b30Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b30Val) (by decide))
    gcd36_step_30]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a31Val)
    (BinaryField.toPoly gcd36_b31Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b31Val) (by decide))
    gcd36_step_31]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a32Val)
    (BinaryField.toPoly gcd36_b32Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b32Val) (by decide))
    gcd36_step_32]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a33Val)
    (BinaryField.toPoly gcd36_b33Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b33Val) (by decide))
    gcd36_step_33]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd36_a34Val)
    (BinaryField.toPoly gcd36_b34Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd36_b34Val) (by decide))
    gcd36_step_34]
  change EuclideanDomain.gcd
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 1 : B144))
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 0 : B144)) = 1
  rw [BinaryField.toPoly_one_eq_one
    (w := 2 * extensionDegree) (h_w_pos := by unfold extensionDegree; omega)]
  rw [BinaryField.toPoly_zero_eq_zero]
  exact BinaryField.gcd_one_zero

/-- Initial Rabin gcd remainder for exponent `24`. -/
def gcd24_b1Val : B144 := BitVec.ofNat (2 * extensionDegree) 3489030642769216307906

lemma gcd24_b1Val_eq_zeroExtend :
    gcd24_b1Val = BitVec.zeroExtend (2 * extensionDegree) (r24Val ^^^ r0Val) := by
  decide

def gcd24_a1Val : B144 := gcdPVal
def gcd24_q1Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r1Val : B144 := BitVec.ofNat (2 * extensionDegree) 2255694802668787402203

def gcd24_a2Val : B144 := gcd24_b1Val
def gcd24_b2Val : B144 := gcd24_r1Val
def gcd24_q2Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r2Val : B144 := BitVec.ofNat (2 * extensionDegree) 958947153640194935983

def gcd24_a3Val : B144 := gcd24_b2Val
def gcd24_b3Val : B144 := gcd24_r2Val
def gcd24_q3Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r3Val : B144 := BitVec.ofNat (2 * extensionDegree) 547650258810799266949

def gcd24_a4Val : B144 := gcd24_b3Val
def gcd24_b4Val : B144 := gcd24_r3Val
def gcd24_q4Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r4Val : B144 := BitVec.ofNat (2 * extensionDegree) 158835636821578069413

def gcd24_a5Val : B144 := gcd24_b4Val
def gcd24_b5Val : B144 := gcd24_r4Val
def gcd24_q5Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r5Val : B144 := BitVec.ofNat (2 * extensionDegree) 75297387224129651306

def gcd24_a6Val : B144 := gcd24_b5Val
def gcd24_b6Val : B144 := gcd24_r5Val
def gcd24_q6Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r6Val : B144 := BitVec.ofNat (2 * extensionDegree) 13089034321561137521

def gcd24_a7Val : B144 := gcd24_b6Val
def gcd24_b7Val : B144 := gcd24_r6Val
def gcd24_q7Val : B144 := BitVec.ofNat (2 * extensionDegree) 11
def gcd24_r7Val : B144 := BitVec.ofNat (2 * extensionDegree) 7436583959422376561

def gcd24_a8Val : B144 := gcd24_b7Val
def gcd24_b8Val : B144 := gcd24_r7Val
def gcd24_q8Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r8Val : B144 := BitVec.ofNat (2 * extensionDegree) 2087842304207036386

def gcd24_a9Val : B144 := gcd24_b8Val
def gcd24_b9Val : B144 := gcd24_r8Val
def gcd24_q9Val : B144 := BitVec.ofNat (2 * extensionDegree) 5
def gcd24_r9Val : B144 := BitVec.ofNat (2 * extensionDegree) 588716151435590171

def gcd24_a10Val : B144 := gcd24_b9Val
def gcd24_b10Val : B144 := gcd24_r9Val
def gcd24_q10Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r10Val : B144 := BitVec.ofNat (2 * extensionDegree) 325701505080725967

def gcd24_a11Val : B144 := gcd24_b10Val
def gcd24_b11Val : B144 := gcd24_r10Val
def gcd24_q11Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r11Val : B144 := BitVec.ofNat (2 * extensionDegree) 81546028633905541

def gcd24_a12Val : B144 := gcd24_b11Val
def gcd24_b12Val : B144 := gcd24_r11Val
def gcd24_q12Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r12Val : B144 := BitVec.ofNat (2 * extensionDegree) 1065917591123931

def gcd24_a13Val : B144 := gcd24_b12Val
def gcd24_b13Val : B144 := gcd24_r12Val
def gcd24_q13Val : B144 := BitVec.ofNat (2 * extensionDegree) 215
def gcd24_r13Val : B144 := BitVec.ofNat (2 * extensionDegree) 203854716794996

def gcd24_a14Val : B144 := gcd24_b13Val
def gcd24_b14Val : B144 := gcd24_r13Val
def gcd24_q14Val : B144 := BitVec.ofNat (2 * extensionDegree) 6
def gcd24_r14Val : B144 := BitVec.ofNat (2 * extensionDegree) 103504542623459

def gcd24_a15Val : B144 := gcd24_b14Val
def gcd24_b15Val : B144 := gcd24_r14Val
def gcd24_q15Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r15Val : B144 := BitVec.ofNat (2 * extensionDegree) 5641725228466

def gcd24_a16Val : B144 := gcd24_b15Val
def gcd24_b16Val : B144 := gcd24_r15Val
def gcd24_q16Val : B144 := BitVec.ofNat (2 * extensionDegree) 19
def gcd24_r16Val : B144 := BitVec.ofNat (2 * extensionDegree) 3679243789077

def gcd24_a17Val : B144 := gcd24_b16Val
def gcd24_b17Val : B144 := gcd24_r16Val
def gcd24_q17Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r17Val : B144 := BitVec.ofNat (2 * extensionDegree) 861091270797

def gcd24_a18Val : B144 := gcd24_b17Val
def gcd24_b18Val : B144 := gcd24_r17Val
def gcd24_q18Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r18Val : B144 := BitVec.ofNat (2 * extensionDegree) 521036144929

def gcd24_a19Val : B144 := gcd24_b18Val
def gcd24_b19Val : B144 := gcd24_r18Val
def gcd24_q19Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r19Val : B144 := BitVec.ofNat (2 * extensionDegree) 252821328591

def gcd24_a20Val : B144 := gcd24_b19Val
def gcd24_b20Val : B144 := gcd24_r19Val
def gcd24_q20Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r20Val : B144 := BitVec.ofNat (2 * extensionDegree) 55474521279

def gcd24_a21Val : B144 := gcd24_b20Val
def gcd24_b21Val : B144 := gcd24_r20Val
def gcd24_q21Val : B144 := BitVec.ofNat (2 * extensionDegree) 5
def gcd24_r21Val : B144 := BitVec.ofNat (2 * extensionDegree) 24124671116

def gcd24_a22Val : B144 := gcd24_b21Val
def gcd24_b22Val : B144 := gcd24_r21Val
def gcd24_q22Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r22Val : B144 := BitVec.ofNat (2 * extensionDegree) 9875081515

def gcd24_a23Val : B144 := gcd24_b22Val
def gcd24_b23Val : B144 := gcd24_r22Val
def gcd24_q23Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r23Val : B144 := BitVec.ofNat (2 * extensionDegree) 4374845146

def gcd24_a24Val : B144 := gcd24_b23Val
def gcd24_b24Val : B144 := gcd24_r23Val
def gcd24_q24Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r24Val : B144 := BitVec.ofNat (2 * extensionDegree) 1159488671

def gcd24_a25Val : B144 := gcd24_b24Val
def gcd24_b25Val : B144 := gcd24_r24Val
def gcd24_q25Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r25Val : B144 := BitVec.ofNat (2 * extensionDegree) 280183974

def gcd24_a26Val : B144 := gcd24_b25Val
def gcd24_b26Val : B144 := gcd24_r25Val
def gcd24_q26Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r26Val : B144 := BitVec.ofNat (2 * extensionDegree) 131167751

def gcd24_a27Val : B144 := gcd24_b26Val
def gcd24_b27Val : B144 := gcd24_r26Val
def gcd24_q27Val : B144 := BitVec.ofNat (2 * extensionDegree) 6
def gcd24_r27Val : B144 := BitVec.ofNat (2 * extensionDegree) 5533876

def gcd24_a28Val : B144 := gcd24_b27Val
def gcd24_b28Val : B144 := gcd24_r27Val
def gcd24_q28Val : B144 := BitVec.ofNat (2 * extensionDegree) 24
def gcd24_r28Val : B144 := BitVec.ofNat (2 * extensionDegree) 3537127

def gcd24_a29Val : B144 := gcd24_b28Val
def gcd24_b29Val : B144 := gcd24_r28Val
def gcd24_q29Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r29Val : B144 := BitVec.ofNat (2 * extensionDegree) 686493

def gcd24_a30Val : B144 := gcd24_b29Val
def gcd24_b30Val : B144 := gcd24_r29Val
def gcd24_q30Val : B144 := BitVec.ofNat (2 * extensionDegree) 7
def gcd24_r30Val : B144 := BitVec.ofNat (2 * extensionDegree) 169012

def gcd24_a31Val : B144 := gcd24_b30Val
def gcd24_b31Val : B144 := gcd24_r30Val
def gcd24_q31Val : B144 := BitVec.ofNat (2 * extensionDegree) 4
def gcd24_r31Val : B144 := BitVec.ofNat (2 * extensionDegree) 10573

def gcd24_a32Val : B144 := gcd24_b31Val
def gcd24_b32Val : B144 := gcd24_r31Val
def gcd24_q32Val : B144 := BitVec.ofNat (2 * extensionDegree) 16
def gcd24_r32Val : B144 := BitVec.ofNat (2 * extensionDegree) 228

def gcd24_a33Val : B144 := gcd24_b32Val
def gcd24_b33Val : B144 := gcd24_r32Val
def gcd24_q33Val : B144 := BitVec.ofNat (2 * extensionDegree) 119
def gcd24_r33Val : B144 := BitVec.ofNat (2 * extensionDegree) 49

def gcd24_a34Val : B144 := gcd24_b33Val
def gcd24_b34Val : B144 := gcd24_r33Val
def gcd24_q34Val : B144 := BitVec.ofNat (2 * extensionDegree) 5
def gcd24_r34Val : B144 := BitVec.ofNat (2 * extensionDegree) 17

def gcd24_a35Val : B144 := gcd24_b34Val
def gcd24_b35Val : B144 := gcd24_r34Val
def gcd24_q35Val : B144 := BitVec.ofNat (2 * extensionDegree) 3
def gcd24_r35Val : B144 := BitVec.ofNat (2 * extensionDegree) 2

def gcd24_a36Val : B144 := gcd24_b35Val
def gcd24_b36Val : B144 := gcd24_r35Val
def gcd24_q36Val : B144 := BitVec.ofNat (2 * extensionDegree) 8
def gcd24_r36Val : B144 := BitVec.ofNat (2 * extensionDegree) 1

def gcd24_a37Val : B144 := gcd24_b36Val
def gcd24_b37Val : B144 := gcd24_r36Val
def gcd24_q37Val : B144 := BitVec.ofNat (2 * extensionDegree) 2
def gcd24_r37Val : B144 := BitVec.ofNat (2 * extensionDegree) 0

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

lemma gcd24_step_28 :
    BinaryField.toPoly gcd24_a28Val =
      BinaryField.toPoly gcd24_q28Val * BinaryField.toPoly gcd24_b28Val +
        BinaryField.toPoly gcd24_r28Val := by
  exact verify_div_step (a := gcd24_a28Val) (q := gcd24_q28Val)
    (b := gcd24_b28Val) (r := gcd24_r28Val) (by rfl)

lemma gcd24_step_29 :
    BinaryField.toPoly gcd24_a29Val =
      BinaryField.toPoly gcd24_q29Val * BinaryField.toPoly gcd24_b29Val +
        BinaryField.toPoly gcd24_r29Val := by
  exact verify_div_step (a := gcd24_a29Val) (q := gcd24_q29Val)
    (b := gcd24_b29Val) (r := gcd24_r29Val) (by rfl)

lemma gcd24_step_30 :
    BinaryField.toPoly gcd24_a30Val =
      BinaryField.toPoly gcd24_q30Val * BinaryField.toPoly gcd24_b30Val +
        BinaryField.toPoly gcd24_r30Val := by
  exact verify_div_step (a := gcd24_a30Val) (q := gcd24_q30Val)
    (b := gcd24_b30Val) (r := gcd24_r30Val) (by rfl)

lemma gcd24_step_31 :
    BinaryField.toPoly gcd24_a31Val =
      BinaryField.toPoly gcd24_q31Val * BinaryField.toPoly gcd24_b31Val +
        BinaryField.toPoly gcd24_r31Val := by
  exact verify_div_step (a := gcd24_a31Val) (q := gcd24_q31Val)
    (b := gcd24_b31Val) (r := gcd24_r31Val) (by rfl)

lemma gcd24_step_32 :
    BinaryField.toPoly gcd24_a32Val =
      BinaryField.toPoly gcd24_q32Val * BinaryField.toPoly gcd24_b32Val +
        BinaryField.toPoly gcd24_r32Val := by
  exact verify_div_step (a := gcd24_a32Val) (q := gcd24_q32Val)
    (b := gcd24_b32Val) (r := gcd24_r32Val) (by rfl)

lemma gcd24_step_33 :
    BinaryField.toPoly gcd24_a33Val =
      BinaryField.toPoly gcd24_q33Val * BinaryField.toPoly gcd24_b33Val +
        BinaryField.toPoly gcd24_r33Val := by
  exact verify_div_step (a := gcd24_a33Val) (q := gcd24_q33Val)
    (b := gcd24_b33Val) (r := gcd24_r33Val) (by rfl)

lemma gcd24_step_34 :
    BinaryField.toPoly gcd24_a34Val =
      BinaryField.toPoly gcd24_q34Val * BinaryField.toPoly gcd24_b34Val +
        BinaryField.toPoly gcd24_r34Val := by
  exact verify_div_step (a := gcd24_a34Val) (q := gcd24_q34Val)
    (b := gcd24_b34Val) (r := gcd24_r34Val) (by rfl)

lemma gcd24_step_35 :
    BinaryField.toPoly gcd24_a35Val =
      BinaryField.toPoly gcd24_q35Val * BinaryField.toPoly gcd24_b35Val +
        BinaryField.toPoly gcd24_r35Val := by
  exact verify_div_step (a := gcd24_a35Val) (q := gcd24_q35Val)
    (b := gcd24_b35Val) (r := gcd24_r35Val) (by rfl)

lemma gcd24_step_36 :
    BinaryField.toPoly gcd24_a36Val =
      BinaryField.toPoly gcd24_q36Val * BinaryField.toPoly gcd24_b36Val +
        BinaryField.toPoly gcd24_r36Val := by
  exact verify_div_step (a := gcd24_a36Val) (q := gcd24_q36Val)
    (b := gcd24_b36Val) (r := gcd24_r36Val) (by rfl)

lemma gcd24_step_37 :
    BinaryField.toPoly gcd24_a37Val =
      BinaryField.toPoly gcd24_q37Val * BinaryField.toPoly gcd24_b37Val +
        BinaryField.toPoly gcd24_r37Val := by
  exact verify_div_step (a := gcd24_a37Val) (q := gcd24_q37Val)
    (b := gcd24_b37Val) (r := gcd24_r37Val) (by rfl)

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
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a28Val)
    (BinaryField.toPoly gcd24_b28Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b28Val) (by decide))
    gcd24_step_28]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a29Val)
    (BinaryField.toPoly gcd24_b29Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b29Val) (by decide))
    gcd24_step_29]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a30Val)
    (BinaryField.toPoly gcd24_b30Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b30Val) (by decide))
    gcd24_step_30]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a31Val)
    (BinaryField.toPoly gcd24_b31Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b31Val) (by decide))
    gcd24_step_31]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a32Val)
    (BinaryField.toPoly gcd24_b32Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b32Val) (by decide))
    gcd24_step_32]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a33Val)
    (BinaryField.toPoly gcd24_b33Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b33Val) (by decide))
    gcd24_step_33]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a34Val)
    (BinaryField.toPoly gcd24_b34Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b34Val) (by decide))
    gcd24_step_34]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a35Val)
    (BinaryField.toPoly gcd24_b35Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b35Val) (by decide))
    gcd24_step_35]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a36Val)
    (BinaryField.toPoly gcd24_b36Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b36Val) (by decide))
    gcd24_step_36]
  change EuclideanDomain.gcd (BinaryField.toPoly gcd24_a37Val)
    (BinaryField.toPoly gcd24_b37Val) = 1
  rw [BinaryField.gcd_eq_gcd_next_step
    (hb := by exact toPoly_ne_zero (v := gcd24_b37Val) (by decide))
    gcd24_step_37]
  change EuclideanDomain.gcd
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 1 : B144))
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 0 : B144)) = 1
  rw [BinaryField.toPoly_one_eq_one
    (w := 2 * extensionDegree) (h_w_pos := by unfold extensionDegree; omega)]
  rw [BinaryField.toPoly_zero_eq_zero]
  exact BinaryField.gcd_one_zero

end GF2_72
