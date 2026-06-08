/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_32.XPowTwoPowModCertificate

/-!
# GF(2^32) Rabin GCD Certificate

Kernel-safe Euclidean-division certificate for the Rabin gcd check of
`X ^ 32 + X ^ 22 + X ^ 2 + X + 1`.
-/

namespace GF2_32

open Polynomial

set_option maxRecDepth 1500

private abbrev B64 : Type := BitVec (2 * extensionDegree)

def gcdPVal : B64 := BitVec.ofNat (2 * extensionDegree) 4299161607

/-- Numeric 64-bit encoding of the GF32 defining polynomial. -/
lemma definingPolynomial_eq_gcdPVal :
    definingPolynomial = BinaryField.toPoly gcdPVal := by
  rw [definingPolynomial_eq_P_val]
  have h : P_val = gcdPVal := by
    decide
  rw [h]

/-- Any GF32-width polynomial is already reduced modulo the defining polynomial. -/
lemma toPoly_mod_definingPolynomial_eq_self (v : B32) :
    BinaryField.toPoly v % definingPolynomial = BinaryField.toPoly v := by
  rw [Polynomial.mod_eq_self_iff (hq0 := by exact definingPolynomial_ne_zero)]
  rw [definingPolynomial_degree]
  exact BinaryField.toPoly_degree_lt_w
    (w := extensionDegree) (h_w_pos := by unfold extensionDegree; omega) v

/-- Soundness wrapper specialized to 64-bit Euclidean-division certificates. -/
private theorem verify_div_step {a q b r : B64}
    (h : BinaryField.Extension.checkDivStep (2 * extensionDegree) a q b r = true) :
    BinaryField.toPoly a = BinaryField.toPoly q * BinaryField.toPoly b +
      BinaryField.toPoly r := by
  exact BinaryField.Extension.checkDivStep_correct a q b r h

private theorem toPoly_ne_zero {v : B64} (h : v ≠ 0) :
    BinaryField.toPoly v ≠ 0 :=
  (BinaryField.toPoly_ne_zero_iff_ne_zero v).mpr h

/-- Initial Rabin gcd remainder for exponent `16`. -/
def gcd16_b1Val : B64 := BitVec.ofNat (2 * extensionDegree) 993037024

lemma gcd16_b1Val_eq_zeroExtend :
    gcd16_b1Val = BitVec.zeroExtend (2 * extensionDegree) (r16Val ^^^ r0Val) := by
  decide

def gcd16_a1Val : B64 := gcdPVal
def gcd16_q1Val : B64 := BitVec.ofNat (2 * extensionDegree) 13
def gcd16_r1Val : B64 := BitVec.ofNat (2 * extensionDegree) 238483047

def gcd16_a2Val : B64 := gcd16_b1Val
def gcd16_b2Val : B64 := gcd16_r1Val
def gcd16_q2Val : B64 := BitVec.ofNat (2 * extensionDegree) 4
def gcd16_r2Val : B64 := BitVec.ofNat (2 * extensionDegree) 65753980

def gcd16_a3Val : B64 := gcd16_b2Val
def gcd16_b3Val : B64 := gcd16_r2Val
def gcd16_q3Val : B64 := BitVec.ofNat (2 * extensionDegree) 4
def gcd16_r3Val : B64 := BitVec.ofNat (2 * extensionDegree) 26983319

def gcd16_a4Val : B64 := gcd16_b3Val
def gcd16_b4Val : B64 := gcd16_r3Val
def gcd16_q4Val : B64 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r4Val : B64 := BitVec.ofNat (2 * extensionDegree) 14427218

def gcd16_a5Val : B64 := gcd16_b4Val
def gcd16_b5Val : B64 := gcd16_r4Val
def gcd16_q5Val : B64 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r5Val : B64 := BitVec.ofNat (2 * extensionDegree) 2356019

def gcd16_a6Val : B64 := gcd16_b5Val
def gcd16_b6Val : B64 := gcd16_r5Val
def gcd16_q6Val : B64 := BitVec.ofNat (2 * extensionDegree) 6
def gcd16_r6Val : B64 := BitVec.ofNat (2 * extensionDegree) 1314552

def gcd16_a7Val : B64 := gcd16_b6Val
def gcd16_b7Val : B64 := gcd16_r6Val
def gcd16_q7Val : B64 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r7Val : B64 := BitVec.ofNat (2 * extensionDegree) 782019

def gcd16_a8Val : B64 := gcd16_b7Val
def gcd16_b8Val : B64 := gcd16_r7Val
def gcd16_q8Val : B64 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r8Val : B64 := BitVec.ofNat (2 * extensionDegree) 250750

def gcd16_a9Val : B64 := gcd16_b8Val
def gcd16_b9Val : B64 := gcd16_r8Val
def gcd16_q9Val : B64 := BitVec.ofNat (2 * extensionDegree) 7
def gcd16_r9Val : B64 := BitVec.ofNat (2 * extensionDegree) 54969

def gcd16_a10Val : B64 := gcd16_b9Val
def gcd16_b10Val : B64 := gcd16_r9Val
def gcd16_q10Val : B64 := BitVec.ofNat (2 * extensionDegree) 5
def gcd16_r10Val : B64 := BitVec.ofNat (2 * extensionDegree) 24355

def gcd16_a11Val : B64 := gcd16_b10Val
def gcd16_b11Val : B64 := gcd16_r10Val
def gcd16_q11Val : B64 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r11Val : B64 := BitVec.ofNat (2 * extensionDegree) 14300

def gcd16_a12Val : B64 := gcd16_b11Val
def gcd16_b12Val : B64 := gcd16_r11Val
def gcd16_q12Val : B64 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r12Val : B64 := BitVec.ofNat (2 * extensionDegree) 1863

def gcd16_a13Val : B64 := gcd16_b12Val
def gcd16_b13Val : B64 := gcd16_r12Val
def gcd16_q13Val : B64 := BitVec.ofNat (2 * extensionDegree) 10
def gcd16_r13Val : B64 := BitVec.ofNat (2 * extensionDegree) 874

def gcd16_a14Val : B64 := gcd16_b13Val
def gcd16_b14Val : B64 := gcd16_r13Val
def gcd16_q14Val : B64 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r14Val : B64 := BitVec.ofNat (2 * extensionDegree) 403

def gcd16_a15Val : B64 := gcd16_b14Val
def gcd16_b15Val : B64 := gcd16_r14Val
def gcd16_q15Val : B64 := BitVec.ofNat (2 * extensionDegree) 2
def gcd16_r15Val : B64 := BitVec.ofNat (2 * extensionDegree) 76

def gcd16_a16Val : B64 := gcd16_b15Val
def gcd16_b16Val : B64 := gcd16_r15Val
def gcd16_q16Val : B64 := BitVec.ofNat (2 * extensionDegree) 6
def gcd16_r16Val : B64 := BitVec.ofNat (2 * extensionDegree) 59

def gcd16_a17Val : B64 := gcd16_b16Val
def gcd16_b17Val : B64 := gcd16_r16Val
def gcd16_q17Val : B64 := BitVec.ofNat (2 * extensionDegree) 3
def gcd16_r17Val : B64 := BitVec.ofNat (2 * extensionDegree) 1

def gcd16_a18Val : B64 := gcd16_b17Val
def gcd16_b18Val : B64 := gcd16_r17Val
def gcd16_q18Val : B64 := BitVec.ofNat (2 * extensionDegree) 59
def gcd16_r18Val : B64 := BitVec.ofNat (2 * extensionDegree) 0

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
  change EuclideanDomain.gcd
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 1 : B64))
    (BinaryField.toPoly (BitVec.ofNat (2 * extensionDegree) 0 : B64)) = 1
  rw [BinaryField.toPoly_one_eq_one
    (w := 2 * extensionDegree) (h_w_pos := by unfold extensionDegree; omega)]
  rw [BinaryField.toPoly_zero_eq_zero]
  exact BinaryField.gcd_one_zero

end GF2_32
