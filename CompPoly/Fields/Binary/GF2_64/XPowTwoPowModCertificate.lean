/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.GF2_64.Prelude
import Mathlib.Tactic.NormNum

/-!
# GF(2^64) Modular Frobenius Certificate

Kernel-safe certificate data for repeated squaring of `X` modulo
`X ^ 64 + X ^ 4 + X ^ 3 + X + 1`.
-/

namespace GF2_64

open Polynomial

set_option maxRecDepth 1500

/-- Certificate exponents fit in the doubled-width checker. -/
lemma certificateExponents_bound :
    ∀ exponent ∈ definingPolynomialExponents,
      extensionDegree + exponent ≤ 2 * extensionDegree := by
  unfold definingPolynomialExponents extensionDegree
  decide

/-- Soundness wrapper specialized to the GF64 defining polynomial. -/
private theorem verify_square_step {rPrev q rNext : B64}
    (h :
      BinaryField.Extension.checkSquareStep extensionDegree definingPolynomialExponents
        rPrev q rNext = true) :
    (BinaryField.toPoly rPrev) ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q) *
        definingPolynomial + BinaryField.toPoly rNext := by
  rw [← sparsePolynomial_definingPolynomialExponents]
  exact BinaryField.Extension.checkSquareStep_correct certificateExponents_bound
    rPrev q rNext h

def r0Val : B64 := BitVec.ofNat extensionDegree 2
noncomputable def r0 : Polynomial (ZMod 2) := BinaryField.toPoly r0Val

def q1Val : B64 := BitVec.ofNat extensionDegree 0
def r1Val : B64 := BitVec.ofNat extensionDegree 4
noncomputable def r1 : Polynomial (ZMod 2) := BinaryField.toPoly r1Val

def q2Val : B64 := BitVec.ofNat extensionDegree 0
def r2Val : B64 := BitVec.ofNat extensionDegree 16
noncomputable def r2 : Polynomial (ZMod 2) := BinaryField.toPoly r2Val

def q3Val : B64 := BitVec.ofNat extensionDegree 0
def r3Val : B64 := BitVec.ofNat extensionDegree 256
noncomputable def r3 : Polynomial (ZMod 2) := BinaryField.toPoly r3Val

def q4Val : B64 := BitVec.ofNat extensionDegree 0
def r4Val : B64 := BitVec.ofNat extensionDegree 65536
noncomputable def r4 : Polynomial (ZMod 2) := BinaryField.toPoly r4Val

def q5Val : B64 := BitVec.ofNat extensionDegree 0
def r5Val : B64 := BitVec.ofNat extensionDegree 4294967296
noncomputable def r5 : Polynomial (ZMod 2) := BinaryField.toPoly r5Val

def q6Val : B64 := BitVec.ofNat extensionDegree 1
def r6Val : B64 := BitVec.ofNat extensionDegree 27
noncomputable def r6 : Polynomial (ZMod 2) := BinaryField.toPoly r6Val

def q7Val : B64 := BitVec.ofNat extensionDegree 0
def r7Val : B64 := BitVec.ofNat extensionDegree 325
noncomputable def r7 : Polynomial (ZMod 2) := BinaryField.toPoly r7Val

def q8Val : B64 := BitVec.ofNat extensionDegree 0
def r8Val : B64 := BitVec.ofNat extensionDegree 69649
noncomputable def r8 : Polynomial (ZMod 2) := BinaryField.toPoly r8Val

def q9Val : B64 := BitVec.ofNat extensionDegree 0
def r9Val : B64 := BitVec.ofNat extensionDegree 4311744769
noncomputable def r9 : Polynomial (ZMod 2) := BinaryField.toPoly r9Val

def q10Val : B64 := BitVec.ofNat extensionDegree 1
def r10Val : B64 := BitVec.ofNat extensionDegree 281474976776218
noncomputable def r10 : Polynomial (ZMod 2) := BinaryField.toPoly r10Val

def q11Val : B64 := BitVec.ofNat extensionDegree 4294967296
def r11Val : B64 := BitVec.ofNat extensionDegree 111669150020
noncomputable def r11 : Polynomial (ZMod 2) := BinaryField.toPoly r11Val

def q12Val : B64 := BitVec.ofNat extensionDegree 324
def r12Val : B64 := BitVec.ofNat extensionDegree 69052
noncomputable def r12 : Polynomial (ZMod 2) := BinaryField.toPoly r12Val

def q13Val : B64 := BitVec.ofNat extensionDegree 0
def r13Val : B64 := BitVec.ofNat extensionDegree 4300293456
noncomputable def r13 : Polynomial (ZMod 2) := BinaryField.toPoly r13Val

def q14Val : B64 := BitVec.ofNat extensionDegree 1
def r14Val : B64 := BitVec.ofNat extensionDegree 18696262193435
noncomputable def r14 : Polynomial (ZMod 2) := BinaryField.toPoly r14Val

def q15Val : B64 := BitVec.ofNat extensionDegree 16842753
def r15Val : B64 := BitVec.ofNat extensionDegree 72058698282434910
noncomputable def r15 : Polynomial (ZMod 2) := BinaryField.toPoly r15Val

def q16Val : B64 := BitVec.ofNat extensionDegree 281474976776193
def r16Val : B64 := BitVec.ofNat extensionDegree 98799108396552527
noncomputable def r16 : Polynomial (ZMod 2) := BinaryField.toPoly r16Val

def q17Val : B64 := BitVec.ofNat extensionDegree 300531746672656
def r17Val : B64 := BitVec.ofNat extensionDegree 7508852687479269
noncomputable def r17 : Polynomial (ZMod 2) := BinaryField.toPoly r17Val

def q18Val : B64 := BitVec.ofNat extensionDegree 1392715567109
def r18Val : B64 := BitVec.ofNat extensionDegree 313291816297574
noncomputable def r18 : Polynomial (ZMod 2) := BinaryField.toPoly r18Val

def q19Val : B64 := BitVec.ofNat extensionDegree 4317008981
def r19Val : B64 := BitVec.ofNat extensionDegree 6076785667380547347
noncomputable def r19 : Polynomial (ZMod 2) := BinaryField.toPoly r19Val

def q20Val : B64 := BitVec.ofNat extensionDegree 1229501463002091861
def r20Val : B64 := BitVec.ofNat extensionDegree 13470757684146121986
noncomputable def r20 : Polynomial (ZMod 2) := BinaryField.toPoly r20Val

def q21Val : B64 := BitVec.ofNat extensionDegree 4991207750979831122
def r21Val : B64 := BitVec.ofNat extensionDegree 12749500389507444802
noncomputable def r21 : Polynomial (ZMod 2) := BinaryField.toPoly r21Val

def q22Val : B64 := BitVec.ofNat extensionDegree 4972066712951521367
def r22Val : B64 := BitVec.ofNat extensionDegree 16291502563427555125
noncomputable def r22 : Polynomial (ZMod 2) := BinaryField.toPoly r22Val

def q23Val : B64 := BitVec.ofNat extensionDegree 6053964988803256322
def r23Val : B64 := BitVec.ofNat extensionDegree 5203926764172326183
noncomputable def r23 : Polynomial (ZMod 2) := BinaryField.toPoly r23Val

def q24Val : B64 := BitVec.ofNat extensionDegree 1170941675557966085
def r24Val : B64 := BitVec.ofNat extensionDegree 13174495406275522402
noncomputable def r24 : Polynomial (ZMod 2) := BinaryField.toPoly r24Val

def q25Val : B64 := BitVec.ofNat extensionDegree 4977692621692555287
def r25Val : B64 := BitVec.ofNat extensionDegree 12024447909651637749
noncomputable def r25 : Polynomial (ZMod 2) := BinaryField.toPoly r25Val

def q26Val : B64 := BitVec.ofNat extensionDegree 4905635319967466562
def r26Val : B64 := BitVec.ofNat extensionDegree 13393486797395263463
noncomputable def r26 : Polynomial (ZMod 2) := BinaryField.toPoly r26Val

def q27Val : B64 := BitVec.ofNat extensionDegree 4990359287705440275
def r27Val : B64 := BitVec.ofNat extensionDegree 16251283266509727112
noncomputable def r27 : Polynomial (ZMod 2) := BinaryField.toPoly r27Val

def q28Val : B64 := BitVec.ofNat extensionDegree 6053190017856045074
def r28Val : B64 := BitVec.ofNat extensionDegree 1733189407169659334
noncomputable def r28 : Polynomial (ZMod 2) := BinaryField.toPoly r28Val

def q29Val : B64 := BitVec.ofNat extensionDegree 90072341514830097
def r29Val : B64 := BitVec.ofNat extensionDegree 1771135578840730303
noncomputable def r29 : Polynomial (ZMod 2) := BinaryField.toPoly r29Val

def q30Val : B64 := BitVec.ofNat extensionDegree 90143529809220688
def r30Val : B64 := BitVec.ofNat extensionDegree 5532544551272160805
noncomputable def r30 : Polynomial (ZMod 2) := BinaryField.toPoly r30Val

def q31Val : B64 := BitVec.ofNat extensionDegree 1175527554946520337
def r31Val : B64 := BitVec.ofNat extensionDegree 16371482399015699130
noncomputable def r31 : Polynomial (ZMod 2) := BinaryField.toPoly r31Val

def q32Val : B64 := BitVec.ofNat extensionDegree 6054250793186377735
def r32Val : B64 := BitVec.ofNat extensionDegree 6656922126492271877
noncomputable def r32 : Polynomial (ZMod 2) := BinaryField.toPoly r32Val

def q33Val : B64 := BitVec.ofNat extensionDegree 1247519104261493780
def r33Val : B64 := BitVec.ofNat extensionDegree 13359044734667447757
noncomputable def r33 : Polynomial (ZMod 2) := BinaryField.toPoly r33Val

def q34Val : B64 := BitVec.ofNat extensionDegree 4990291922419455046
def r34Val : B64 := BitVec.ofNat extensionDegree 13081489766298454731
noncomputable def r34 : Polynomial (ZMod 2) := BinaryField.toPoly r34Val

def q35Val : B64 := BitVec.ofNat extensionDegree 4976829725369517058
def r35Val : B64 := BitVec.ofNat extensionDegree 12969455067531443315
noncomputable def r35 : Polynomial (ZMod 2) := BinaryField.toPoly r35Val

def q36Val : B64 := BitVec.ofNat extensionDegree 4973475166928782403
def r36Val : B64 := BitVec.ofNat extensionDegree 12854470937230884840
noncomputable def r36 : Polynomial (ZMod 2) := BinaryField.toPoly r36Val

def q37Val : B64 := BitVec.ofNat extensionDegree 4973121947744404754
def r37Val : B64 := BitVec.ofNat extensionDegree 12933450780795347654
noncomputable def r37 : Polynomial (ZMod 2) := BinaryField.toPoly r37Val

def q38Val : B64 := BitVec.ofNat extensionDegree 4973404798205318423
def r38Val : B64 := BitVec.ofNat extensionDegree 16314237025689753317
noncomputable def r38 : Polynomial (ZMod 2) := BinaryField.toPoly r38Val

def q39Val : B64 := BitVec.ofNat extensionDegree 6053985880878613506
def r39Val : B64 := BitVec.ofNat extensionDegree 589001530574911527
noncomputable def r39 : Polynomial (ZMod 2) := BinaryField.toPoly r39Val

def q40Val : B64 := BitVec.ofNat extensionDegree 18019141232447505
def r40Val : B64 := BitVec.ofNat extensionDegree 1406365973223339454
noncomputable def r40 : Polynomial (ZMod 2) := BinaryField.toPoly r40Val

def q41Val : B64 := BitVec.ofNat extensionDegree 73535406725141524
def r41Val : B64 := BitVec.ofNat extensionDegree 5437469698763298952
noncomputable def r41 : Polynomial (ZMod 2) := BinaryField.toPoly r41Val

def q42Val : B64 := BitVec.ofNat extensionDegree 1172366442101822464
def r42Val : B64 := BitVec.ofNat extensionDegree 16637286567612537920
noncomputable def r42 : Polynomial (ZMod 2) := BinaryField.toPoly r42Val

def q43Val : B64 := BitVec.ofNat extensionDegree 6058559780245820759
def r43Val : B64 := BitVec.ofNat extensionDegree 1791104586889564209
noncomputable def r43 : Polynomial (ZMod 2) := BinaryField.toPoly r43Val

def q44Val : B64 := BitVec.ofNat extensionDegree 90161349614633985
def r44Val : B64 := BitVec.ofNat extensionDegree 5532225425759037722
noncomputable def r44 : Polynomial (ZMod 2) := BinaryField.toPoly r44Val

def q45Val : B64 := BitVec.ofNat extensionDegree 1175527549913089301
def r45Val : B64 := BitVec.ofNat extensionDegree 17465559541434070915
noncomputable def r45 : Polynomial (ZMod 2) := BinaryField.toPoly r45Val

def q46Val : B64 := BitVec.ofNat extensionDegree 6126043400610337110
def r46Val : B64 := BitVec.ofNat extensionDegree 6285227636684303407
noncomputable def r46 : Polynomial (ZMod 2) := BinaryField.toPoly r46Val

def q47Val : B64 := BitVec.ofNat extensionDegree 1230895850982540625
def r47Val : B64 := BitVec.ofNat extensionDegree 12575863927935300670
noncomputable def r47 : Polynomial (ZMod 2) := BinaryField.toPoly r47Val

def q48Val : B64 := BitVec.ofNat extensionDegree 4923630747618722134
def r48Val : B64 := BitVec.ofNat extensionDegree 18039947418024139134
noncomputable def r48 : Polynomial (ZMod 2) := BinaryField.toPoly r48Val

def q49Val : B64 := BitVec.ofNat extensionDegree 6144054776738890055
def r49Val : B64 := BitVec.ofNat extensionDegree 5812368083904874709
noncomputable def r49 : Polynomial (ZMod 2) := BinaryField.toPoly r49Val

def q50Val : B64 := BitVec.ofNat extensionDegree 1225054145754518853
def r50Val : B64 := BitVec.ofNat extensionDegree 12612049045170180262
noncomputable def r50 : Polynomial (ZMod 2) := BinaryField.toPoly r50Val

def q51Val : B64 := BitVec.ofNat extensionDegree 4923841854930505798
def r51Val : B64 := BitVec.ofNat extensionDegree 18321212328940417678
noncomputable def r51 : Polynomial (ZMod 2) := BinaryField.toPoly r51Val

def q52Val : B64 := BitVec.ofNat extensionDegree 6148557000634613826
def r52Val : B64 := BitVec.ofNat extensionDegree 80132871367001762
noncomputable def r52 : Polynomial (ZMod 2) := BinaryField.toPoly r52Val

def q53Val : B64 := BitVec.ofNat extensionDegree 282919243355216
def r53Val : B64 := BitVec.ofNat extensionDegree 3193222135652212
noncomputable def r53 : Polynomial (ZMod 2) := BinaryField.toPoly r53Val

def q54Val : B64 := BitVec.ofNat extensionDegree 296642151701
def r54Val : B64 := BitVec.ofNat extensionDegree 6130814885544944599
noncomputable def r54 : Polynomial (ZMod 2) := BinaryField.toPoly r54Val

def q55Val : B64 := BitVec.ofNat extensionDegree 1229765345776321556
def r55Val : B64 := BitVec.ofNat extensionDegree 18373379959575346377
noncomputable def r55 : Polynomial (ZMod 2) := BinaryField.toPoly r55Val

def q56Val : B64 := BitVec.ofNat extensionDegree 6148633146398426435
def r56Val : B64 := BitVec.ofNat extensionDegree 74962121387008428
noncomputable def r56 : Polynomial (ZMod 2) := BinaryField.toPoly r56Val

def q57Val : B64 := BitVec.ofNat extensionDegree 281767319782420
def r57Val : B64 := BitVec.ofNat extensionDegree 6150600619072481676
noncomputable def r57 : Polynomial (ZMod 2) := BinaryField.toPoly r57Val

def q58Val : B64 := BitVec.ofNat extensionDegree 1229783161584763985
def r58Val : B64 := BitVec.ofNat extensionDegree 18446652706856364859
noncomputable def r58 : Polynomial (ZMod 2) := BinaryField.toPoly r58Val

def q59Val : B64 := BitVec.ofNat extensionDegree 6148914690950976531
def r59Val : B64 := BitVec.ofNat extensionDegree 6148825560630040792
noncomputable def r59 : Polynomial (ZMod 2) := BinaryField.toPoly r59Val

def q60Val : B64 := BitVec.ofNat extensionDegree 1229782937962024977
def r60Val : B64 := BitVec.ofNat extensionDegree 18446655764902830315
noncomputable def r60 : Polynomial (ZMod 2) := BinaryField.toPoly r60Val

def q61Val : B64 := BitVec.ofNat extensionDegree 6148914690951300178
def r61Val : B64 := BitVec.ofNat extensionDegree 93462766681859
noncomputable def r61 : Polynomial (ZMod 2) := BinaryField.toPoly r61Val

def q62Val : B64 := BitVec.ofNat extensionDegree 286326784
def r62Val : B64 := BitVec.ofNat extensionDegree 6148820870539116549
noncomputable def r62 : Polynomial (ZMod 2) := BinaryField.toPoly r62Val

def q63Val : B64 := BitVec.ofNat extensionDegree 1229782937960972289
def r63Val : B64 := BitVec.ofNat extensionDegree 18446744069414584330
noncomputable def r63 : Polynomial (ZMod 2) := BinaryField.toPoly r63Val

def q64Val : B64 := BitVec.ofNat extensionDegree 6148914691236517202
def r64Val : B64 := BitVec.ofNat extensionDegree 2
noncomputable def r64 : Polynomial (ZMod 2) := BinaryField.toPoly r64Val

/-- The initial remainder denotes `X`. -/
lemma r0_eq_X : r0 = X := by
  rw [r0, r0Val, extensionDegree]
  have h : (BitVec.ofNat 64 2 : BitVec 64) = (1 <<< 1 : BitVec 64) := by
    decide
  rw [h]
  simpa only [pow_one] using
    BinaryField.Extension.toPoly_one_shiftLeft (w := 64) 1 (by decide)

/-- The final remainder after 64 Frobenius steps denotes `X`. -/
lemma r64_eq_X : r64 = X := by
  rw [r64, r64Val, extensionDegree]
  have h : (BitVec.ofNat 64 2 : BitVec 64) = (1 <<< 1 : BitVec 64) := by
    decide
  rw [h]
  simpa only [pow_one] using
    BinaryField.Extension.toPoly_one_shiftLeft (w := 64) 1 (by decide)

/-- Certificate step 1: square and reduce modulo the GF64 polynomial. -/
lemma step_1 :
    r0 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q1Val) *
        definingPolynomial + r1 := by
  change (BinaryField.toPoly r0Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q1Val) *
      definingPolynomial + BinaryField.toPoly r1Val
  exact verify_square_step (rPrev := r0Val) (q := q1Val)
    (rNext := r1Val) (by rfl)

/-- Certificate step 2: square and reduce modulo the GF64 polynomial. -/
lemma step_2 :
    r1 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q2Val) *
        definingPolynomial + r2 := by
  change (BinaryField.toPoly r1Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q2Val) *
      definingPolynomial + BinaryField.toPoly r2Val
  exact verify_square_step (rPrev := r1Val) (q := q2Val)
    (rNext := r2Val) (by rfl)

/-- Certificate step 3: square and reduce modulo the GF64 polynomial. -/
lemma step_3 :
    r2 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q3Val) *
        definingPolynomial + r3 := by
  change (BinaryField.toPoly r2Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q3Val) *
      definingPolynomial + BinaryField.toPoly r3Val
  exact verify_square_step (rPrev := r2Val) (q := q3Val)
    (rNext := r3Val) (by rfl)

/-- Certificate step 4: square and reduce modulo the GF64 polynomial. -/
lemma step_4 :
    r3 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q4Val) *
        definingPolynomial + r4 := by
  change (BinaryField.toPoly r3Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q4Val) *
      definingPolynomial + BinaryField.toPoly r4Val
  exact verify_square_step (rPrev := r3Val) (q := q4Val)
    (rNext := r4Val) (by rfl)

/-- Certificate step 5: square and reduce modulo the GF64 polynomial. -/
lemma step_5 :
    r4 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q5Val) *
        definingPolynomial + r5 := by
  change (BinaryField.toPoly r4Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q5Val) *
      definingPolynomial + BinaryField.toPoly r5Val
  exact verify_square_step (rPrev := r4Val) (q := q5Val)
    (rNext := r5Val) (by rfl)

/-- Certificate step 6: square and reduce modulo the GF64 polynomial. -/
lemma step_6 :
    r5 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q6Val) *
        definingPolynomial + r6 := by
  change (BinaryField.toPoly r5Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q6Val) *
      definingPolynomial + BinaryField.toPoly r6Val
  exact verify_square_step (rPrev := r5Val) (q := q6Val)
    (rNext := r6Val) (by rfl)

/-- Certificate step 7: square and reduce modulo the GF64 polynomial. -/
lemma step_7 :
    r6 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q7Val) *
        definingPolynomial + r7 := by
  change (BinaryField.toPoly r6Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q7Val) *
      definingPolynomial + BinaryField.toPoly r7Val
  exact verify_square_step (rPrev := r6Val) (q := q7Val)
    (rNext := r7Val) (by rfl)

/-- Certificate step 8: square and reduce modulo the GF64 polynomial. -/
lemma step_8 :
    r7 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q8Val) *
        definingPolynomial + r8 := by
  change (BinaryField.toPoly r7Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q8Val) *
      definingPolynomial + BinaryField.toPoly r8Val
  exact verify_square_step (rPrev := r7Val) (q := q8Val)
    (rNext := r8Val) (by rfl)

/-- Certificate step 9: square and reduce modulo the GF64 polynomial. -/
lemma step_9 :
    r8 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q9Val) *
        definingPolynomial + r9 := by
  change (BinaryField.toPoly r8Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q9Val) *
      definingPolynomial + BinaryField.toPoly r9Val
  exact verify_square_step (rPrev := r8Val) (q := q9Val)
    (rNext := r9Val) (by rfl)

/-- Certificate step 10: square and reduce modulo the GF64 polynomial. -/
lemma step_10 :
    r9 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q10Val) *
        definingPolynomial + r10 := by
  change (BinaryField.toPoly r9Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q10Val) *
      definingPolynomial + BinaryField.toPoly r10Val
  exact verify_square_step (rPrev := r9Val) (q := q10Val)
    (rNext := r10Val) (by rfl)

/-- Certificate step 11: square and reduce modulo the GF64 polynomial. -/
lemma step_11 :
    r10 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q11Val) *
        definingPolynomial + r11 := by
  change (BinaryField.toPoly r10Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q11Val) *
      definingPolynomial + BinaryField.toPoly r11Val
  exact verify_square_step (rPrev := r10Val) (q := q11Val)
    (rNext := r11Val) (by rfl)

/-- Certificate step 12: square and reduce modulo the GF64 polynomial. -/
lemma step_12 :
    r11 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q12Val) *
        definingPolynomial + r12 := by
  change (BinaryField.toPoly r11Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q12Val) *
      definingPolynomial + BinaryField.toPoly r12Val
  exact verify_square_step (rPrev := r11Val) (q := q12Val)
    (rNext := r12Val) (by rfl)

/-- Certificate step 13: square and reduce modulo the GF64 polynomial. -/
lemma step_13 :
    r12 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q13Val) *
        definingPolynomial + r13 := by
  change (BinaryField.toPoly r12Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q13Val) *
      definingPolynomial + BinaryField.toPoly r13Val
  exact verify_square_step (rPrev := r12Val) (q := q13Val)
    (rNext := r13Val) (by rfl)

/-- Certificate step 14: square and reduce modulo the GF64 polynomial. -/
lemma step_14 :
    r13 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q14Val) *
        definingPolynomial + r14 := by
  change (BinaryField.toPoly r13Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q14Val) *
      definingPolynomial + BinaryField.toPoly r14Val
  exact verify_square_step (rPrev := r13Val) (q := q14Val)
    (rNext := r14Val) (by rfl)

/-- Certificate step 15: square and reduce modulo the GF64 polynomial. -/
lemma step_15 :
    r14 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q15Val) *
        definingPolynomial + r15 := by
  change (BinaryField.toPoly r14Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q15Val) *
      definingPolynomial + BinaryField.toPoly r15Val
  exact verify_square_step (rPrev := r14Val) (q := q15Val)
    (rNext := r15Val) (by rfl)

/-- Certificate step 16: square and reduce modulo the GF64 polynomial. -/
lemma step_16 :
    r15 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q16Val) *
        definingPolynomial + r16 := by
  change (BinaryField.toPoly r15Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q16Val) *
      definingPolynomial + BinaryField.toPoly r16Val
  exact verify_square_step (rPrev := r15Val) (q := q16Val)
    (rNext := r16Val) (by rfl)

/-- Certificate step 17: square and reduce modulo the GF64 polynomial. -/
lemma step_17 :
    r16 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q17Val) *
        definingPolynomial + r17 := by
  change (BinaryField.toPoly r16Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q17Val) *
      definingPolynomial + BinaryField.toPoly r17Val
  exact verify_square_step (rPrev := r16Val) (q := q17Val)
    (rNext := r17Val) (by rfl)

/-- Certificate step 18: square and reduce modulo the GF64 polynomial. -/
lemma step_18 :
    r17 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q18Val) *
        definingPolynomial + r18 := by
  change (BinaryField.toPoly r17Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q18Val) *
      definingPolynomial + BinaryField.toPoly r18Val
  exact verify_square_step (rPrev := r17Val) (q := q18Val)
    (rNext := r18Val) (by rfl)

/-- Certificate step 19: square and reduce modulo the GF64 polynomial. -/
lemma step_19 :
    r18 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q19Val) *
        definingPolynomial + r19 := by
  change (BinaryField.toPoly r18Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q19Val) *
      definingPolynomial + BinaryField.toPoly r19Val
  exact verify_square_step (rPrev := r18Val) (q := q19Val)
    (rNext := r19Val) (by rfl)

/-- Certificate step 20: square and reduce modulo the GF64 polynomial. -/
lemma step_20 :
    r19 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q20Val) *
        definingPolynomial + r20 := by
  change (BinaryField.toPoly r19Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q20Val) *
      definingPolynomial + BinaryField.toPoly r20Val
  exact verify_square_step (rPrev := r19Val) (q := q20Val)
    (rNext := r20Val) (by rfl)

/-- Certificate step 21: square and reduce modulo the GF64 polynomial. -/
lemma step_21 :
    r20 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q21Val) *
        definingPolynomial + r21 := by
  change (BinaryField.toPoly r20Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q21Val) *
      definingPolynomial + BinaryField.toPoly r21Val
  exact verify_square_step (rPrev := r20Val) (q := q21Val)
    (rNext := r21Val) (by rfl)

/-- Certificate step 22: square and reduce modulo the GF64 polynomial. -/
lemma step_22 :
    r21 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q22Val) *
        definingPolynomial + r22 := by
  change (BinaryField.toPoly r21Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q22Val) *
      definingPolynomial + BinaryField.toPoly r22Val
  exact verify_square_step (rPrev := r21Val) (q := q22Val)
    (rNext := r22Val) (by rfl)

/-- Certificate step 23: square and reduce modulo the GF64 polynomial. -/
lemma step_23 :
    r22 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q23Val) *
        definingPolynomial + r23 := by
  change (BinaryField.toPoly r22Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q23Val) *
      definingPolynomial + BinaryField.toPoly r23Val
  exact verify_square_step (rPrev := r22Val) (q := q23Val)
    (rNext := r23Val) (by rfl)

/-- Certificate step 24: square and reduce modulo the GF64 polynomial. -/
lemma step_24 :
    r23 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q24Val) *
        definingPolynomial + r24 := by
  change (BinaryField.toPoly r23Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q24Val) *
      definingPolynomial + BinaryField.toPoly r24Val
  exact verify_square_step (rPrev := r23Val) (q := q24Val)
    (rNext := r24Val) (by rfl)

/-- Certificate step 25: square and reduce modulo the GF64 polynomial. -/
lemma step_25 :
    r24 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q25Val) *
        definingPolynomial + r25 := by
  change (BinaryField.toPoly r24Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q25Val) *
      definingPolynomial + BinaryField.toPoly r25Val
  exact verify_square_step (rPrev := r24Val) (q := q25Val)
    (rNext := r25Val) (by rfl)

/-- Certificate step 26: square and reduce modulo the GF64 polynomial. -/
lemma step_26 :
    r25 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q26Val) *
        definingPolynomial + r26 := by
  change (BinaryField.toPoly r25Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q26Val) *
      definingPolynomial + BinaryField.toPoly r26Val
  exact verify_square_step (rPrev := r25Val) (q := q26Val)
    (rNext := r26Val) (by rfl)

/-- Certificate step 27: square and reduce modulo the GF64 polynomial. -/
lemma step_27 :
    r26 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q27Val) *
        definingPolynomial + r27 := by
  change (BinaryField.toPoly r26Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q27Val) *
      definingPolynomial + BinaryField.toPoly r27Val
  exact verify_square_step (rPrev := r26Val) (q := q27Val)
    (rNext := r27Val) (by rfl)

/-- Certificate step 28: square and reduce modulo the GF64 polynomial. -/
lemma step_28 :
    r27 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q28Val) *
        definingPolynomial + r28 := by
  change (BinaryField.toPoly r27Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q28Val) *
      definingPolynomial + BinaryField.toPoly r28Val
  exact verify_square_step (rPrev := r27Val) (q := q28Val)
    (rNext := r28Val) (by rfl)

/-- Certificate step 29: square and reduce modulo the GF64 polynomial. -/
lemma step_29 :
    r28 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q29Val) *
        definingPolynomial + r29 := by
  change (BinaryField.toPoly r28Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q29Val) *
      definingPolynomial + BinaryField.toPoly r29Val
  exact verify_square_step (rPrev := r28Val) (q := q29Val)
    (rNext := r29Val) (by rfl)

/-- Certificate step 30: square and reduce modulo the GF64 polynomial. -/
lemma step_30 :
    r29 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q30Val) *
        definingPolynomial + r30 := by
  change (BinaryField.toPoly r29Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q30Val) *
      definingPolynomial + BinaryField.toPoly r30Val
  exact verify_square_step (rPrev := r29Val) (q := q30Val)
    (rNext := r30Val) (by rfl)

/-- Certificate step 31: square and reduce modulo the GF64 polynomial. -/
lemma step_31 :
    r30 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q31Val) *
        definingPolynomial + r31 := by
  change (BinaryField.toPoly r30Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q31Val) *
      definingPolynomial + BinaryField.toPoly r31Val
  exact verify_square_step (rPrev := r30Val) (q := q31Val)
    (rNext := r31Val) (by rfl)

/-- Certificate step 32: square and reduce modulo the GF64 polynomial. -/
lemma step_32 :
    r31 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q32Val) *
        definingPolynomial + r32 := by
  change (BinaryField.toPoly r31Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q32Val) *
      definingPolynomial + BinaryField.toPoly r32Val
  exact verify_square_step (rPrev := r31Val) (q := q32Val)
    (rNext := r32Val) (by rfl)

/-- Certificate step 33: square and reduce modulo the GF64 polynomial. -/
lemma step_33 :
    r32 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q33Val) *
        definingPolynomial + r33 := by
  change (BinaryField.toPoly r32Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q33Val) *
      definingPolynomial + BinaryField.toPoly r33Val
  exact verify_square_step (rPrev := r32Val) (q := q33Val)
    (rNext := r33Val) (by rfl)

/-- Certificate step 34: square and reduce modulo the GF64 polynomial. -/
lemma step_34 :
    r33 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q34Val) *
        definingPolynomial + r34 := by
  change (BinaryField.toPoly r33Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q34Val) *
      definingPolynomial + BinaryField.toPoly r34Val
  exact verify_square_step (rPrev := r33Val) (q := q34Val)
    (rNext := r34Val) (by rfl)

/-- Certificate step 35: square and reduce modulo the GF64 polynomial. -/
lemma step_35 :
    r34 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q35Val) *
        definingPolynomial + r35 := by
  change (BinaryField.toPoly r34Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q35Val) *
      definingPolynomial + BinaryField.toPoly r35Val
  exact verify_square_step (rPrev := r34Val) (q := q35Val)
    (rNext := r35Val) (by rfl)

/-- Certificate step 36: square and reduce modulo the GF64 polynomial. -/
lemma step_36 :
    r35 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q36Val) *
        definingPolynomial + r36 := by
  change (BinaryField.toPoly r35Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q36Val) *
      definingPolynomial + BinaryField.toPoly r36Val
  exact verify_square_step (rPrev := r35Val) (q := q36Val)
    (rNext := r36Val) (by rfl)

/-- Certificate step 37: square and reduce modulo the GF64 polynomial. -/
lemma step_37 :
    r36 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q37Val) *
        definingPolynomial + r37 := by
  change (BinaryField.toPoly r36Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q37Val) *
      definingPolynomial + BinaryField.toPoly r37Val
  exact verify_square_step (rPrev := r36Val) (q := q37Val)
    (rNext := r37Val) (by rfl)

/-- Certificate step 38: square and reduce modulo the GF64 polynomial. -/
lemma step_38 :
    r37 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q38Val) *
        definingPolynomial + r38 := by
  change (BinaryField.toPoly r37Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q38Val) *
      definingPolynomial + BinaryField.toPoly r38Val
  exact verify_square_step (rPrev := r37Val) (q := q38Val)
    (rNext := r38Val) (by rfl)

/-- Certificate step 39: square and reduce modulo the GF64 polynomial. -/
lemma step_39 :
    r38 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q39Val) *
        definingPolynomial + r39 := by
  change (BinaryField.toPoly r38Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q39Val) *
      definingPolynomial + BinaryField.toPoly r39Val
  exact verify_square_step (rPrev := r38Val) (q := q39Val)
    (rNext := r39Val) (by rfl)

/-- Certificate step 40: square and reduce modulo the GF64 polynomial. -/
lemma step_40 :
    r39 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q40Val) *
        definingPolynomial + r40 := by
  change (BinaryField.toPoly r39Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q40Val) *
      definingPolynomial + BinaryField.toPoly r40Val
  exact verify_square_step (rPrev := r39Val) (q := q40Val)
    (rNext := r40Val) (by rfl)

/-- Certificate step 41: square and reduce modulo the GF64 polynomial. -/
lemma step_41 :
    r40 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q41Val) *
        definingPolynomial + r41 := by
  change (BinaryField.toPoly r40Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q41Val) *
      definingPolynomial + BinaryField.toPoly r41Val
  exact verify_square_step (rPrev := r40Val) (q := q41Val)
    (rNext := r41Val) (by rfl)

/-- Certificate step 42: square and reduce modulo the GF64 polynomial. -/
lemma step_42 :
    r41 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q42Val) *
        definingPolynomial + r42 := by
  change (BinaryField.toPoly r41Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q42Val) *
      definingPolynomial + BinaryField.toPoly r42Val
  exact verify_square_step (rPrev := r41Val) (q := q42Val)
    (rNext := r42Val) (by rfl)

/-- Certificate step 43: square and reduce modulo the GF64 polynomial. -/
lemma step_43 :
    r42 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q43Val) *
        definingPolynomial + r43 := by
  change (BinaryField.toPoly r42Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q43Val) *
      definingPolynomial + BinaryField.toPoly r43Val
  exact verify_square_step (rPrev := r42Val) (q := q43Val)
    (rNext := r43Val) (by rfl)

/-- Certificate step 44: square and reduce modulo the GF64 polynomial. -/
lemma step_44 :
    r43 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q44Val) *
        definingPolynomial + r44 := by
  change (BinaryField.toPoly r43Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q44Val) *
      definingPolynomial + BinaryField.toPoly r44Val
  exact verify_square_step (rPrev := r43Val) (q := q44Val)
    (rNext := r44Val) (by rfl)

/-- Certificate step 45: square and reduce modulo the GF64 polynomial. -/
lemma step_45 :
    r44 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q45Val) *
        definingPolynomial + r45 := by
  change (BinaryField.toPoly r44Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q45Val) *
      definingPolynomial + BinaryField.toPoly r45Val
  exact verify_square_step (rPrev := r44Val) (q := q45Val)
    (rNext := r45Val) (by rfl)

/-- Certificate step 46: square and reduce modulo the GF64 polynomial. -/
lemma step_46 :
    r45 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q46Val) *
        definingPolynomial + r46 := by
  change (BinaryField.toPoly r45Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q46Val) *
      definingPolynomial + BinaryField.toPoly r46Val
  exact verify_square_step (rPrev := r45Val) (q := q46Val)
    (rNext := r46Val) (by rfl)

/-- Certificate step 47: square and reduce modulo the GF64 polynomial. -/
lemma step_47 :
    r46 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q47Val) *
        definingPolynomial + r47 := by
  change (BinaryField.toPoly r46Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q47Val) *
      definingPolynomial + BinaryField.toPoly r47Val
  exact verify_square_step (rPrev := r46Val) (q := q47Val)
    (rNext := r47Val) (by rfl)

/-- Certificate step 48: square and reduce modulo the GF64 polynomial. -/
lemma step_48 :
    r47 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q48Val) *
        definingPolynomial + r48 := by
  change (BinaryField.toPoly r47Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q48Val) *
      definingPolynomial + BinaryField.toPoly r48Val
  exact verify_square_step (rPrev := r47Val) (q := q48Val)
    (rNext := r48Val) (by rfl)

/-- Certificate step 49: square and reduce modulo the GF64 polynomial. -/
lemma step_49 :
    r48 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q49Val) *
        definingPolynomial + r49 := by
  change (BinaryField.toPoly r48Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q49Val) *
      definingPolynomial + BinaryField.toPoly r49Val
  exact verify_square_step (rPrev := r48Val) (q := q49Val)
    (rNext := r49Val) (by rfl)

/-- Certificate step 50: square and reduce modulo the GF64 polynomial. -/
lemma step_50 :
    r49 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q50Val) *
        definingPolynomial + r50 := by
  change (BinaryField.toPoly r49Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q50Val) *
      definingPolynomial + BinaryField.toPoly r50Val
  exact verify_square_step (rPrev := r49Val) (q := q50Val)
    (rNext := r50Val) (by rfl)

/-- Certificate step 51: square and reduce modulo the GF64 polynomial. -/
lemma step_51 :
    r50 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q51Val) *
        definingPolynomial + r51 := by
  change (BinaryField.toPoly r50Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q51Val) *
      definingPolynomial + BinaryField.toPoly r51Val
  exact verify_square_step (rPrev := r50Val) (q := q51Val)
    (rNext := r51Val) (by rfl)

/-- Certificate step 52: square and reduce modulo the GF64 polynomial. -/
lemma step_52 :
    r51 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q52Val) *
        definingPolynomial + r52 := by
  change (BinaryField.toPoly r51Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q52Val) *
      definingPolynomial + BinaryField.toPoly r52Val
  exact verify_square_step (rPrev := r51Val) (q := q52Val)
    (rNext := r52Val) (by rfl)

/-- Certificate step 53: square and reduce modulo the GF64 polynomial. -/
lemma step_53 :
    r52 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q53Val) *
        definingPolynomial + r53 := by
  change (BinaryField.toPoly r52Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q53Val) *
      definingPolynomial + BinaryField.toPoly r53Val
  exact verify_square_step (rPrev := r52Val) (q := q53Val)
    (rNext := r53Val) (by rfl)

/-- Certificate step 54: square and reduce modulo the GF64 polynomial. -/
lemma step_54 :
    r53 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q54Val) *
        definingPolynomial + r54 := by
  change (BinaryField.toPoly r53Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q54Val) *
      definingPolynomial + BinaryField.toPoly r54Val
  exact verify_square_step (rPrev := r53Val) (q := q54Val)
    (rNext := r54Val) (by rfl)

/-- Certificate step 55: square and reduce modulo the GF64 polynomial. -/
lemma step_55 :
    r54 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q55Val) *
        definingPolynomial + r55 := by
  change (BinaryField.toPoly r54Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q55Val) *
      definingPolynomial + BinaryField.toPoly r55Val
  exact verify_square_step (rPrev := r54Val) (q := q55Val)
    (rNext := r55Val) (by rfl)

/-- Certificate step 56: square and reduce modulo the GF64 polynomial. -/
lemma step_56 :
    r55 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q56Val) *
        definingPolynomial + r56 := by
  change (BinaryField.toPoly r55Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q56Val) *
      definingPolynomial + BinaryField.toPoly r56Val
  exact verify_square_step (rPrev := r55Val) (q := q56Val)
    (rNext := r56Val) (by rfl)

/-- Certificate step 57: square and reduce modulo the GF64 polynomial. -/
lemma step_57 :
    r56 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q57Val) *
        definingPolynomial + r57 := by
  change (BinaryField.toPoly r56Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q57Val) *
      definingPolynomial + BinaryField.toPoly r57Val
  exact verify_square_step (rPrev := r56Val) (q := q57Val)
    (rNext := r57Val) (by rfl)

/-- Certificate step 58: square and reduce modulo the GF64 polynomial. -/
lemma step_58 :
    r57 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q58Val) *
        definingPolynomial + r58 := by
  change (BinaryField.toPoly r57Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q58Val) *
      definingPolynomial + BinaryField.toPoly r58Val
  exact verify_square_step (rPrev := r57Val) (q := q58Val)
    (rNext := r58Val) (by rfl)

/-- Certificate step 59: square and reduce modulo the GF64 polynomial. -/
lemma step_59 :
    r58 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q59Val) *
        definingPolynomial + r59 := by
  change (BinaryField.toPoly r58Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q59Val) *
      definingPolynomial + BinaryField.toPoly r59Val
  exact verify_square_step (rPrev := r58Val) (q := q59Val)
    (rNext := r59Val) (by rfl)

/-- Certificate step 60: square and reduce modulo the GF64 polynomial. -/
lemma step_60 :
    r59 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q60Val) *
        definingPolynomial + r60 := by
  change (BinaryField.toPoly r59Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q60Val) *
      definingPolynomial + BinaryField.toPoly r60Val
  exact verify_square_step (rPrev := r59Val) (q := q60Val)
    (rNext := r60Val) (by rfl)

/-- Certificate step 61: square and reduce modulo the GF64 polynomial. -/
lemma step_61 :
    r60 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q61Val) *
        definingPolynomial + r61 := by
  change (BinaryField.toPoly r60Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q61Val) *
      definingPolynomial + BinaryField.toPoly r61Val
  exact verify_square_step (rPrev := r60Val) (q := q61Val)
    (rNext := r61Val) (by rfl)

/-- Certificate step 62: square and reduce modulo the GF64 polynomial. -/
lemma step_62 :
    r61 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q62Val) *
        definingPolynomial + r62 := by
  change (BinaryField.toPoly r61Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q62Val) *
      definingPolynomial + BinaryField.toPoly r62Val
  exact verify_square_step (rPrev := r61Val) (q := q62Val)
    (rNext := r62Val) (by rfl)

/-- Certificate step 63: square and reduce modulo the GF64 polynomial. -/
lemma step_63 :
    r62 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q63Val) *
        definingPolynomial + r63 := by
  change (BinaryField.toPoly r62Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q63Val) *
      definingPolynomial + BinaryField.toPoly r63Val
  exact verify_square_step (rPrev := r62Val) (q := q63Val)
    (rNext := r63Val) (by rfl)

/-- Certificate step 64: square and reduce modulo the GF64 polynomial. -/
lemma step_64 :
    r63 ^ 2 =
      BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q64Val) *
        definingPolynomial + r64 := by
  change (BinaryField.toPoly r63Val) ^ 2 =
    BinaryField.toPoly (BitVec.zeroExtend (2 * extensionDegree) q64Val) *
      definingPolynomial + BinaryField.toPoly r64Val
  exact verify_square_step (rPrev := r63Val) (q := q64Val)
    (rNext := r64Val) (by rfl)


/-- The degree-one polynomial `X` is already reduced modulo the GF64 polynomial. -/
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

lemma X_pow_2_pow_33_mod_eq :
    X ^ (2 ^ 33) % definingPolynomial = r33 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 32) X_pow_2_pow_32_mod_eq step_33

lemma X_pow_2_pow_34_mod_eq :
    X ^ (2 ^ 34) % definingPolynomial = r34 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 33) X_pow_2_pow_33_mod_eq step_34

lemma X_pow_2_pow_35_mod_eq :
    X ^ (2 ^ 35) % definingPolynomial = r35 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 34) X_pow_2_pow_34_mod_eq step_35

lemma X_pow_2_pow_36_mod_eq :
    X ^ (2 ^ 36) % definingPolynomial = r36 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 35) X_pow_2_pow_35_mod_eq step_36

lemma X_pow_2_pow_37_mod_eq :
    X ^ (2 ^ 37) % definingPolynomial = r37 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 36) X_pow_2_pow_36_mod_eq step_37

lemma X_pow_2_pow_38_mod_eq :
    X ^ (2 ^ 38) % definingPolynomial = r38 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 37) X_pow_2_pow_37_mod_eq step_38

lemma X_pow_2_pow_39_mod_eq :
    X ^ (2 ^ 39) % definingPolynomial = r39 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 38) X_pow_2_pow_38_mod_eq step_39

lemma X_pow_2_pow_40_mod_eq :
    X ^ (2 ^ 40) % definingPolynomial = r40 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 39) X_pow_2_pow_39_mod_eq step_40

lemma X_pow_2_pow_41_mod_eq :
    X ^ (2 ^ 41) % definingPolynomial = r41 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 40) X_pow_2_pow_40_mod_eq step_41

lemma X_pow_2_pow_42_mod_eq :
    X ^ (2 ^ 42) % definingPolynomial = r42 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 41) X_pow_2_pow_41_mod_eq step_42

lemma X_pow_2_pow_43_mod_eq :
    X ^ (2 ^ 43) % definingPolynomial = r43 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 42) X_pow_2_pow_42_mod_eq step_43

lemma X_pow_2_pow_44_mod_eq :
    X ^ (2 ^ 44) % definingPolynomial = r44 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 43) X_pow_2_pow_43_mod_eq step_44

lemma X_pow_2_pow_45_mod_eq :
    X ^ (2 ^ 45) % definingPolynomial = r45 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 44) X_pow_2_pow_44_mod_eq step_45

lemma X_pow_2_pow_46_mod_eq :
    X ^ (2 ^ 46) % definingPolynomial = r46 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 45) X_pow_2_pow_45_mod_eq step_46

lemma X_pow_2_pow_47_mod_eq :
    X ^ (2 ^ 47) % definingPolynomial = r47 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 46) X_pow_2_pow_46_mod_eq step_47

lemma X_pow_2_pow_48_mod_eq :
    X ^ (2 ^ 48) % definingPolynomial = r48 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 47) X_pow_2_pow_47_mod_eq step_48

lemma X_pow_2_pow_49_mod_eq :
    X ^ (2 ^ 49) % definingPolynomial = r49 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 48) X_pow_2_pow_48_mod_eq step_49

lemma X_pow_2_pow_50_mod_eq :
    X ^ (2 ^ 50) % definingPolynomial = r50 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 49) X_pow_2_pow_49_mod_eq step_50

lemma X_pow_2_pow_51_mod_eq :
    X ^ (2 ^ 51) % definingPolynomial = r51 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 50) X_pow_2_pow_50_mod_eq step_51

lemma X_pow_2_pow_52_mod_eq :
    X ^ (2 ^ 52) % definingPolynomial = r52 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 51) X_pow_2_pow_51_mod_eq step_52

lemma X_pow_2_pow_53_mod_eq :
    X ^ (2 ^ 53) % definingPolynomial = r53 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 52) X_pow_2_pow_52_mod_eq step_53

lemma X_pow_2_pow_54_mod_eq :
    X ^ (2 ^ 54) % definingPolynomial = r54 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 53) X_pow_2_pow_53_mod_eq step_54

lemma X_pow_2_pow_55_mod_eq :
    X ^ (2 ^ 55) % definingPolynomial = r55 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 54) X_pow_2_pow_54_mod_eq step_55

lemma X_pow_2_pow_56_mod_eq :
    X ^ (2 ^ 56) % definingPolynomial = r56 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 55) X_pow_2_pow_55_mod_eq step_56

lemma X_pow_2_pow_57_mod_eq :
    X ^ (2 ^ 57) % definingPolynomial = r57 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 56) X_pow_2_pow_56_mod_eq step_57

lemma X_pow_2_pow_58_mod_eq :
    X ^ (2 ^ 58) % definingPolynomial = r58 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 57) X_pow_2_pow_57_mod_eq step_58

lemma X_pow_2_pow_59_mod_eq :
    X ^ (2 ^ 59) % definingPolynomial = r59 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 58) X_pow_2_pow_58_mod_eq step_59

lemma X_pow_2_pow_60_mod_eq :
    X ^ (2 ^ 60) % definingPolynomial = r60 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 59) X_pow_2_pow_59_mod_eq step_60

lemma X_pow_2_pow_61_mod_eq :
    X ^ (2 ^ 61) % definingPolynomial = r61 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 60) X_pow_2_pow_60_mod_eq step_61

lemma X_pow_2_pow_62_mod_eq :
    X ^ (2 ^ 62) % definingPolynomial = r62 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 61) X_pow_2_pow_61_mod_eq step_62

lemma X_pow_2_pow_63_mod_eq :
    X ^ (2 ^ 63) % definingPolynomial = r63 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 62) X_pow_2_pow_62_mod_eq step_63

lemma X_pow_2_pow_64_mod_eq :
    X ^ (2 ^ 64) % definingPolynomial = r64 % definingPolynomial := by
  exact BinaryField.Extension.chain_step
    (P := definingPolynomial) definingPolynomial_ne_zero
    (k := 63) X_pow_2_pow_63_mod_eq step_64

/-- Rabin trace-condition remainder for the GF64 candidate polynomial. -/
lemma X_pow_2_pow_64_add_X_mod_eq_zero :
    (X ^ (2 ^ 64) + X) % definingPolynomial = 0 := by
  rw [CanonicalEuclideanDomain.add_mod_eq (hn := definingPolynomial_ne_zero)]
  rw [X_pow_2_pow_64_mod_eq, r64_eq_X, X_mod_definingPolynomial]
  simp only [CharTwo.add_self_eq_zero, EuclideanDomain.zero_mod]

/-- Rabin trace divisibility condition for the GF64 candidate polynomial. -/
lemma X_pow_2_pow_64_add_X_dvd :
    definingPolynomial ∣ X ^ (2 ^ 64) + X := by
  rw [← EuclideanDomain.mod_eq_zero]
  exact X_pow_2_pow_64_add_X_mod_eq_zero

end GF2_64
