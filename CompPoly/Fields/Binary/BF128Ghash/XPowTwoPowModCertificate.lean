/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.BF128Ghash.Prelude

namespace BF128Ghash
open Polynomial

set_option maxRecDepth 1500

def r0Val : B128 := X_val
noncomputable def r0 := X_ZMod2Poly
def q1Val : B128 := BitVec.ofNat 128 0
def r1Val : B128 := BitVec.ofNat 128 4
noncomputable def r1 := toPoly r1Val
lemma step_1 : r0^2 = (toPoly (to256 q1Val)) * ghashPoly + r1 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r0Val q1Val r1Val; rfl -- Kernel check

def q2Val : B128 := BitVec.ofNat 128 0
def r2Val : B128 := BitVec.ofNat 128 16
noncomputable def r2 := toPoly r2Val
lemma step_2 : r1^2 = (toPoly (to256 q2Val)) * ghashPoly + r2 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r1Val q2Val r2Val; rfl -- Kernel check

def q3Val : B128 := BitVec.ofNat 128 0
def r3Val : B128 := BitVec.ofNat 128 256
noncomputable def r3 := toPoly r3Val
lemma step_3 : r2^2 = (toPoly (to256 q3Val)) * ghashPoly + r3 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r2Val q3Val r3Val; rfl -- Kernel check

def q4Val : B128 := BitVec.ofNat 128 0
def r4Val : B128 := BitVec.ofNat 128 65536
noncomputable def r4 := toPoly r4Val
lemma step_4 : r3^2 = (toPoly (to256 q4Val)) * ghashPoly + r4 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r3Val q4Val r4Val; rfl -- Kernel check

def q5Val : B128 := BitVec.ofNat 128 0
def r5Val : B128 := BitVec.ofNat 128 4294967296
noncomputable def r5 := toPoly r5Val
lemma step_5 : r4^2 = (toPoly (to256 q5Val)) * ghashPoly + r5 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r4Val q5Val r5Val; rfl -- Kernel check

def q6Val : B128 := BitVec.ofNat 128 0
def r6Val : B128 := BitVec.ofNat 128 18446744073709551616
noncomputable def r6 := toPoly r6Val
lemma step_6 : r5^2 = (toPoly (to256 q6Val)) * ghashPoly + r6 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r5Val q6Val r6Val; rfl -- Kernel check

def q7Val : B128 := BitVec.ofNat 128 1
def r7Val : B128 := BitVec.ofNat 128 135
noncomputable def r7 := toPoly r7Val
lemma step_7 : r6^2 = (toPoly (to256 q7Val)) * ghashPoly + r7 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r6Val q7Val r7Val; rfl -- Kernel check

def q8Val : B128 := BitVec.ofNat 128 0
def r8Val : B128 := BitVec.ofNat 128 16405
noncomputable def r8 := toPoly r8Val
lemma step_8 : r7^2 = (toPoly (to256 q8Val)) * ghashPoly + r8 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r7Val q8Val r8Val; rfl -- Kernel check

def q9Val : B128 := BitVec.ofNat 128 0
def r9Val : B128 := BitVec.ofNat 128 268435729
noncomputable def r9 := toPoly r9Val
lemma step_9 : r8^2 = (toPoly (to256 q9Val)) * ghashPoly + r9 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r8Val q9Val r9Val; rfl -- Kernel check

def q10Val : B128 := BitVec.ofNat 128 0
def r10Val : B128 := BitVec.ofNat 128 72057594037993729
noncomputable def r10 := toPoly r10Val
lemma step_10 : r9^2 = (toPoly (to256 q10Val)) * ghashPoly + r10 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r9Val q10Val r10Val; rfl -- Kernel check

def q11Val : B128 := BitVec.ofNat 128 0
def r11Val : B128 := BitVec.ofNat 128 5192296858534827628530500624252929
noncomputable def r11 := toPoly r11Val
lemma step_11 : r10^2 = (toPoly (to256 q11Val)) * ghashPoly + r11 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r10Val q11Val r11Val; rfl -- Kernel check

def q12Val : B128 := BitVec.ofNat 128 79228162514264337593543950336
def r12Val : B128 := BitVec.ofNat 128 10695801939444132319206437814273
noncomputable def r12 := toPoly r12Val
lemma step_12 : r11^2 = (toPoly (to256 q12Val)) * ghashPoly + r12 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r11Val q12Val r12Val; rfl -- Kernel check

def q13Val : B128 := BitVec.ofNat 128 302618836529205194260481
def r13Val : B128 := BitVec.ofNat 128 40852786614935679133548678
noncomputable def r13 := toPoly r13Val
lemma step_13 : r12^2 = (toPoly (to256 q13Val)) * ghashPoly + r13 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r12Val q13Val r13Val; rfl -- Kernel check

def q14Val : B128 := BitVec.ofNat 128 4403688133700
def r14Val : B128 := BitVec.ofNat 128 594486085799880
noncomputable def r14 := toPoly r14Val
lemma step_14 : r13^2 = (toPoly (to256 q14Val)) * ghashPoly + r14 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r13Val q14Val r14Val; rfl -- Kernel check

def q15Val : B128 := BitVec.ofNat 128 0
def r15Val : B128 := BitVec.ofNat 128 317319171807580447641733255232
noncomputable def r15 := toPoly r15Val
lemma step_15 : r14^2 = (toPoly (to256 q15Val)) * ghashPoly + r15 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r14Val q15Val r15Val; rfl -- Kernel check

def q16Val : B128 := BitVec.ofNat 128 295148205346296697104
def r16Val : B128 := BitVec.ofNat 128 21272841581577792734377501409119104880
noncomputable def r16 := toPoly r16Val
lemma step_16 : r15^2 = (toPoly (to256 q16Val)) * ghashPoly + r16 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r15Val q16Val r16Val; rfl -- Kernel check

def q17Val : B128 := BitVec.ofNat 128 1329228075013083128053711770004558849
def r17Val : B128 := BitVec.ofNat 128 178123058470187579300754373079857658247
noncomputable def r17 := toPoly r17Val
lemma step_17 : r16^2 = (toPoly (to256 q17Val)) * ghashPoly + r17 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r16Val q17Val r17Val; rfl -- Kernel check

def q18Val : B128 := BitVec.ofNat 128 85174437751585617676521693081345740853
def r18Val : B128 := BitVec.ofNat 128 185309517472602589216710143146226674206
noncomputable def r18 := toPoly r18Val
lemma step_18 : r17^2 = (toPoly (to256 q18Val)) * ghashPoly + r18 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r17Val q18Val r18Val; rfl -- Kernel check

def q19Val : B128 := BitVec.ofNat 128 85429271016757708826772846602701832224
def r19Val : B128 := BitVec.ofNat 128 243359572833697916948025442825716044212
noncomputable def r19 := toPoly r19Val
lemma step_19 : r18^2 = (toPoly (to256 q19Val)) * ghashPoly + r19 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r18Val q19Val r19Val; rfl -- Kernel check

def q20Val : B128 := BitVec.ofNat 128 91825791577816695462331943916582015331
def r20Val : B128 := BitVec.ofNat 128 2242402909557391341593841539292758713
noncomputable def r20 := toPoly r20Val
lemma step_20 : r19^2 = (toPoly (to256 q20Val)) * ghashPoly + r20 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r19Val q20Val r20Val; rfl -- Kernel check

def q21Val : B128 := BitVec.ofNat 128 6578260275635393025015507911528788
def r21Val : B128 := BitVec.ofNat 128 23534795660742517158384838884479883757
noncomputable def r21 := toPoly r21Val
lemma step_21 : r20^2 = (toPoly (to256 q21Val)) * ghashPoly + r21 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r20Val q21Val r21Val; rfl -- Kernel check

def q22Val : B128 := BitVec.ofNat 128 1335821067607728284447314588529135620
def r22Val : B128 := BitVec.ofNat 128 174985988737277424980776175160916846157
noncomputable def r22 := toPoly r22Val
lemma step_22 : r21^2 = (toPoly (to256 q22Val)) * ghashPoly + r22 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r21Val q22Val r22Val; rfl -- Kernel check

def q23Val : B128 := BitVec.ofNat 128 85097933765574711371307601252685529380
def r23Val : B128 := BitVec.ofNat 128 175030095290142335996286672108454299053
noncomputable def r23 := toPoly r23Val
lemma step_23 : r22^2 = (toPoly (to256 q23Val)) * ghashPoly + r23 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r22Val q23Val r23Val; rfl -- Kernel check

def q24Val : B128 := BitVec.ofNat 128 85097938855979638311968046394211651956
def r24Val : B128 := BitVec.ofNat 128 265807388946362947165055761130818848797
noncomputable def r24 := toPoly r24Val
lemma step_24 : r23^2 = (toPoly (to256 q24Val)) * ghashPoly + r24 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r23Val q24Val r24Val; rfl -- Kernel check

def q25Val : B128 := BitVec.ofNat 128 106449006993305541109351437619337171064
def r25Val : B128 := BitVec.ofNat 128 249252559114209554249604311851685858361
noncomputable def r25 := toPoly r25Val
lemma step_25 : r24^2 = (toPoly (to256 q25Val)) * ghashPoly + r25 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r24Val q25Val r25Val; rfl -- Kernel check

def q26Val : B128 := BitVec.ofNat 128 92076299539298910085337233284453712951
def r26Val : B128 := BitVec.ofNat 128 58796763164556581763983006251523293764
noncomputable def r26 := toPoly r26Val
lemma step_26 : r25^2 = (toPoly (to256 q26Val)) * ghashPoly + r26 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r25Val q26Val r26Val; rfl -- Kernel check

def q27Val : B128 := BitVec.ofNat 128 5732402635759363598497704284982935635
def r27Val : B128 := BitVec.ofNat 128 49134626841591323031921206452464859177
noncomputable def r27 := toPoly r27Val
lemma step_27 : r26^2 = (toPoly (to256 q27Val)) * ghashPoly + r27 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r26Val q27Val r27Val; rfl -- Kernel check

def q28Val : B128 := BitVec.ofNat 128 5401714348658740294254131118417904902
def r28Val : B128 := BitVec.ofNat 128 27987540068191889485421864406071811155
noncomputable def r28 := toPoly r28Val
lemma step_28 : r27^2 = (toPoly (to256 q28Val)) * ghashPoly + r28 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r27Val q28Val r28Val; rfl -- Kernel check

def q29Val : B128 := BitVec.ofNat 128 1417503699112502653188969622685433860
def r29Val : B128 := BitVec.ofNat 128 271029757364165806137532465049589437209
noncomputable def r29 := toPoly r29Val
lemma step_29 : r28^2 = (toPoly (to256 q29Val)) * ghashPoly + r29 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r28Val q29Val r29Val; rfl -- Kernel check

def q30Val : B128 := BitVec.ofNat 128 106698213459293707051433245069331939437
def r30Val : B128 := BitVec.ofNat 128 280724925951004403811542151209009346242
noncomputable def r30 := toPoly r30Val
lemma step_30 : r29^2 = (toPoly (to256 q30Val)) * ghashPoly + r30 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r29Val q30Val r30Val; rfl -- Kernel check

def q31Val : B128 := BitVec.ofNat 128 107693530655217507989114849941793018940
def r31Val : B128 := BitVec.ofNat 128 128752713728467045721822022561693573808
noncomputable def r31 := toPoly r31Val
lemma step_31 : r30^2 = (toPoly (to256 q31Val)) * ghashPoly + r31 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r30Val q31Val r31Val; rfl -- Kernel check

def q32Val : B128 := BitVec.ofNat 128 26586209154299446928674418544604102926
def r32Val : B128 := BitVec.ofNat 128 159741227827866894033846763158209103146
noncomputable def r32 := toPoly r32Val
lemma step_32 : r31^2 = (toPoly (to256 q32Val)) * ghashPoly + r32 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r31Val q32Val r32Val; rfl -- Kernel check

def q33Val : B128 := BitVec.ofNat 128 28246182457631555671140354653794861386
def r33Val : B128 := BitVec.ofNat 128 274834116766907886484561602157405644722
noncomputable def r33 := toPoly r33Val
lemma step_33 : r32^2 = (toPoly (to256 q33Val)) * ghashPoly + r33 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r32Val q33Val r33Val; rfl -- Kernel check

def q34Val : B128 := BitVec.ofNat 128 106776015589057259060961011925506130044
def r34Val : B128 := BitVec.ofNat 128 269592872973127703478481607229849893488
noncomputable def r34 := toPoly r34Val
lemma step_34 : r33^2 = (toPoly (to256 q34Val)) * ghashPoly + r34 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r33Val q34Val r34Val; rfl -- Kernel check

def q35Val : B128 := BitVec.ofNat 128 106692958824939381797454263554624721276
def r35Val : B128 := BitVec.ofNat 128 281740353144251213267627901976484830580
noncomputable def r35 := toPoly r35Val
lemma step_35 : r34^2 = (toPoly (to256 q35Val)) * ghashPoly + r35 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r34Val q35Val r35Val; rfl -- Kernel check

def q36Val : B128 := BitVec.ofNat 128 107695154496139142149109455169944552508
def r36Val : B128 := BitVec.ofNat 128 43449847600466687806806694967245739940
noncomputable def r36 := toPoly r36Val
lemma step_36 : r35^2 = (toPoly (to256 q36Val)) * ghashPoly + r36 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r35Val q36Val r36Val; rfl -- Kernel check

def q37Val : B128 := BitVec.ofNat 128 5318311470645487902434602580876197954
def r37Val : B128 := BitVec.ofNat 128 37727843099595198433684011782007776478
noncomputable def r37 := toPoly r37Val
lemma step_37 : r36^2 = (toPoly (to256 q37Val)) * ghashPoly + r37 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r36Val q37Val r37Val; rfl -- Kernel check

def q38Val : B128 := BitVec.ofNat 128 1745017709983535898810543976869807188
def r38Val : B128 := BitVec.ofNat 128 311928417185453978908537250809886516984
noncomputable def r38 := toPoly r38Val
lemma step_38 : r37^2 = (toPoly (to256 q38Val)) * ghashPoly + r38 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r37Val q38Val r38Val; rfl -- Kernel check

def q39Val : B128 := BitVec.ofNat 128 112009612504539276871140401964429693999
def r39Val : B128 := BitVec.ofNat 128 297740222968517774644413722072226000397
noncomputable def r39 := toPoly r39Val
lemma step_39 : r38^2 = (toPoly (to256 q39Val)) * ghashPoly + r39 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r38Val q39Val r39Val; rfl -- Kernel check

def q40Val : B128 := BitVec.ofNat 128 108110543572682219842640169583646098477
def r40Val : B128 := BitVec.ofNat 128 32339339626698503367513300576590613010
noncomputable def r40 := toPoly r40Val
lemma step_40 : r39^2 = (toPoly (to256 q40Val)) * ghashPoly + r40 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r39Val q40Val r40Val; rfl -- Kernel check

def q41Val : B128 := BitVec.ofNat 128 1661881068625898637091009420418367572
def r41Val : B128 := BitVec.ofNat 128 223132434853550809815195064548738067112
noncomputable def r41 := toPoly r41Val
lemma step_41 : r40^2 = (toPoly (to256 q41Val)) * ghashPoly + r41 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r40Val q41Val r41Val; rfl -- Kernel check

def q42Val : B128 := BitVec.ofNat 128 90498191261518681257739264897661080691
def r42Val : B128 := BitVec.ofNat 128 265523960741914972480486897956328640665
noncomputable def r42 := toPoly r42Val
lemma step_42 : r41^2 = (toPoly (to256 q42Val)) * ghashPoly + r42 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r41Val q42Val r42Val; rfl -- Kernel check

def q43Val : B128 := BitVec.ofNat 128 106448900806604993173560670687746606380
def r43Val : B128 := BitVec.ofNat 128 317476001073086156486538380654899563653
noncomputable def r43 := toPoly r43Val
lemma step_43 : r42^2 = (toPoly (to256 q43Val)) * ghashPoly + r43 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r42Val q43Val r43Val; rfl -- Kernel check

def q44Val : B128 := BitVec.ofNat 128 112092949142089617020436155326729814143
def r44Val : B128 := BitVec.ofNat 128 281134273668648985900959546328737677036
noncomputable def r44 := toPoly r44Val
lemma step_44 : r43^2 = (toPoly (to256 q44Val)) * ghashPoly + r44 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r43Val q44Val r44Val; rfl -- Kernel check

def q45Val : B128 := BitVec.ofNat 128 107694727223682985464461035033154818152
def r45Val : B128 := BitVec.ofNat 128 134228771238834113055021444037992255816
noncomputable def r45 := toPoly r45Val
lemma step_45 : r44^2 = (toPoly (to256 q45Val)) * ghashPoly + r45 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r44Val q45Val r45Val; rfl -- Kernel check

def q46Val : B128 := BitVec.ofNat 128 26669366156822072797831484246999700558
def r46Val : B128 := BitVec.ofNat 128 150254873993691350120483903676558564010
noncomputable def r46 := toPoly r46Val
lemma step_46 : r45^2 = (toPoly (to256 q46Val)) * ghashPoly + r46 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r45Val q46Val r46Val; rfl -- Kernel check

def q47Val : B128 := BitVec.ofNat 128 27918985595935424472919418209090736158
def r47Val : B128 := BitVec.ofNat 128 233624311168361768088952357930788403998
noncomputable def r47 := toPoly r47Val
lemma step_47 : r46^2 = (toPoly (to256 q47Val)) * ghashPoly + r47 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r46Val q47Val r47Val; rfl -- Kernel check

def q48Val : B128 := BitVec.ofNat 128 90830471862246153247450751397716381795
def r48Val : B128 := BitVec.ofNat 128 301852678830317075984151617556076790269
noncomputable def r48 := toPoly r48Val
lemma step_48 : r47^2 = (toPoly (to256 q48Val)) * ghashPoly + r48 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r47Val q48Val r48Val; rfl -- Kernel check

def q49Val : B128 := BitVec.ofNat 128 111681135018577110704347238966514418027
def r49Val : B128 := BitVec.ofNat 128 334713874327018819147718792733305726656
noncomputable def r49 := toPoly r49Val
lemma step_49 : r48^2 = (toPoly (to256 q49Val)) * ghashPoly + r49 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r48Val q49Val r49Val; rfl -- Kernel check

def q50Val : B128 := BitVec.ofNat 128 113344277472022619116480485242451285306
def r50Val : B128 := BitVec.ofNat 128 102613057823079007323731014766805608102
noncomputable def r50 := toPoly r50Val
lemma step_50 : r49^2 = (toPoly (to256 q50Val)) * ghashPoly + r50 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r49Val q50Val r50Val; rfl -- Kernel check

def q51Val : B128 := BitVec.ofNat 128 21688325726969315257874800492319691801
def r51Val : B128 := BitVec.ofNat 128 102960897267461938273022342347012760795
noncomputable def r51 := toPoly r51Val
lemma step_51 : r50^2 = (toPoly (to256 q51Val)) * ghashPoly + r51 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r50Val q51Val r51Val; rfl -- Kernel check

def q52Val : B128 := BitVec.ofNat 128 21688651275484189220660633885066941725
def r52Val : B128 := BitVec.ofNat 128 12615472659389050585944223579430941846
noncomputable def r52 := toPoly r52Val
lemma step_52 : r51^2 = (toPoly (to256 q52Val)) * ghashPoly + r52 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r51Val q52Val r52Val; rfl -- Kernel check

def q53Val : B128 := BitVec.ofNat 128 337931664957145912131522070333887569
def r53Val : B128 := BitVec.ofNat 128 127982396443970808193093289421192168483
noncomputable def r53 := toPoly r53Val
lemma step_53 : r52^2 = (toPoly (to256 q53Val)) * ghashPoly + r53 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r52Val q53Val r53Val; rfl -- Kernel check

def q54Val : B128 := BitVec.ofNat 128 26584889524667542359832176840194131230
def r54Val : B128 := BitVec.ofNat 128 80211020574021611523259929375765860447
noncomputable def r54 := toPoly r54Val
lemma step_54 : r53^2 = (toPoly (to256 q54Val)) * ghashPoly + r54 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r53Val q54Val r54Val; rfl -- Kernel check

def q55Val : B128 := BitVec.ofNat 128 7061873599502177810890797532710258006
def r55Val : B128 := BitVec.ofNat 128 328306714951167239883061265636229931255
noncomputable def r55 := toPoly r55Val
lemma step_55 : r54^2 = (toPoly (to256 q55Val)) * ghashPoly + r55 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r54Val q55Val r55Val; rfl -- Kernel check

def q56Val : B128 := BitVec.ofNat 128 113089956021307759246001883954363240570
def r56Val : B128 := BitVec.ofNat 128 154202500596702199027624208412024772979
noncomputable def r56 := toPoly r56Val
lemma step_56 : r55^2 = (toPoly (to256 q56Val)) * ghashPoly + r56 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r55Val q56Val r56Val; rfl -- Kernel check

def q57Val : B128 := BitVec.ofNat 128 27996864983398597151662045814934552847
def r57Val : B128 := BitVec.ofNat 128 243851091912831247504069218024646202792
noncomputable def r57 := toPoly r57Val
lemma step_57 : r56^2 = (toPoly (to256 q57Val)) * ghashPoly + r57 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r56Val q57Val r57Val; rfl -- Kernel check

def q58Val : B128 := BitVec.ofNat 128 91826197141446752898753407217650974759
def r58Val : B128 := BitVec.ofNat 128 27440791048182847192756476088690644789
noncomputable def r58 := toPoly r58Val
lemma step_58 : r57^2 = (toPoly (to256 q58Val)) * ghashPoly + r58 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r57Val q58Val r58Val; rfl -- Kernel check

def q59Val : B128 := BitVec.ofNat 128 1413685243047349389981581478196429825
def r59Val : B128 := BitVec.ofNat 128 211387903213242387898935001709526309270
noncomputable def r59 := toPoly r59Val
lemma step_59 : r58^2 = (toPoly (to256 q59Val)) * ghashPoly + r59 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r58Val q59Val r59Val; rfl -- Kernel check

def q60Val : B128 := BitVec.ofNat 128 86841166647874110313667572945145627760
def r60Val : B128 := BitVec.ofNat 128 159829576190644668190096436593299055684
noncomputable def r60 := toPoly r60Val
lemma step_60 : r59^2 = (toPoly (to256 q60Val)) * ghashPoly + r60 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r59Val q60Val r60Val; rfl -- Kernel check

def q61Val : B128 := BitVec.ofNat 128 28246202977744983831384242042349896718
def r61Val : B128 := BitVec.ofNat 128 211134062703199012190249497033863383866
noncomputable def r61 := toPoly r61Val
lemma step_61 : r60^2 = (toPoly (to256 q61Val)) * ghashPoly + r61 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r60Val q61Val r61Val; rfl -- Kernel check

def q62Val : B128 := BitVec.ofNat 128 86837617148184232060666537332607095093
def r62Val : B128 := BitVec.ofNat 128 82185866721533220436512213066902333519
noncomputable def r62 := toPoly r62Val
lemma step_62 : r61^2 = (toPoly (to256 q62Val)) * ghashPoly + r62 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r61Val q62Val r62Val; rfl -- Kernel check

def q63Val : B128 := BitVec.ofNat 128 7068360173580815494096880910548145427
def r63Val : B128 := BitVec.ofNat 128 327395961906668187682165754937045283500
noncomputable def r63 := toPoly r63Val
lemma step_63 : r62^2 = (toPoly (to256 q63Val)) * ghashPoly + r63 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r62Val q63Val r63Val; rfl -- Kernel check

def q64Val : B128 := BitVec.ofNat 128 113088556753929231734156930669399326778
def r64Val : B128 := BitVec.ofNat 128 129460184901158119860735353079755610614
noncomputable def r64 := toPoly r64Val
lemma step_64 : r63^2 = (toPoly (to256 q64Val)) * ghashPoly + r64 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r63Val q64Val r64Val; rfl -- Kernel check

def q65Val : B128 := BitVec.ofNat 128 26590159208040329700719228969042593099
def r65Val : B128 := BitVec.ofNat 128 165640453935684170557382138895643060837
noncomputable def r65 := toPoly r65Val
lemma step_65 : r64^2 = (toPoly (to256 q65Val)) * ghashPoly + r65 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r64Val q65Val r65Val; rfl -- Kernel check

def q66Val : B128 := BitVec.ofNat 128 28330496435819242658153112454463574031
def r66Val : B128 := BitVec.ofNat 128 258895673196720778598706762360552858556
noncomputable def r66 := toPoly r66Val
lemma step_66 : r65^2 = (toPoly (to256 q66Val)) * ghashPoly + r66 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r65Val q66Val r66Val; rfl -- Kernel check

def q67Val : B128 := BitVec.ofNat 128 106360632796475222630177185573960421676
def r67Val : B128 := BitVec.ofNat 128 301930392259976828106625834641931740308
noncomputable def r67 := toPoly r67Val
lemma step_67 : r66^2 = (toPoly (to256 q67Val)) * ghashPoly + r67 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r66Val q67Val r67Val; rfl -- Kernel check

def q68Val : B128 := BitVec.ofNat 128 111681195627886010777831830863322830206
def r68Val : B128 := BitVec.ofNat 128 254590090333913220966971847449742103658
noncomputable def r68 := toPoly r68Val
lemma step_68 : r67^2 = (toPoly (to256 q68Val)) * ghashPoly + r68 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r67Val q68Val r68Val; rfl -- Kernel check

def q69Val : B128 := BitVec.ofNat 128 92159380091923100147260900319429678434
def r69Val : B128 := BitVec.ofNat 128 154605543219637426435106976091970670442
noncomputable def r69 := toPoly r69Val
lemma step_69 : r68^2 = (toPoly (to256 q69Val)) * ghashPoly + r69 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r68Val q69Val r69Val; rfl -- Kernel check

def q70Val : B128 := BitVec.ofNat 128 27997195940475076739387703229219689547
def r70Val : B128 := BitVec.ofNat 128 328554470600989978311552677909447941173
noncomputable def r70 := toPoly r70Val
lemma step_70 : r69^2 = (toPoly (to256 q70Val)) * ghashPoly + r70 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r69Val q70Val r70Val; rfl -- Kernel check

def q71Val : B128 := BitVec.ofNat 128 113093505427900630694337031647284712575
def r71Val : B128 := BitVec.ofNat 128 66427334083092228965437207507360258028
noncomputable def r71 := toPoly r71Val
lemma step_71 : r70^2 = (toPoly (to256 q71Val)) * ghashPoly + r71 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r70Val q71Val r71Val; rfl -- Kernel check

def q72Val : B128 := BitVec.ofNat 128 6653061436929269215650648925752610883
def r72Val : B128 := BitVec.ofNat 128 269818012861271281423176274446422361113
noncomputable def r72 := toPoly r72Val
lemma step_72 : r71^2 = (toPoly (to256 q72Val)) * ghashPoly + r72 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r71Val q72Val r72Val; rfl -- Kernel check

def q73Val : B128 := BitVec.ofNat 128 106693046271573877075738515171988297017
def r73Val : B128 := BitVec.ofNat 128 264132206416858785477441377236972222062
noncomputable def r73 := toPoly r73Val
lemma step_73 : r72^2 = (toPoly (to256 q73Val)) * ghashPoly + r73 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r72Val q73Val r73Val; rfl -- Kernel check

def q74Val : B128 := BitVec.ofNat 128 106443486670795937264113025222060609657
def r74Val : B128 := BitVec.ofNat 128 334025740161143946608295602721698306491
noncomputable def r74 := toPoly r74Val
lemma step_74 : r73^2 = (toPoly (to256 q74Val)) * ghashPoly + r74 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r73Val q74Val r74Val; rfl -- Kernel check

def q75Val : B128 := BitVec.ofNat 128 113342978110273067672708979424336364922
def r75Val : B128 := BitVec.ofNat 128 122383803109284106894334171034010591779
noncomputable def r75 := toPoly r75Val
lemma step_75 : r74^2 = (toPoly (to256 q75Val)) * ghashPoly + r75 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r74Val q75Val r75Val; rfl -- Kernel check

def q76Val : B128 := BitVec.ofNat 128 23012280281306496098841036354677392648
def r76Val : B128 := BitVec.ofNat 128 296025850348968698648586558724418263869
noncomputable def r76 := toPoly r76Val
lemma step_76 : r75^2 = (toPoly (to256 q76Val)) * ghashPoly + r76 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r75Val q76Val r76Val; rfl -- Kernel check

def q77Val : B128 := BitVec.ofNat 128 108105021368416688828337788080635253053
def r77Val : B128 := BitVec.ofNat 128 37960944824515205685591230648204258402
noncomputable def r77 := toPoly r77Val
lemma step_77 : r76^2 = (toPoly (to256 q77Val)) * ghashPoly + r77 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r76Val q77Val r77Val; rfl -- Kernel check

def q78Val : B128 := BitVec.ofNat 128 1745916553082199154939513287878906948
def r78Val : B128 := BitVec.ofNat 128 226742293150914418175831072849372273624
noncomputable def r78 := toPoly r78Val
lemma step_78 : r77^2 = (toPoly (to256 q78Val)) * ghashPoly + r78 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r77Val q78Val r78Val; rfl -- Kernel check

def q79Val : B128 := BitVec.ofNat 128 90741899550417938157404566366188802402
def r79Val : B128 := BitVec.ofNat 128 248467511393027050396179622604745119342
noncomputable def r79 := toPoly r79Val
lemma step_79 : r78^2 = (toPoly (to256 q79Val)) * ghashPoly + r79 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r78Val q79Val r79Val; rfl -- Kernel check

def q80Val : B128 := BitVec.ofNat 128 92071518035819132161895892174899593314
def r80Val : B128 := BitVec.ofNat 128 161687256048543766767383987762312963194
noncomputable def r80 := toPoly r80Val
lemma step_80 : r79^2 = (toPoly (to256 q80Val)) * ghashPoly + r80 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r79Val q80Val r80Val; rfl -- Kernel check

def q81Val : B128 := BitVec.ofNat 128 28252666832370719236803303807264036127
def r81Val : B128 := BitVec.ofNat 128 269110802679140966820977389101215773081
noncomputable def r81 := toPoly r81Val
lemma step_81 : r80^2 = (toPoly (to256 q81Val)) * ghashPoly + r81 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r80Val q81Val r81Val; rfl -- Kernel check

def q82Val : B128 := BitVec.ofNat 128 106691743072576809547238840914556290412
def r82Val : B128 := BitVec.ofNat 128 195167772352272279581770856328715365701
noncomputable def r82 := toPoly r82Val
lemma step_82 : r81^2 = (toPoly (to256 q82Val)) * ghashPoly + r82 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r81Val q82Val r82Val; rfl -- Kernel check

def q83Val : B128 := BitVec.ofNat 128 86422232211083446865462163070649439524
def r83Val : B128 := BitVec.ofNat 128 6839019468748781921035578916625770989
noncomputable def r83 := toPoly r83Val
lemma step_83 : r82^2 = (toPoly (to256 q83Val)) * ghashPoly + r83 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r82Val q83Val r83Val; rfl -- Kernel check

def q84Val : B128 := BitVec.ofNat 128 88351524371087060277032187079229461
def r84Val : B128 := BitVec.ofNat 128 119133456490525504919656485393064943290
noncomputable def r84 := toPoly r84Val
lemma step_84 : r83^2 = (toPoly (to256 q84Val)) * ghashPoly + r84 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r83Val q84Val r84Val; rfl -- Kernel check

def q85Val : B128 := BitVec.ofNat 128 22935754432972881912600091642172883273
def r85Val : B128 := BitVec.ofNat 128 284976786280009736580048287615377352507
noncomputable def r85 := toPoly r85Val
lemma step_85 : r84^2 = (toPoly (to256 q85Val)) * ghashPoly + r85 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r84Val q85Val r85Val; rfl -- Kernel check

def q86Val : B128 := BitVec.ofNat 128 107771720531476048881238081762006946940
def r86Val : B128 := BitVec.ofNat 128 53368461820224018424322992725600146993
noncomputable def r86 := toPoly r86Val
lemma step_86 : r85^2 = (toPoly (to256 q86Val)) * ghashPoly + r86 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r85Val q86Val r86Val; rfl -- Kernel check

def q87Val : B128 := BitVec.ofNat 128 5649301702496680664927320601070403923
def r87Val : B128 := BitVec.ofNat 128 165521487478005576843608560748526611000
noncomputable def r87 := toPoly r87Val
lemma step_87 : r86^2 = (toPoly (to256 q87Val)) * ghashPoly + r87 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r86Val q87Val r87Val; rfl -- Kernel check

def q88Val : B128 := BitVec.ofNat 128 28330471323921145967809237462456554778
def r88Val : B128 := BitVec.ofNat 128 195068410978310211650239904624548258566
noncomputable def r88 := toPoly r88Val
lemma step_88 : r87^2 = (toPoly (to256 q88Val)) * ghashPoly + r88 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r87Val q88Val r88Val; rfl -- Kernel check

def q89Val : B128 := BitVec.ofNat 128 86422211531083546570630185816972149872
def r89Val : B128 := BitVec.ofNat 128 113589941149803520359128394698002916676
noncomputable def r89 := toPoly r89Val
lemma step_89 : r88^2 = (toPoly (to256 q89Val)) * ghashPoly + r89 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r88Val q89Val r89Val; rfl -- Kernel check

def q90Val : B128 := BitVec.ofNat 128 22685572194236020141428944940093998365
def r90Val : B128 := BitVec.ofNat 128 249467295398400182484435455780551427523
noncomputable def r90 := toPoly r90Val
lemma step_90 : r89^2 = (toPoly (to256 q90Val)) * ghashPoly + r90 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r89Val q90Val r90Val; rfl -- Kernel check

def q91Val : B128 := BitVec.ofNat 128 92076385834802754365670188026180227442
def r91Val : B128 := BitVec.ofNat 128 75006380269635190750556711265086168923
noncomputable def r91 := toPoly r91Val
lemma step_91 : r90^2 = (toPoly (to256 q91Val)) * ghashPoly + r91 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r90Val q91Val r91Val; rfl -- Kernel check

def q92Val : B128 := BitVec.ofNat 128 6978859064917858239407404423466729542
def r92Val : B128 := BitVec.ofNat 128 318824008587287836741888684444380361623
noncomputable def r92 := toPoly r92Val
lemma step_92 : r91^2 = (toPoly (to256 q92Val)) * ghashPoly + r92 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r91Val q92Val r92Val; rfl -- Kernel check

def q93Val : B128 := BitVec.ofNat 128 112098145225801890397053623176863679546
def r93Val : B128 := BitVec.ofNat 128 178459331004814995506250383468567150771
noncomputable def r93 := toPoly r93Val
lemma step_93 : r92^2 = (toPoly (to256 q93Val)) * ghashPoly + r93 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r92Val q93Val r93Val; rfl -- Kernel check

def q94Val : B128 := BitVec.ofNat 128 85174762502891044365941082238663790704
def r94Val : B128 := BitVec.ofNat 128 211872363948266361377324272839095225429
noncomputable def r94 := toPoly r94Val
lemma step_94 : r93^2 = (toPoly (to256 q94Val)) * ghashPoly + r94 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r93Val q94Val r94Val; rfl -- Kernel check

def q95Val : B128 := BitVec.ofNat 128 86841571955308605099847419267740865588
def r95Val : B128 := BitVec.ofNat 128 143811789042420870636385239690585466781
noncomputable def r95 := toPoly r95Val
lemma step_95 : r94^2 = (toPoly (to256 q95Val)) * ghashPoly + r95 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r94Val q95Val r95Val; rfl -- Kernel check

def q96Val : B128 := BitVec.ofNat 128 27000045156914888433990455064947393806
def r96Val : B128 := BitVec.ofNat 128 86248589110002907259851524152594849147
noncomputable def r96 := toPoly r96Val
lemma step_96 : r95^2 = (toPoly (to256 q96Val)) * ghashPoly + r96 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r95Val q96Val r96Val; rfl -- Kernel check

def q97Val : B128 := BitVec.ofNat 128 21269351997049433062953149265858285644
def r97Val : B128 := BitVec.ofNat 128 44507931730853748353717482469352571553
noncomputable def r97 := toPoly r97Val
lemma step_97 : r96^2 = (toPoly (to256 q97Val)) * ghashPoly + r97 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r96Val q97Val r97Val; rfl -- Kernel check

def q98Val : B128 := BitVec.ofNat 128 5322535703422135752597822652532412743
def r98Val : B128 := BitVec.ofNat 128 32963873827986936976259691565938463060
noncomputable def r98 := toPoly r98Val
lemma step_98 : r97^2 = (toPoly (to256 q98Val)) * ghashPoly + r98 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r97Val q98Val r98Val; rfl -- Kernel check

def q99Val : B128 := BitVec.ofNat 128 1663163945965777307793753184466715668
def r99Val : B128 := BitVec.ofNat 128 216630587467047648990556766097492264828
noncomputable def r99 := toPoly r99Val
lemma step_99 : r98^2 = (toPoly (to256 q99Val)) * ghashPoly + r99 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r98Val q99Val r99Val; rfl -- Kernel check

def q100Val : B128 := BitVec.ofNat 128 90410002075340011635962445654417232183
def r100Val : B128 := BitVec.ofNat 128 185272067944601170075289186680278366549
noncomputable def r100 := toPoly r100Val
lemma step_100 : r99^2 = (toPoly (to256 q100Val)) * ghashPoly + r100 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r99Val q100Val r100Val; rfl -- Kernel check

def q101Val : B128 := BitVec.ofNat 128 85429266178969957737271708988624688160
def r101Val : B128 := BitVec.ofNat 128 220985417642294560069226125886699449841
noncomputable def r101 := toPoly r101Val
lemma step_101 : r100^2 = (toPoly (to256 q101Val)) * ghashPoly + r101 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r100Val q101Val r101Val; rfl -- Kernel check

def q102Val : B128 := BitVec.ofNat 128 90491674170747685916512986686148334707
def r102Val : B128 := BitVec.ofNat 128 264688778274977021302766754871988896216
noncomputable def r102 := toPoly r102Val
lemma step_102 : r101^2 = (toPoly (to256 q102Val)) * ghashPoly + r102 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r101Val q102Val r102Val; rfl -- Kernel check

def q103Val : B128 := BitVec.ofNat 128 106447359107255926573111061020838724904
def r103Val : B128 := BitVec.ofNat 128 333264177890741770072193430405525003928
noncomputable def r103 := toPoly r103Val
lemma step_103 : r102^2 = (toPoly (to256 q103Val)) * ghashPoly + r103 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r102Val q103Val r103Val; rfl -- Kernel check

def q104Val : B128 := BitVec.ofNat 128 113338860390302193732750644424425424250
def r104Val : B128 := BitVec.ofNat 128 33205950964766484238866480871644341798
noncomputable def r104 := toPoly r104Val
lemma step_104 : r103^2 = (toPoly (to256 q104Val)) * ghashPoly + r104 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r103Val q104Val r104Val; rfl -- Kernel check

def q105Val : B128 := BitVec.ofNat 128 1663264467921888622614922324832748865
def r105Val : B128 := BitVec.ofNat 128 301310530123703810140221288298382736979
noncomputable def r105 := toPoly r105Val
lemma step_105 : r104^2 = (toPoly (to256 q105Val)) * ghashPoly + r105 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r104Val q105Val r105Val; rfl -- Kernel check

def q106Val : B128 := BitVec.ofNat 128 111677306697434252276890411435311514938
def r106Val : B128 := BitVec.ofNat 128 254546671986439821273357947065150691235
noncomputable def r106 := toPoly r106Val
lemma step_106 : r105^2 = (toPoly (to256 q106Val)) * ghashPoly + r106 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r105Val q106Val r106Val; rfl -- Kernel check

def q107Val : B128 := BitVec.ofNat 128 92158509633152670942014662830365885751
def r107Val : B128 := BitVec.ofNat 128 154463474563896264286711223429656871936
noncomputable def r107 := toPoly r107Val
lemma step_107 : r106^2 = (toPoly (to256 q107Val)) * ghashPoly + r107 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r106Val q107Val r107Val; rfl -- Kernel check

def q108Val : B128 := BitVec.ofNat 128 27996967361055562314451527514068107615
def r108Val : B128 := BitVec.ofNat 128 238553731111275542579218303752720181533
noncomputable def r108 := toPoly r108Val
lemma step_108 : r107^2 = (toPoly (to256 q108Val)) * ghashPoly + r108 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r107Val q108Val r108Val; rfl -- Kernel check

def q109Val : B128 := BitVec.ofNat 128 91743120812629147377374904346117947762
def r109Val : B128 := BitVec.ofNat 128 18384089493480778990035902178609102351
noncomputable def r109 := toPoly r109Val
lemma step_109 : r108^2 = (toPoly (to256 q109Val)) * ghashPoly + r109 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r108Val q109Val r109Val; rfl -- Kernel check

def q110Val : B128 := BitVec.ofNat 128 422220209435656804352068862373532753
def r110Val : B128 := BitVec.ofNat 128 75820400037257621222803633372476097890
noncomputable def r110 := toPoly r110Val
lemma step_110 : r109^2 = (toPoly (to256 q110Val)) * ghashPoly + r110 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r109Val q110Val r110Val; rfl -- Kernel check

def q111Val : B128 := BitVec.ofNat 128 6983644668825866946112147987807354946
def r111Val : B128 := BitVec.ofNat 128 317696663419018730218660346852253168842
noncomputable def r111 := toPoly r111Val
lemma step_111 : r110^2 = (toPoly (to256 q111Val)) * ghashPoly + r111 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r110Val q111Val r111Val; rfl -- Kernel check

def q112Val : B128 := BitVec.ofNat 128 112096497197083545190001414019926261867
def r112Val : B128 := BitVec.ofNat 128 265151192445743918497476159262292403413
noncomputable def r112 := toPoly r112Val
lemma step_112 : r111^2 = (toPoly (to256 q112Val)) * ghashPoly + r112 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r111Val q112Val r112Val; rfl -- Kernel check

def q113Val : B128 := BitVec.ofNat 128 106447709219897039649066968929207930925
def r113Val : B128 := BitVec.ofNat 128 227243742383211985895879960446026839890
noncomputable def r113 := toPoly r113Val
lemma step_113 : r112^2 = (toPoly (to256 q113Val)) * ghashPoly + r113 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r112Val q113Val r113Val; rfl -- Kernel check

def q114Val : B128 := BitVec.ofNat 128 90742305271354986935977381436566077815
def r114Val : B128 := BitVec.ofNat 128 253422517028958359388508295558326299841
noncomputable def r114 := toPoly r114Val
lemma step_114 : r113^2 = (toPoly (to256 q114Val)) * ghashPoly + r114 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r113Val q114Val r114Val; rfl -- Kernel check

def q115Val : B128 := BitVec.ofNat 128 92154265519134838446371680302547358755
def r115Val : B128 := BitVec.ofNat 128 150927228725920353331738429768615062888
noncomputable def r115 := toPoly r115Val
lemma step_115 : r114^2 = (toPoly (to256 q115Val)) * ghashPoly + r115 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r114Val q115Val r115Val; rfl -- Kernel check

def q116Val : B128 := BitVec.ofNat 128 27920283769131231470092830173402764319
def r116Val : B128 := BitVec.ofNat 128 313214421372485833387472208663997282205
noncomputable def r116 := toPoly r116Val
lemma step_116 : r115^2 = (toPoly (to256 q116Val)) * ghashPoly + r116 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r115Val q116Val r116Val; rfl -- Kernel check

def q117Val : B128 := BitVec.ofNat 128 112014799675959688252580459700414321791
def r117Val : B128 := BitVec.ofNat 128 205270197963465857064863719867483624364
noncomputable def r117 := toPoly r117Val
lemma step_117 : r116^2 = (toPoly (to256 q117Val)) * ghashPoly + r117 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r116Val q117Val r117Val; rfl -- Kernel check

def q118Val : B128 := BitVec.ofNat 128 86753307998271888269735528725523529828
def r118Val : B128 := BitVec.ofNat 128 64566217092196733533220887167246694252
noncomputable def r118 := toPoly r118Val
lemma step_118 : r117^2 = (toPoly (to256 q118Val)) * ghashPoly + r118 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r117Val q118Val r118Val; rfl -- Kernel check

def q119Val : B128 := BitVec.ofNat 128 6647458731689705241109357448167490823
def r119Val : B128 := BitVec.ofNat 128 296938408697389789750215214903058009285
noncomputable def r119 := toPoly r119Val
lemma step_119 : r118^2 = (toPoly (to256 q119Val)) * ghashPoly + r119 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r118Val q119Val r119Val; rfl -- Kernel check

def q120Val : B128 := BitVec.ofNat 128 108109219812349672459520657510902285624
def r120Val : B128 := BitVec.ofNat 128 10807226621238021931262095742919972793
noncomputable def r120 := toPoly r120Val
lemma step_120 : r119^2 = (toPoly (to256 q120Val)) * ghashPoly + r120 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r119Val q120Val r120Val; rfl -- Kernel check

def q121Val : B128 := BitVec.ofNat 128 332388214023153671265224035075708225
def r121Val : B128 := BitVec.ofNat 128 129631382596958590886433730895748353798
noncomputable def r121 := toPoly r121Val
lemma step_121 : r120^2 = (toPoly (to256 q121Val)) * ghashPoly + r121 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r120Val q121Val r121Val; rfl -- Kernel check

def q122Val : B128 := BitVec.ofNat 128 26591051871721900988471200547568947211
def r122Val : B128 := BitVec.ofNat 128 59414367279926819390058891142076462501
noncomputable def r122 := toPoly r122Val
lemma step_122 : r121^2 = (toPoly (to256 q122Val)) * ghashPoly + r122 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r121Val q122Val r122Val; rfl -- Kernel check

def q123Val : B128 := BitVec.ofNat 128 5733695559838859821997752053717537795
def r123Val : B128 := BitVec.ofNat 128 70216996008105906389747657374764050840
noncomputable def r123 := toPoly r123Val
lemma step_123 : r122^2 = (toPoly (to256 q123Val)) * ghashPoly + r123 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r122Val q123Val r123Val; rfl -- Kernel check

def q124Val : B128 := BitVec.ofNat 128 6730860005029551728181658353192424518
def r124Val : B128 := BitVec.ofNat 128 264664062837534286517811593844813647762
noncomputable def r124 := toPoly r124Val
lemma step_124 : r123^2 = (toPoly (to256 q124Val)) * ghashPoly + r124 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r123Val q124Val r124Val; rfl -- Kernel check

def q125Val : B128 := BitVec.ofNat 128 106447304523985878018959366555039962424
def r125Val : B128 := BitVec.ofNat 128 313275912279873968957145467509231826604
noncomputable def r125 := toPoly r125Val
lemma step_125 : r124^2 = (toPoly (to256 q125Val)) * ghashPoly + r125 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r124Val q125Val r125Val; rfl -- Kernel check

def q126Val : B128 := BitVec.ofNat 128 112014806009646954068650741980837728622
def r126Val : B128 := BitVec.ofNat 128 205249681632336591850764335734481569114
noncomputable def r126 := toPoly r126Val
lemma step_126 : r125^2 = (toPoly (to256 q126Val)) * ghashPoly + r126 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r125Val q126Val r126Val; rfl -- Kernel check

def q127Val : B128 := BitVec.ofNat 128 86753306731492003871963199800359261216
def r127Val : B128 := BitVec.ofNat 128 48611766702991209068831621643639680420
noncomputable def r127 := toPoly r127Val
lemma step_127 : r126^2 = (toPoly (to256 q127Val)) * ghashPoly + r127 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r126Val q127Val r127Val; rfl -- Kernel check

def q128Val : B128 := BitVec.ofNat 128 5401307411443467674021819165583622406
def r128Val : B128 := BitVec.ofNat 128 2
noncomputable def r128 := toPoly r128Val
lemma step_128 : r127^2 = (toPoly (to256 q128Val)) * ghashPoly + r128 := by
  rw [ghashPoly_eq_P_val]
  apply verify_square_step_correct r127Val q128Val r128Val; rfl -- Kernel check

/-- Intermediate Result: X^(2^64) mod P. Needed for GCD check. -/
theorem X_pow_2_pow_64_eq : (X : Polynomial (ZMod 2))^(2^64) % ghashPoly
    = toPoly (BitVec.ofNat 128 129460184901158119860735353079755610614) := by
  have s0 : X^(2^0) % ghashPoly = r0 % ghashPoly := by rw [pow_zero, pow_one, r0, X_ZMod2Poly_eq_X]
  have s1 := chain_step s0 step_1
  have s2 := chain_step s1 step_2
  have s3 := chain_step s2 step_3
  have s4 := chain_step s3 step_4
  have s5 := chain_step s4 step_5
  have s6 := chain_step s5 step_6
  have s7 := chain_step s6 step_7
  have s8 := chain_step s7 step_8
  have s9 := chain_step s8 step_9
  have s10 := chain_step s9 step_10
  have s11 := chain_step s10 step_11
  have s12 := chain_step s11 step_12
  have s13 := chain_step s12 step_13
  have s14 := chain_step s13 step_14
  have s15 := chain_step s14 step_15
  have s16 := chain_step s15 step_16
  have s17 := chain_step s16 step_17
  have s18 := chain_step s17 step_18
  have s19 := chain_step s18 step_19
  have s20 := chain_step s19 step_20
  have s21 := chain_step s20 step_21
  have s22 := chain_step s21 step_22
  have s23 := chain_step s22 step_23
  have s24 := chain_step s23 step_24
  have s25 := chain_step s24 step_25
  have s26 := chain_step s25 step_26
  have s27 := chain_step s26 step_27
  have s28 := chain_step s27 step_28
  have s29 := chain_step s28 step_29
  have s30 := chain_step s29 step_30
  have s31 := chain_step s30 step_31
  have s32 := chain_step s31 step_32
  have s33 := chain_step s32 step_33
  have s34 := chain_step s33 step_34
  have s35 := chain_step s34 step_35
  have s36 := chain_step s35 step_36
  have s37 := chain_step s36 step_37
  have s38 := chain_step s37 step_38
  have s39 := chain_step s38 step_39
  have s40 := chain_step s39 step_40
  have s41 := chain_step s40 step_41
  have s42 := chain_step s41 step_42
  have s43 := chain_step s42 step_43
  have s44 := chain_step s43 step_44
  have s45 := chain_step s44 step_45
  have s46 := chain_step s45 step_46
  have s47 := chain_step s46 step_47
  have s48 := chain_step s47 step_48
  have s49 := chain_step s48 step_49
  have s50 := chain_step s49 step_50
  have s51 := chain_step s50 step_51
  have s52 := chain_step s51 step_52
  have s53 := chain_step s52 step_53
  have s54 := chain_step s53 step_54
  have s55 := chain_step s54 step_55
  have s56 := chain_step s55 step_56
  have s57 := chain_step s56 step_57
  have s58 := chain_step s57 step_58
  have s59 := chain_step s58 step_59
  have s60 := chain_step s59 step_60
  have s61 := chain_step s60 step_61
  have s62 := chain_step s61 step_62
  have s63 := chain_step s62 step_63
  have s64 := chain_step s63 step_64
  rw [s64]
  rw [r64, r64Val]
  rw [Polynomial.mod_eq_self_iff]
  · -- Degree proof
    conv_rhs => rw [ghashPoly_degree]
    apply (toPoly_degree_lt_w (w := 128)
      (h_w_pos := by simp only [gt_iff_lt, Nat.ofNat_pos]) (v := r64Val))
  · exact ghashPoly_ne_zero

/-- Final Result: X^(2^128) = X (mod P). -/
theorem X_pow_2_pow_128_eq : (X : Polynomial (ZMod 2))^(2^128) % ghashPoly = X := by
  have s0 : X^(2^0) % ghashPoly = r0 % ghashPoly := by rw [pow_zero, pow_one, r0, X_ZMod2Poly_eq_X]
  have s1 := chain_step s0 step_1
  have s2 := chain_step s1 step_2
  have s3 := chain_step s2 step_3
  have s4 := chain_step s3 step_4
  have s5 := chain_step s4 step_5
  have s6 := chain_step s5 step_6
  have s7 := chain_step s6 step_7
  have s8 := chain_step s7 step_8
  have s9 := chain_step s8 step_9
  have s10 := chain_step s9 step_10
  have s11 := chain_step s10 step_11
  have s12 := chain_step s11 step_12
  have s13 := chain_step s12 step_13
  have s14 := chain_step s13 step_14
  have s15 := chain_step s14 step_15
  have s16 := chain_step s15 step_16
  have s17 := chain_step s16 step_17
  have s18 := chain_step s17 step_18
  have s19 := chain_step s18 step_19
  have s20 := chain_step s19 step_20
  have s21 := chain_step s20 step_21
  have s22 := chain_step s21 step_22
  have s23 := chain_step s22 step_23
  have s24 := chain_step s23 step_24
  have s25 := chain_step s24 step_25
  have s26 := chain_step s25 step_26
  have s27 := chain_step s26 step_27
  have s28 := chain_step s27 step_28
  have s29 := chain_step s28 step_29
  have s30 := chain_step s29 step_30
  have s31 := chain_step s30 step_31
  have s32 := chain_step s31 step_32
  have s33 := chain_step s32 step_33
  have s34 := chain_step s33 step_34
  have s35 := chain_step s34 step_35
  have s36 := chain_step s35 step_36
  have s37 := chain_step s36 step_37
  have s38 := chain_step s37 step_38
  have s39 := chain_step s38 step_39
  have s40 := chain_step s39 step_40
  have s41 := chain_step s40 step_41
  have s42 := chain_step s41 step_42
  have s43 := chain_step s42 step_43
  have s44 := chain_step s43 step_44
  have s45 := chain_step s44 step_45
  have s46 := chain_step s45 step_46
  have s47 := chain_step s46 step_47
  have s48 := chain_step s47 step_48
  have s49 := chain_step s48 step_49
  have s50 := chain_step s49 step_50
  have s51 := chain_step s50 step_51
  have s52 := chain_step s51 step_52
  have s53 := chain_step s52 step_53
  have s54 := chain_step s53 step_54
  have s55 := chain_step s54 step_55
  have s56 := chain_step s55 step_56
  have s57 := chain_step s56 step_57
  have s58 := chain_step s57 step_58
  have s59 := chain_step s58 step_59
  have s60 := chain_step s59 step_60
  have s61 := chain_step s60 step_61
  have s62 := chain_step s61 step_62
  have s63 := chain_step s62 step_63
  have s64 := chain_step s63 step_64
  have s65 := chain_step s64 step_65
  have s66 := chain_step s65 step_66
  have s67 := chain_step s66 step_67
  have s68 := chain_step s67 step_68
  have s69 := chain_step s68 step_69
  have s70 := chain_step s69 step_70
  have s71 := chain_step s70 step_71
  have s72 := chain_step s71 step_72
  have s73 := chain_step s72 step_73
  have s74 := chain_step s73 step_74
  have s75 := chain_step s74 step_75
  have s76 := chain_step s75 step_76
  have s77 := chain_step s76 step_77
  have s78 := chain_step s77 step_78
  have s79 := chain_step s78 step_79
  have s80 := chain_step s79 step_80
  have s81 := chain_step s80 step_81
  have s82 := chain_step s81 step_82
  have s83 := chain_step s82 step_83
  have s84 := chain_step s83 step_84
  have s85 := chain_step s84 step_85
  have s86 := chain_step s85 step_86
  have s87 := chain_step s86 step_87
  have s88 := chain_step s87 step_88
  have s89 := chain_step s88 step_89
  have s90 := chain_step s89 step_90
  have s91 := chain_step s90 step_91
  have s92 := chain_step s91 step_92
  have s93 := chain_step s92 step_93
  have s94 := chain_step s93 step_94
  have s95 := chain_step s94 step_95
  have s96 := chain_step s95 step_96
  have s97 := chain_step s96 step_97
  have s98 := chain_step s97 step_98
  have s99 := chain_step s98 step_99
  have s100 := chain_step s99 step_100
  have s101 := chain_step s100 step_101
  have s102 := chain_step s101 step_102
  have s103 := chain_step s102 step_103
  have s104 := chain_step s103 step_104
  have s105 := chain_step s104 step_105
  have s106 := chain_step s105 step_106
  have s107 := chain_step s106 step_107
  have s108 := chain_step s107 step_108
  have s109 := chain_step s108 step_109
  have s110 := chain_step s109 step_110
  have s111 := chain_step s110 step_111
  have s112 := chain_step s111 step_112
  have s113 := chain_step s112 step_113
  have s114 := chain_step s113 step_114
  have s115 := chain_step s114 step_115
  have s116 := chain_step s115 step_116
  have s117 := chain_step s116 step_117
  have s118 := chain_step s117 step_118
  have s119 := chain_step s118 step_119
  have s120 := chain_step s119 step_120
  have s121 := chain_step s120 step_121
  have s122 := chain_step s121 step_122
  have s123 := chain_step s122 step_123
  have s124 := chain_step s123 step_124
  have s125 := chain_step s124 step_125
  have s126 := chain_step s125 step_126
  have s127 := chain_step s126 step_127
  have s128 := chain_step s127 step_128

  rw [s128]
  have r128_eq_X : r128 = X := by
    rw [r128, r128Val]
    exact X_ZMod2Poly_eq_X
  rw [r128_eq_X]
  rw [X_mod_ghashPoly]

end BF128Ghash
