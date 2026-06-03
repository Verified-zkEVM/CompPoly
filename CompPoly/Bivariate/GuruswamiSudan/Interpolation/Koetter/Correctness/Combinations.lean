/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Soundness

/-!
# Koetter Basis Combination Helpers

Finite-`Y` expansion, basis-combination, and weak-leading minimality lemmas used
by Koetter completeness.
-/

namespace CompPoly

namespace GuruswamiSudan

theorem koetterRawInterpolate_some_of_exists_final_entry {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    (hEntry : ∃ idx,
      idx < (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis.size ∧
      (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis.getD idx 0 ≠ 0 ∧
      CBivariate.natWeightedDegree
        ((koetterProcessConstraints params
          (interpolationConstraints points params.multiplicity)
          (koetterInitialState params)).basis.getD idx 0)
        1 (yWeight params) ≤ params.weightedDegreeBound) :
    ∃ Q, koetterRawInterpolate points params = some Q := by
  unfold koetterRawInterpolate
  exact koetterSelectFinal?_some_of_exists_entry hEntry

theorem koetterFinalBasis_size {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) :
    (koetterProcessConstraints params
      (interpolationConstraints points params.multiplicity)
      (koetterInitialState params)).basis.size = koetterYCap params + 1 := by
  rw [koetterProcessConstraints_size]
  exact koetterInitialBasis_size (F := F) params

theorem koetterFinalBasis_nonempty {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (params : GSInterpParams) :
    0 <
      (koetterProcessConstraints params
        (interpolationConstraints points params.multiplicity)
        (koetterInitialState params)).basis.size := by
  rw [koetterFinalBasis_size points params]
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

theorem validWitness_coeff_eq_zero_of_yCap_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hMessage : ¬ params.messageDegree ≤ 1)
    (hQ : ValidInterpolationWitness points params Q) {i j : Nat}
    (hj : koetterYCap params < j) :
    CBivariate.coeff Q i j = 0 := by
  have hcoeffY := validWitness_coeffY_eq_zero_of_yCap_lt
    (points := points) (params := params) (Q := Q) hMessage hQ hj
  unfold CBivariate.coeff
  rw [hcoeffY, CPolynomial.coeff_zero]

theorem validWitness_exists_coeff_within_yCap {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hMessage : ¬ params.messageDegree ≤ 1)
    (hQ : ValidInterpolationWitness points params Q) :
    ∃ i j, j ≤ koetterYCap params ∧ CBivariate.coeff Q i j ≠ 0 := by
  rcases hQ with ⟨hne, hdeg, hmult⟩
  by_contra hnone
  apply hne
  rw [CBivariate.eq_iff_coeff]
  intro i j
  by_cases hj : j ≤ koetterYCap params
  · by_contra hcoeff
    exact hnone ⟨i, j, hj, hcoeff⟩
  · exact validWitness_coeff_eq_zero_of_yCap_lt
      (points := points) (params := params) (Q := Q) hMessage
      ⟨hne, hdeg, hmult⟩ (by omega)

theorem validWitness_exists_bounded_coeff_within_yCap {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hMessage : ¬ params.messageDegree ≤ 1)
    (hQ : ValidInterpolationWitness points params Q) :
    ∃ i j,
      j ≤ koetterYCap params ∧
        CBivariate.coeff Q i j ≠ 0 ∧
          i + yWeight params * j ≤ params.weightedDegreeBound := by
  rcases hQ with ⟨hne, hdeg, hmult⟩
  rcases validWitness_exists_coeff_within_yCap
      (points := points) (params := params) (Q := Q) hMessage
      ⟨hne, hdeg, hmult⟩ with
    ⟨i, j, hj, hcoeff⟩
  have hweight :
      1 * i + yWeight params * j ≤ params.weightedDegreeBound :=
    (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params)
      params.weightedDegreeBound).mp hdeg i j hcoeff
  refine ⟨i, j, hj, hcoeff, ?_⟩
  simpa using hweight

theorem validWitness_discrepancy_eq_zero_of_constraint_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hQ : ValidInterpolationWitness points params Q)
    {constraint : InterpolationConstraint F}
    (hmem : constraint ∈ (interpolationConstraints points params.multiplicity).toList) :
    koetterDiscrepancy constraint Q = 0 := by
  rcases hQ with ⟨_hne, _hdeg, hmult⟩
  rw [interpolationConstraints_toList_eq_list] at hmem
  unfold interpolationConstraintsList at hmem
  apply List.mem_flatMap.mp at hmem
  rcases hmem with ⟨point, hpoint, horders⟩
  apply List.mem_flatMap.mp at horders
  rcases horders with ⟨a, ha, hbmem⟩
  apply List.mem_map.mp at hbmem
  rcases hbmem with ⟨b, hb, hconstraint⟩
  subst constraint
  have haLt : a < params.multiplicity := by
    simpa using ha
  have hbLt : b < params.multiplicity - a := by
    simpa using hb
  exact hmult point hpoint a b (by omega)

def koetterBasisYBounded {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (cap : Nat) (basis : Array (CBivariate F)) : Prop :=
  ∀ idx, idx < basis.size → ∀ i j, cap < j →
    CompPoly.CBivariate.coeff (basis.getD idx 0) i j = 0

theorem koetterBasisYBounded_coeffY_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {cap : Nat} {basis : Array (CBivariate F)}
    (hBasis : koetterBasisYBounded cap basis) {idx : Nat} (hidx : idx < basis.size)
    {j : Nat} (hj : cap < j) :
    (basis.getD idx 0).val.coeff j = 0 := by
  apply (CPolynomial.eq_iff_coeff (p := (basis.getD idx 0).val.coeff j)
    (q := 0)).2
  intro i
  exact hBasis idx hidx i j hj

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

theorem koetterRowLeadingAt_coeffY_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {idx : Nat} {P : CBivariate F}
    (h : koetterRowLeadingAt params idx P) :
    P.val.coeff idx ≠ 0 := by
  intro hzero
  have hcoeff := h.2.1
  change (P.val.coeff idx).coeff
      (CBivariate.natWeightedDegree P 1 (yWeight params) - yWeight params * idx) ≠ 0
    at hcoeff
  rw [hzero, CPolynomial.coeff_zero] at hcoeff
  exact hcoeff rfl

theorem koetterRowLeadingAt_coeffY_natDegree_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {idx : Nat} {P : CBivariate F}
    (h : koetterRowLeadingAt params idx P) :
    (P.val.coeff idx).natDegree =
      CBivariate.natWeightedDegree P 1 (yWeight params) - yWeight params * idx := by
  apply le_antisymm
  · have hrowNe := koetterRowLeadingAt_coeffY_ne_zero h
    have hlead :
        CBivariate.coeff P (P.val.coeff idx).natDegree idx ≠ 0 := by
      change (P.val.coeff idx).coeff (P.val.coeff idx).natDegree ≠ 0
      rw [← CPolynomial.leadingCoeff_eq_coeff_natDegree]
      exact CPolynomial.leadingCoeff_ne_zero hrowNe
    have hle := (CBivariate.natWeightedDegree_le_iff_coeff P 1 (yWeight params)
      (CBivariate.natWeightedDegree P 1 (yWeight params))).mp le_rfl
        (P.val.coeff idx).natDegree idx hlead
    omega
  · exact CPolynomial.le_natDegree_of_ne_zero h.2.1

theorem coeff_ofYConstant_mul_rowLeadingAt_lead_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {idx : Nat} {P : CBivariate F}
    (A : CPolynomial F) (hA : A ≠ 0)
    (h : koetterRowLeadingAt params idx P) :
    CBivariate.coeff (CBivariate.ofYConstant A * P)
        (A.natDegree +
          (CBivariate.natWeightedDegree P 1 (yWeight params) - yWeight params * idx))
        idx ≠ 0 := by
  rw [coeff_ofYConstant_mul]
  rw [← koetterRowLeadingAt_coeffY_natDegree_eq h]
  rw [cpoly_coeff_mul_natDegree_add]
  exact mul_ne_zero (CPolynomial.leadingCoeff_ne_zero hA)
    (CPolynomial.leadingCoeff_ne_zero (koetterRowLeadingAt_coeffY_ne_zero h))

theorem coeff_ofYConstant_mul_rowLeadingAt_eq_zero_of_higherY_top {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {rowIdx targetIdx targetX : Nat}
    {P : CBivariate F} (A : CPolynomial F)
    (h : koetterRowLeadingAt params rowIdx P) (hlt : rowIdx < targetIdx)
    (hweight :
      targetX + yWeight params * targetIdx =
        A.natDegree + CBivariate.natWeightedDegree P 1 (yWeight params)) :
    CBivariate.coeff (CBivariate.ofYConstant A * P) targetX targetIdx = 0 := by
  by_contra hcoeff
  rw [coeff_ofYConstant_mul] at hcoeff
  let B := P.val.coeff targetIdx
  have hmulCoeff :
      targetX ≤ (A * B).natDegree :=
    CPolynomial.le_natDegree_of_ne_zero hcoeff
  have hmulDeg :
      (A * B).natDegree ≤ A.natDegree + B.natDegree :=
    cpoly_natDegree_mul_le A B
  have hBne : B ≠ 0 := by
    intro hzero
    rw [show P.val.coeff targetIdx = B from rfl, hzero, CPolynomial.mul_zero] at hcoeff
    exact hcoeff (CPolynomial.coeff_zero targetX)
  have hBcoeff :
      CBivariate.coeff P B.natDegree targetIdx ≠ 0 := by
    change (P.val.coeff targetIdx).coeff B.natDegree ≠ 0
    rw [show P.val.coeff targetIdx = B from rfl]
    rw [← CPolynomial.leadingCoeff_eq_coeff_natDegree]
    exact CPolynomial.leadingCoeff_ne_zero hBne
  have hrowStrict := h.2.2 B.natDegree targetIdx hlt hBcoeff
  have htargetLe :
      targetX + yWeight params * targetIdx ≤
        A.natDegree + B.natDegree + yWeight params * targetIdx := by
    omega
  have htargetLt :
      targetX + yWeight params * targetIdx <
        A.natDegree + CBivariate.natWeightedDegree P 1 (yWeight params) := by
    omega
  omega

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

theorem ofYConstant_X {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] :
    CBivariate.ofYConstant (CPolynomial.X : CPolynomial F) = CBivariate.X := by
  rfl

theorem ofYConstant_linearFactor {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] (x : F) :
    CBivariate.ofYConstant (CPolynomial.linearFactor x) =
      CBivariate.linearXFactor x := by
  rw [CPolynomial.linearFactor, ofYConstant_add, ofYConstant_C, ofYConstant_X]
  unfold CBivariate.linearXFactor
  rw [sub_eq_add_neg]
  have hneg : CBivariate.CC (-x) = -CBivariate.CC x := by
    rw [CBivariate.eq_iff_coeff]
    intro i j
    change CBivariate.coeff (CBivariate.ofYConstant (CPolynomial.C (-x))) i j =
      CBivariate.coeff (-CBivariate.ofYConstant (CPolynomial.C x)) i j
    rw [CompPoly.CBivariate.coeff_neg, coeff_ofYConstant, coeff_ofYConstant]
    by_cases hj : j = 0
    · subst j
      rw [CPolynomial.coeff_C, CPolynomial.coeff_C]
      by_cases hi : i = 0 <;> simp [hi]
    · simp [hj]
  rw [hneg]
  abel

theorem ofYConstant_linearFactor_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] (x : F) (P : CPolynomial F) :
    CBivariate.ofYConstant (CPolynomial.linearFactor x * P) =
      CBivariate.linearXFactor x * CBivariate.ofYConstant P := by
  rw [ofYConstant_mul, ofYConstant_linearFactor]

theorem ofYConstant_mul_linearXFactor_divByMonic_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x : F) (A : CPolynomial F) (P : CBivariate F)
    (hroot : CPolynomial.eval x A = 0) :
    CBivariate.ofYConstant A * P =
      CBivariate.ofYConstant (A.divByMonic (CPolynomial.linearFactor x)) *
        (CBivariate.linearXFactor x * P) := by
  have hdiv :=
    cpoly_linearFactor_mul_divByMonic_eq_self_of_eval_eq_zero x A hroot
  conv_lhs =>
    rw [← hdiv]
  rw [ofYConstant_linearFactor_mul]
  ring

theorem ofYConstant_mul_oldPivot_eq_updatedPivot_of_eval_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (A : CPolynomial F)
    (hroot : CPolynomial.eval constraint.x A = 0) :
    CBivariate.ofYConstant A * basis.getD pivot.index 0 =
      CBivariate.ofYConstant (A.divByMonic (CPolynomial.linearFactor constraint.x)) *
        koetterUpdatedEntry constraint basis pivot pivot.index := by
  unfold koetterUpdatedEntry
  rw [if_pos (by simp)]
  exact ofYConstant_mul_linearXFactor_divByMonic_eq
    constraint.x A (basis.getD pivot.index 0) hroot

theorem ofYConstant_mul_oldNonpivot_eq_updated_add_correction {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (A : CPolynomial F) {idx : Nat}
    (hidx : ¬ idx == pivot.index) :
    CBivariate.ofYConstant A * basis.getD idx 0 =
      CBivariate.ofYConstant A * koetterUpdatedEntry constraint basis pivot idx +
        CBivariate.ofYConstant
          (CPolynomial.C
            (koetterDiscrepancy constraint (basis.getD idx 0) / pivot.discrepancy) * A) *
          basis.getD pivot.index 0 := by
  unfold koetterUpdatedEntry
  rw [if_neg hidx]
  by_cases hdelta : koetterDiscrepancy constraint (basis.getD idx 0) == 0
  · rw [if_pos hdelta]
    have hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0 :=
      LawfulBEq.eq_of_beq hdelta
    have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
      simpa [Array.getD_eq_getD_getElem?] using hzero
    simp [hzero', ofYConstant_zero]
  · rw [if_neg hdelta]
    rw [ofYConstant_mul, ofYConstant_C]
    ring

theorem koetterDiscrepancy_add {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (P Q : CBivariate F) :
    koetterDiscrepancy constraint (P + Q) =
      koetterDiscrepancy constraint P + koetterDiscrepancy constraint Q := by
  unfold koetterDiscrepancy
  exact CBivariate.hasseDerivativeEval_add constraint.xOrder constraint.yOrder
    constraint.x constraint.y P Q

theorem koetterDiscrepancy_ofYConstant_C_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (c : F) (P : CBivariate F) :
    koetterDiscrepancy constraint (CBivariate.ofYConstant (CPolynomial.C c) * P) =
      c * koetterDiscrepancy constraint P := by
  rw [ofYConstant_C]
  unfold koetterDiscrepancy
  exact CBivariate.hasseDerivativeEval_CC_mul c constraint.xOrder constraint.yOrder
    constraint.x constraint.y P

theorem koetterDiscrepancy_X_mul_of_lower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (P : CBivariate F)
    (hLower : ∀ a, constraint.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y P = 0) :
    koetterDiscrepancy constraint (CBivariate.X * P) =
      constraint.x * koetterDiscrepancy constraint P := by
  unfold koetterDiscrepancy
  cases hx : constraint.xOrder with
  | zero =>
      rw [CBivariate.hasseDerivativeEval_X_mul_zero_xOrder]
  | succ a =>
      rw [CBivariate.hasseDerivativeEval_X_mul_succ_xOrder, hLower a hx]
      simp

theorem koetterDiscrepancy_ofYConstant_X_mul_of_lower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (A : CPolynomial F) (P : CBivariate F)
    (hLower : ∀ a, constraint.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (CBivariate.ofYConstant A * P) = 0) :
    koetterDiscrepancy constraint (CBivariate.ofYConstant (CPolynomial.X * A) * P) =
      constraint.x * koetterDiscrepancy constraint (CBivariate.ofYConstant A * P) := by
  rw [ofYConstant_X_mul, mul_assoc]
  exact koetterDiscrepancy_X_mul_of_lower constraint (CBivariate.ofYConstant A * P) hLower

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

theorem koetterDiscrepancy_ofYConstant_mul_eq_eval_mul_of_lower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (A : CPolynomial F) (P : CBivariate F)
    (hLower : ∀ a, a < constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y P = 0) :
    koetterDiscrepancy constraint (CBivariate.ofYConstant A * P) =
      CPolynomial.eval constraint.x A * koetterDiscrepancy constraint P := by
  unfold koetterDiscrepancy
  exact hasseDerivativeEval_ofYConstant_mul_eq_eval_mul_of_lower
    constraint.x constraint.y constraint.yOrder A P constraint.xOrder hLower

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

theorem koetterDiscrepancy_ofYConstant_mul_eq_zero_of_lower {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (A : CPolynomial F) (P : CBivariate F)
    (hLower : ∀ a, a ≤ constraint.xOrder →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y P = 0) :
    koetterDiscrepancy constraint (CBivariate.ofYConstant A * P) = 0 := by
  unfold koetterDiscrepancy
  exact hasseDerivativeEval_ofYConstant_mul_eq_zero_of_lower
    constraint.x constraint.y constraint.yOrder A P constraint.xOrder hLower

def koetterFiniteYExpansion {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (cap : Nat) : CBivariate F :=
  (List.range (cap + 1)).foldl
    (fun out j ↦ out + CBivariate.ofYCoefficient j (Q.val.coeff j)) 0

theorem koetterFiniteYExpansion_coeff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (cap i j : Nat) :
    CBivariate.coeff (koetterFiniteYExpansion Q cap) i j =
      if j ≤ cap then CBivariate.coeff Q i j else 0 := by
  induction cap with
  | zero =>
      unfold koetterFiniteYExpansion
      change
        CBivariate.coeff
            (0 + CBivariate.ofYCoefficient 0 (Q.val.coeff 0)) i j =
          if j ≤ 0 then CBivariate.coeff Q i j else 0
      rw [zero_add, coeff_ofYCoefficient]
      by_cases hj : j = 0
      · subst j
        simp [CBivariate.coeff]
      · have hnot : ¬ j ≤ 0 := by omega
        simp [hj, hnot]
  | succ cap ih =>
      unfold koetterFiniteYExpansion
      rw [show Nat.succ cap + 1 = cap + 1 + 1 by omega, List.range_succ,
        List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        CBivariate.coeff
            (koetterFiniteYExpansion Q cap +
              CBivariate.ofYCoefficient (cap + 1) (Q.val.coeff (cap + 1))) i j =
          if j ≤ Nat.succ cap then CBivariate.coeff Q i j else 0
      rw [CBivariate.coeff_add, ih, coeff_ofYCoefficient]
      by_cases hjle : j ≤ cap
      · have hjSucc : j ≤ Nat.succ cap := by omega
        have hne : ¬ j = cap + 1 := by omega
        simp [hjle, hjSucc, hne]
      · by_cases hjeq : j = cap + 1
        · have hjSucc : j ≤ Nat.succ cap := by omega
          subst j
          simp [CBivariate.coeff]
        · have hjSucc : ¬ j ≤ Nat.succ cap := by omega
          simp [hjle, hjeq, hjSucc]

theorem koetterFiniteYExpansion_eq_of_yCap {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {cap : Nat}
    (hQ : ∀ j, cap < j → Q.val.coeff j = 0) :
    koetterFiniteYExpansion Q cap = Q := by
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [koetterFiniteYExpansion_coeff]
  by_cases hj : j ≤ cap
  · simp [hj]
  · have hz := hQ j (by omega)
    unfold CBivariate.coeff
    rw [if_neg hj, hz, CPolynomial.coeff_zero]

theorem cpoly_monomial_zero_one_eq_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] :
    CPolynomial.monomial 0 (1 : F) = 1 := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  rw [CPolynomial.coeff_monomial, CPolynomial.coeff_one]

theorem ofYConstant_mul_monomialY_eq_ofYCoefficient {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (P : CPolynomial F) (j : Nat) :
    CBivariate.ofYConstant P * CBivariate.monomialXY 0 j (1 : F) =
      CBivariate.ofYCoefficient j P := by
  rw [CBivariate.eq_iff_coeff]
  intro i k
  unfold CBivariate.ofYConstant CBivariate.ofYCoefficient CBivariate.monomialXY
    CBivariate.coeff
  have houter :
      CPolynomial.coeff
          (CPolynomial.C P *
            (CPolynomial.monomial j (CPolynomial.monomial 0 (1 : F)) :
              CBivariate F)) k =
        P * CPolynomial.coeff
          (CPolynomial.monomial j (CPolynomial.monomial 0 (1 : F)) :
            CBivariate F) k := by
    exact CPolynomial.coeff_C_mul
      (p := (CPolynomial.monomial j (CPolynomial.monomial 0 (1 : F)) :
        CBivariate F)) (c := P) k
  by_cases hk : k = j
  · subst k
    have hleft := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    rw [CPolynomial.coeff_monomial] at hleft
    simp [cpoly_monomial_zero_one_eq_one] at hleft
    have hright := congrArg (fun P : CPolynomial F ↦ P.coeff i)
      (CPolynomial.coeff_monomial j j P)
    simp at hright
    simpa [CPolynomial.coeff, cpoly_monomial_zero_one_eq_one] using
      hleft.trans hright.symm
  · have hleft := congrArg (fun P : CPolynomial F ↦ P.coeff i) houter
    rw [CPolynomial.coeff_monomial] at hleft
    simp [hk] at hleft
    have hright := congrArg (fun P : CPolynomial F ↦ P.coeff i)
      (CPolynomial.coeff_monomial j k P)
    simp [hk] at hright
    simpa [CPolynomial.coeff] using hleft.trans hright.symm

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

def koetterUpdatedEntryCombination {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) (pivot : KoetterPivot F) : CBivariate F :=
  (List.range basis.size).foldl
    (fun out idx ↦
      out + CBivariate.ofYConstant (weights idx) *
        koetterUpdatedEntry constraint basis pivot idx) 0

theorem koetterBasisCombination_updateBasis_eq_updatedEntryCombination {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (constraint : InterpolationConstraint F)
    (basis : Array (CBivariate F)) (pivot : KoetterPivot F) :
    koetterBasisCombination weights (koetterUpdateBasis constraint basis pivot) =
      koetterUpdatedEntryCombination weights constraint basis pivot := by
  unfold koetterBasisCombination koetterUpdatedEntryCombination
  rw [koetterUpdateBasis_size]
  apply foldl_add_congr_terms
  intro idx hmem
  have hidx : idx < basis.size := List.mem_range.mp hmem
  rw [koetterUpdateBasis_getD_of_lt constraint basis pivot hidx]

def koetterBasisSpanContains {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array (CBivariate F)) (Q : CBivariate F) : Prop :=
  ∃ weights : Nat → CPolynomial F, koetterBasisCombination weights basis = Q

theorem koetterBasisCombination_eq_zero_of_entries_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F))
    (hzero : ∀ idx, idx < basis.size → basis.getD idx 0 = 0) :
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
        rw [hzero idx hi, mul_zero, add_zero]
        exact ih (fun j hj ↦ hidx j (by simp [hj]))
  simpa [step] using hfold (List.range basis.size)
    (fun idx hmem ↦ List.mem_range.mp hmem)

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

theorem exists_nonzero_entry_of_koetterBasisCombination_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (weights : Nat → CPolynomial F) (basis : Array (CBivariate F))
    {Q : CBivariate F}
    (hcomb : koetterBasisCombination weights basis = Q) (hQ : Q ≠ 0) :
    ∃ idx, idx < basis.size ∧ basis.getD idx 0 ≠ 0 := by
  by_contra hnone
  have hzero : ∀ idx, idx < basis.size → basis.getD idx 0 = 0 := by
    intro idx hi
    by_contra hne
    exact hnone ⟨idx, hi, hne⟩
  apply hQ
  rw [← hcomb]
  exact koetterBasisCombination_eq_zero_of_entries_zero weights basis hzero

theorem exists_nonzero_entry_of_koetterBasisSpanContains {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (basis : Array (CBivariate F)) {Q : CBivariate F}
    (hspan : koetterBasisSpanContains basis Q) (hQ : Q ≠ 0) :
    ∃ idx, idx < basis.size ∧ basis.getD idx 0 ≠ 0 := by
  rcases hspan with ⟨weights, hcomb⟩
  exact exists_nonzero_entry_of_koetterBasisCombination_ne_zero
    weights basis hcomb hQ

theorem exists_basis_entry_natWeightedDegree_le_of_weakLeading_span {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (hWeak : koetterBasisWeakLeading params basis)
    (hspan : koetterBasisSpanContains basis Q) (hQ : Q ≠ 0) :
    ∃ idx, idx < basis.size ∧ basis.getD idx 0 ≠ 0 ∧
      CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) ≤
        CBivariate.natWeightedDegree Q 1 (yWeight params) := by
  rcases hspan with ⟨weights, hcomb⟩
  have hcombNe : koetterBasisCombination weights basis ≠ 0 := by
    intro hzero
    exact hQ (by simpa [hcomb] using hzero)
  have hweightExists : ∃ idx, idx < basis.size ∧ weights idx ≠ 0 := by
    by_contra hnone
    have hzero : ∀ idx, idx < basis.size → weights idx = 0 := by
      intro idx hi
      by_contra hne
      exact hnone ⟨idx, hi, hne⟩
    exact hcombNe (koetterBasisCombination_eq_zero_of_weights_zero weights basis hzero)
  let active : Finset Nat := (Finset.range basis.size).filter (fun idx ↦ weights idx ≠ 0)
  have hactiveNonempty : active.Nonempty := by
    rcases hweightExists with ⟨idx, hi, hne⟩
    exact ⟨idx, by simp [active, hi, hne]⟩
  let rowDeg : Nat → Nat := fun idx ↦
    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params)
  let measure : Nat → Nat := fun idx ↦ (weights idx).natDegree + rowDeg idx
  rcases Finset.exists_max_image active measure hactiveNonempty with
    ⟨maxIdx, hmaxMem, hmaxMax⟩
  let maxMeasure := measure maxIdx
  let tied : Finset Nat := active.filter (fun idx ↦ measure idx = maxMeasure)
  have htiedNonempty : tied.Nonempty := by
    exact ⟨maxIdx, by simp [tied, hmaxMem, maxMeasure]⟩
  rcases Finset.exists_max_image tied (fun idx : Nat ↦ idx) htiedNonempty with
    ⟨best, hbestTied, hbestMax⟩
  have hbestActive : best ∈ active := by
    simpa [tied] using (Finset.mem_filter.mp hbestTied).1
  have hbestMeasure : measure best = maxMeasure := by
    simpa [tied] using (Finset.mem_filter.mp hbestTied).2
  have hbestIdx : best < basis.size := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hbestActive).1
  have hbestWeightNe : weights best ≠ 0 := by
    exact (Finset.mem_filter.mp hbestActive).2
  have hbestRow :
      koetterRowLeadingAt params best (basis.getD best 0) := by
    simpa [koetterBasisWeakLeading, Array.getD_eq_getD_getElem?] using
      hWeak best hbestIdx
  have hbestEntryNe : basis.getD best 0 ≠ 0 :=
    koetterRowLeadingAt_ne_zero hbestRow
  refine ⟨best, hbestIdx, hbestEntryNe, ?_⟩
  let targetX := measure best - yWeight params * best
  have htargetWeight :
      targetX + yWeight params * best = measure best := by
    have hrowLe := hbestRow.1
    dsimp [targetX, measure, rowDeg] at hrowLe ⊢
    omega
  have hbestTermNe :
      CBivariate.coeff
        (CBivariate.ofYConstant (weights best) * basis.getD best 0)
        targetX best ≠ 0 := by
    have hraw :=
      coeff_ofYConstant_mul_rowLeadingAt_lead_ne_zero
        (weights best) hbestWeightNe hbestRow
    have hxEq :
        targetX =
          (weights best).natDegree +
            (CBivariate.natWeightedDegree (basis.getD best 0) 1 (yWeight params) -
              yWeight params * best) := by
      dsimp [targetX, measure, rowDeg]
      exact Nat.add_sub_assoc hbestRow.1 (weights best).natDegree
    rw [hxEq]
    exact hraw
  have htermZero : ∀ idx, idx ∈ List.range basis.size → idx ≠ best →
      CBivariate.coeff
        (CBivariate.ofYConstant (weights idx) * basis.getD idx 0)
        targetX best = 0 := by
    intro idx hmem hidxNe
    have hidx : idx < basis.size := List.mem_range.mp hmem
    by_cases hweight : weights idx = 0
    · rw [hweight, ofYConstant_zero, zero_mul, CBivariate.coeff_zero]
    · have hidxActive : idx ∈ active := by
        simp [active, hidx, hweight]
      have hmeasureLe : measure idx ≤ measure best := by
        have hleMax := hmaxMax idx hidxActive
        rw [hbestMeasure]
        exact hleMax
      rcases lt_or_eq_of_le hmeasureLe with hmeasureLt | hmeasureEq
      · by_contra hcoeff
        have hcoeffWeight := (CBivariate.natWeightedDegree_le_iff_coeff
          (CBivariate.ofYConstant (weights idx) * basis.getD idx 0) 1
          (yWeight params)
          (CBivariate.natWeightedDegree
            (CBivariate.ofYConstant (weights idx) * basis.getD idx 0) 1
            (yWeight params))).mp le_rfl targetX best hcoeff
        have htermDegree :=
          natWeightedDegree_ofYConstant_mul_le (weights idx) (basis.getD idx 0)
            (yWeight params)
        dsimp [targetX, measure, rowDeg] at hmeasureLt htargetWeight htermDegree hcoeffWeight
        omega
      · have hidxLeBest : idx ≤ best := by
          have hidxTied : idx ∈ tied := by
            simp [tied, hidxActive, maxMeasure, hbestMeasure, hmeasureEq]
          exact hbestMax idx hidxTied
        have hidxLtBest : idx < best := by
          omega
        have hrowIdx :
            koetterRowLeadingAt params idx (basis.getD idx 0) := by
          simpa [koetterBasisWeakLeading, Array.getD_eq_getD_getElem?] using
            hWeak idx hidx
        apply coeff_ofYConstant_mul_rowLeadingAt_eq_zero_of_higherY_top
          (weights idx) hrowIdx hidxLtBest
        dsimp [targetX, measure, rowDeg] at htargetWeight hmeasureEq ⊢
        omega
  have hcoeffCombination :
      CBivariate.coeff (koetterBasisCombination weights basis) targetX best =
        CBivariate.coeff
          (CBivariate.ofYConstant (weights best) * basis.getD best 0)
          targetX best := by
    rw [coeff_koetterBasisCombination]
    let bestCoeff :=
      CBivariate.coeff
        (CBivariate.ofYConstant (weights best) * basis.getD best 0)
        targetX best
    have hcongr :
        (List.range basis.size).foldl
            (fun out idx ↦
              out + CBivariate.coeff
                (CBivariate.ofYConstant (weights idx) * basis.getD idx 0)
                targetX best)
            0 =
          (List.range basis.size).foldl
            (fun out idx ↦ out + if idx == best then bestCoeff else 0) 0 := by
      apply foldl_add_congr_terms
      intro idx hmem
      by_cases hidxBeq : idx == best
      · have hidxEq : idx = best := LawfulBEq.eq_of_beq hidxBeq
        subst idx
        simp [bestCoeff]
      · rw [if_neg hidxBeq]
        have hidxNe : idx ≠ best := by
          intro hEq
          subst idx
          simp at hidxBeq
        rw [htermZero idx hmem hidxNe]
    rw [hcongr]
    have hbestMemRange : best ∈ List.range basis.size := by
      simpa using hbestIdx
    simpa [bestCoeff] using
      foldl_add_single_beq_of_nodup_mem (List.range basis.size) best bestCoeff
        (List.nodup_range (n := basis.size)) hbestMemRange
  have hcombCoeffNe :
      CBivariate.coeff (koetterBasisCombination weights basis) targetX best ≠ 0 := by
    rw [hcoeffCombination]
    exact hbestTermNe
  have hQCoeffNe : CBivariate.coeff Q targetX best ≠ 0 := by
    rw [← hcomb]
    exact hcombCoeffNe
  have hQWeight := (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params)
    (CBivariate.natWeightedDegree Q 1 (yWeight params))).mp le_rfl
      targetX best hQCoeffNe
  have hmeasureLeQ :
      measure best ≤ CBivariate.natWeightedDegree Q 1 (yWeight params) := by
    dsimp [targetX] at htargetWeight
    omega
  dsimp [measure, rowDeg] at hmeasureLeQ ⊢
  omega

end GuruswamiSudan

end CompPoly
