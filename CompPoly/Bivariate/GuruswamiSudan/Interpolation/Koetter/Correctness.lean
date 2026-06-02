/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Algorithm
import Mathlib.Data.List.Range

/-!
# Koetter Interpolation Correctness

Soundness and completeness theorem surface for the public Koetter interpolation
operation. The executable operation uses the existing low-message-degree branch
and otherwise the checked direct Koetter pass; there is no dense interpolation
fallback in this module.
-/

namespace CompPoly

namespace CBivariate

private theorem coeff_neg {R : Type*}
    [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P : CBivariate R) (i j : Nat) :
    coeff (-P) i j = -coeff P i j := by
  sorry

private theorem coeff_sub {R : Type*}
    [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P Q : CBivariate R) (i j : Nat) :
    coeff (P - Q) i j = coeff P i j - coeff Q i j := by
  sorry

private theorem coeff_CC_mul {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (c : R) (Q : CBivariate R) (i j : Nat) :
    coeff (CC c * Q) i j = c * coeff Q i j := by
  sorry

private theorem coeff_X_mul_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (j : Nat) :
    coeff (X * Q) 0 j = 0 := by
  sorry

private theorem coeff_X_mul_succ {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (Q : CBivariate R) (i j : Nat) :
    coeff (X * Q) (i + 1) j = coeff Q i j := by
  sorry

private theorem evalEval_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (P Q : CBivariate F) :
    evalEval x y (P - Q) = evalEval x y P - evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, evalEval_toPoly]
  have hsub : toPoly (P - Q) = toPoly P - toPoly Q := by
    simpa [ringEquiv] using (ringEquiv (R := F)).map_sub P Q
  rw [hsub]
  simp [Polynomial.evalEval]

private theorem evalEval_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c x y : F) (Q : CBivariate F) :
    evalEval x y (CC c * Q) = c * evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, toPoly_mul, CC_toPoly]
  simp [Polynomial.evalEval]

private theorem evalEval_X_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (Q : CBivariate F) :
    evalEval x y (X * Q) = x * evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, toPoly_mul, X_toPoly]
  simp [Polynomial.evalEval]

private theorem hasseDerivative_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (P Q : CBivariate F) :
    hasseDerivative a b (P - Q) =
      hasseDerivative a b P - hasseDerivative a b Q := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff, coeff_sub, coeff_sub, hasseDerivative_coeff,
    hasseDerivative_coeff]
  ring

private theorem hasseDerivative_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (a b : Nat) (Q : CBivariate F) :
    hasseDerivative a b (CC c * Q) = CC c * hasseDerivative a b Q := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff, coeff_CC_mul, coeff_CC_mul, hasseDerivative_coeff]
  ring

private theorem hasseDerivative_X_mul_zero_xOrder {F : Type*}
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
      change coeff (hasseDerivative 0 b (X * Q)) (i + 1) j =
        coeff (X * hasseDerivative 0 b Q) (i + 1) j
      rw [hasseDerivative_coeff, coeff_X_mul_succ, coeff_X_mul_succ,
        hasseDerivative_coeff]
      simp

private theorem hasseDerivative_X_mul_succ_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (Q : CBivariate F) :
    hasseDerivative (a + 1) b (X * Q) =
      X * hasseDerivative (a + 1) b Q + hasseDerivative a b Q := by
  sorry

private theorem hasseDerivativeEval_sub {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (x y : F) (P Q : CBivariate F) :
    hasseDerivativeEval a b x y (P - Q) =
      hasseDerivativeEval a b x y P - hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (P - Q)]
  rw [hasseDerivative_sub]
  rw [evalEval_sub]
  rw [hasseDerivative_eval_eq_eval, hasseDerivative_eval_eq_eval]

private theorem hasseDerivativeEval_CC_mul {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (a b : Nat) (x y : F) (Q : CBivariate F) :
    hasseDerivativeEval a b x y (CC c * Q) =
      c * hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (CC c * Q)]
  rw [hasseDerivative_CC_mul]
  rw [evalEval_CC_mul]
  rw [hasseDerivative_eval_eq_eval]

private theorem hasseDerivativeEval_X_mul_zero_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (b : Nat) (x y : F) (Q : CBivariate F) :
    hasseDerivativeEval 0 b x y (X * Q) =
      x * hasseDerivativeEval 0 b x y Q := by
  rw [← hasseDerivative_eval_eq_eval 0 b x y (X * Q)]
  rw [hasseDerivative_X_mul_zero_xOrder]
  rw [evalEval_X_mul]
  rw [hasseDerivative_eval_eq_eval]

private theorem hasseDerivativeEval_X_mul_succ_xOrder {F : Type*}
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

private theorem hasseDerivativeEval_linearXFactor_mul_zero_xOrder_general {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (c : F) (b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval 0 b x y (linearXFactor c * Q) =
      (x - c) * CompPoly.CBivariate.hasseDerivativeEval 0 b x y Q := by
  unfold linearXFactor
  rw [sub_mul, CompPoly.CBivariate.hasseDerivativeEval_sub,
    CompPoly.CBivariate.hasseDerivativeEval_X_mul_zero_xOrder,
    CompPoly.CBivariate.hasseDerivativeEval_CC_mul]
  ring

private theorem hasseDerivativeEval_linearXFactor_mul_succ_xOrder_general {F : Type*}
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

private theorem hasseDerivativeEval_linearXFactor_mul_zero_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval 0 b x y (linearXFactor x * Q) = 0 := by
  rw [hasseDerivativeEval_linearXFactor_mul_zero_xOrder_general]
  ring

private theorem hasseDerivativeEval_linearXFactor_mul_succ_xOrder {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (a b : Nat) (x y : F) (Q : CompPoly.CBivariate F) :
    CompPoly.CBivariate.hasseDerivativeEval (a + 1) b x y (linearXFactor x * Q) =
      CompPoly.CBivariate.hasseDerivativeEval a b x y Q := by
  rw [hasseDerivativeEval_linearXFactor_mul_succ_xOrder_general]
  ring

end CBivariate

/-- The initial direct Koetter basis has one entry for each `Y` exponent up to the cap. -/
theorem koetterInitialBasis_size {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) :
    (koetterInitialBasis (F := F) params).size = koetterYCap params + 1 := by
  unfold koetterInitialBasis
  simp

private theorem derivativeOrders_mem_of_lt {a b m : Nat} (h : a + b < m) :
    (a, b) ∈ (CBivariate.derivativeOrders m).toList := by
  unfold CBivariate.derivativeOrders CBivariate.derivativeOrderGrid
  simp [h]
  constructor <;> omega

private theorem multiplicityAtLeast_of_bool {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {x y : F} {m : Nat}
    (h : CBivariate.multiplicityAtLeastBool Q x y m = true) :
    CBivariate.HasMultiplicityAtLeast Q x y m := by
  intro a b hab
  unfold CBivariate.multiplicityAtLeastBool at h
  have hmemList : (a, b) ∈ (CBivariate.derivativeOrders m).toList :=
    derivativeOrders_mem_of_lt hab
  have hmem : (a, b) ∈ CBivariate.derivativeOrders m := Array.mem_def.mpr hmemList
  simpa using (Array.all_eq_true'.mp h (a, b) hmem)

private theorem satisfiesMultiplicityConstraints_of_bool {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {points : Array (F × F)} {m : Nat}
    (h : CBivariate.satisfiesMultiplicityConstraintsBool Q points m = true) :
    CBivariate.SatisfiesMultiplicityConstraints Q points m := by
  intro point hpointList
  unfold CBivariate.satisfiesMultiplicityConstraintsBool at h
  have hpoint : point ∈ points := Array.mem_def.mpr hpointList
  have hpointAll := Array.all_eq_true'.mp h point hpoint
  exact multiplicityAtLeast_of_bool hpointAll

private theorem derivativeOrders_lt_of_mem {m : Nat} {order : Nat × Nat}
    (h : order ∈ CBivariate.derivativeOrders m) :
    order.1 + order.2 < m := by
  have hList : order ∈ (CBivariate.derivativeOrders m).toList := Array.mem_def.mp h
  unfold CBivariate.derivativeOrders CBivariate.derivativeOrderGrid at hList
  simp at hList
  omega

private theorem multiplicityAtLeastBool_of_prop {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {x y : F} {m : Nat}
    (h : CBivariate.HasMultiplicityAtLeast Q x y m) :
    CBivariate.multiplicityAtLeastBool Q x y m = true := by
  unfold CBivariate.multiplicityAtLeastBool
  apply Array.all_eq_true'.mpr
  intro order horder
  rcases order with ⟨a, b⟩
  have hab : a + b < m := derivativeOrders_lt_of_mem horder
  simp [h a b hab]

private theorem satisfiesMultiplicityConstraintsBool_of_prop {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {points : Array (F × F)} {m : Nat}
    (h : CBivariate.SatisfiesMultiplicityConstraints Q points m) :
    CBivariate.satisfiesMultiplicityConstraintsBool Q points m = true := by
  unfold CBivariate.satisfiesMultiplicityConstraintsBool
  apply Array.all_eq_true'.mpr
  intro point hpoint
  exact multiplicityAtLeastBool_of_prop (h point (Array.mem_def.mp hpoint))

/-- The executable Koetter witness recognizer implies the semantic witness contract. -/
theorem koetterWitnessIsValidBool_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : koetterWitnessIsValidBool points params Q = true) :
    ValidInterpolationWitness points params Q := by
  unfold koetterWitnessIsValidBool at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨hhead, hmultBool⟩
  rw [Bool.and_eq_true] at hhead
  rcases hhead with ⟨hneBool, hdegBool⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    subst Q
    simp at hneBool
  · exact of_decide_eq_true hdegBool
  · exact satisfiesMultiplicityConstraints_of_bool hmultBool

private theorem koetterWitnessIsValidBool_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : ValidInterpolationWitness points params Q) :
    koetterWitnessIsValidBool points params Q = true := by
  rcases h with ⟨hne, hdeg, hmult⟩
  unfold koetterWitnessIsValidBool
  have hneBool : (Q == 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact hne
  simp [hneBool, hdeg, satisfiesMultiplicityConstraintsBool_of_prop hmult]

/-- Soundness for a checked raw direct Koetter interpolation result. -/
theorem koetterCheckedRawInterpolate_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : koetterCheckedRawInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold koetterCheckedRawInterpolate at h
  cases hraw : koetterRawInterpolate points params with
  | none =>
      simp [hraw] at h
  | some rawQ =>
      by_cases hvalid : koetterWitnessIsValidBool points params rawQ = true
      · simp [hraw, hvalid] at h
        cases h
        exact koetterWitnessIsValidBool_sound hvalid
      · simp [hraw, hvalid] at h

/-- Soundness for any polynomial returned by direct Koetter interpolation. -/
theorem koetterInterpolate_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : koetterInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold koetterInterpolate at h
  by_cases hLow : params.messageDegree ≤ 1
  · simp [hLow] at h
    cases h
    simpa using lowMessageDegreeInterpolation_sound (points := points)
      (params := params) hLow
  · simp [hLow] at h
    exact koetterCheckedRawInterpolate_sound h

private theorem koetterSelectFinal?_some_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    Q ≠ 0 := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => basis.getD pivot.index 0 ≠ 0
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  have hstep : ∀ best idx, good best → good (step best idx) := by
    intro best idx hbest
    unfold good step
    by_cases hzero : basis.getD idx 0 = 0
    · have hzero' : basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best <;> simpa [good, hzero', Array.getD_eq_getD_getElem?] using hbest
    · cases best with
      | none =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          simpa [good, hzero', Array.getD_eq_getD_getElem?]
      | some current =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [good, hzero', hbetter', Array.getD_eq_getD_getElem?]
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [good, hzero', hbetter', Array.getD_eq_getD_getElem?] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best, good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hbest
        simp only [List.foldl_cons]
        exact ih (step best idx) (hstep best idx hbest)
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    exact hfoldGoodAux (List.range basis.size) none (by simp [good])
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      have hpivotGood : basis.getD pivot.index 0 ≠ 0 := by
        simpa [hbest, good] using hfoldGood
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest, hdeg] at h
        rcases h with ⟨_, hQ⟩
        have hpivotGood' : basis[pivot.index]?.getD 0 ≠ 0 := by
          simpa [Array.getD_eq_getD_getElem?] using hpivotGood
        simpa [hQ] using hpivotGood'
      · simp [hbest, hdeg] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

private theorem koetterSelectFinal?_some_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest, hdeg] at h
        rcases h with ⟨hdeg', hQ⟩
        simpa [hQ, Array.getD_eq_getD_getElem?] using hdeg'
      · simp [hbest, hdeg] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

private theorem koetterSelectFinal?_some_entry {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    ∃ idx, Q = basis.getD idx 0 := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest, hdeg] at h
        rcases h with ⟨_, hQ⟩
        refine ⟨pivot.index, ?_⟩
        simpa [hQ, Array.getD_eq_getD_getElem?]
      · simp [hbest, hdeg] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

private theorem koetterSelectFinal?_some_entry_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    ∃ idx, idx < basis.size ∧ Q = basis.getD idx 0 := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => pivot.index < basis.size
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  have hstep : ∀ best idx, idx ∈ List.range basis.size → good best → good (step best idx) := by
    intro best idx hidxMem hbest
    have hidx : idx < basis.size := by
      simpa using hidxMem
    unfold good step
    by_cases hzero : basis.getD idx 0 = 0
    · have hzero' : basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      simpa [hzero'] using hbest
    · cases best with
      | none =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          simpa [hzero'] using hidx
      | some current =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hidx
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best,
      (∀ idx, idx ∈ xs → idx < basis.size) → good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best _ hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hxs hbest
        simp only [List.foldl_cons]
        apply ih
        · intro j hj
          exact hxs j (by simp [hj])
        · exact hstep best idx (by simpa using hxs idx (by simp)) hbest
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    apply hfoldGoodAux (List.range basis.size) none
    · intro idx hidx
      simpa using hidx
    · simp [good]
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      have hpivotLt : pivot.index < basis.size := by
        simpa [hbest, good] using hfoldGood
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest, hdeg] at h
        rcases h with ⟨_, hQ⟩
        refine ⟨pivot.index, hpivotLt, ?_⟩
        simpa [hQ, Array.getD_eq_getD_getElem?]
      · simp [hbest, hdeg] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

private theorem koetterPivotBetter_weightedDegree_le {F : Type*}
    {candidate current : KoetterPivot F}
    (h : koetterPivotBetter candidate current = true) :
    candidate.weightedDegree ≤ current.weightedDegree := by
  unfold koetterPivotBetter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

private theorem koetterPivotBetter_not_weightedDegree_le {F : Type*}
    {candidate current : KoetterPivot F}
    (h : ¬ koetterPivotBetter candidate current = true) :
    current.weightedDegree ≤ candidate.weightedDegree := by
  unfold koetterPivotBetter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    not_and] at h
  omega

private theorem koetterSelectFinal?_some_of_exists_entry {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)}
    (hExists : ∃ idx, idx < basis.size ∧ basis.getD idx 0 ≠ 0 ∧
      CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) ≤
        params.weightedDegreeBound) :
    ∃ Q, koetterSelectFinal? params basis = some Q := by
  unfold koetterSelectFinal?
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change ∃ Q,
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q
  let degree : Nat → Nat := fun idx ↦
    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params)
  let wellBest : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => pivot.weightedDegree = degree pivot.index
  let boundedBest : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => False
    | some pivot =>
        pivot.weightedDegree = degree pivot.index ∧
          pivot.weightedDegree ≤ params.weightedDegreeBound
  let boundedEntry : Nat → Prop := fun idx ↦
    basis.getD idx 0 ≠ 0 ∧ degree idx ≤ params.weightedDegreeBound
  have hstep_well : ∀ best idx, wellBest best → wellBest (step best idx) := by
    intro best idx hbest
    unfold wellBest step degree at *
    by_cases hzero : basis.getD idx 0 = 0
    · have hzero' : basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best <;> simpa [hzero'] using hbest
    · have hzero' : ¬basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none =>
          simp [hzero', Array.getD_eq_getD_getElem?]
      | some current =>
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hstep_bounded_preserve : ∀ best idx, boundedBest best → boundedBest (step best idx) := by
    intro best idx hbest
    unfold boundedBest step degree at *
    by_cases hzero : basis.getD idx 0 = 0
    · have hzero' : basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best <;> simpa [hzero'] using hbest
    · have hzero' : ¬basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none => contradiction
      | some current =>
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            have hle := koetterPivotBetter_weightedDegree_le hbetter
            have hbound :
                CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) ≤
                  params.weightedDegreeBound := by
              have hboundGetD :
                  CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) ≤
                    params.weightedDegreeBound :=
                le_trans hle hbest.2
              simpa [Array.getD_eq_getD_getElem?] using hboundGetD
            simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
            exact hbound
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hstep_of_entry : ∀ best idx, wellBest best → boundedEntry idx →
      boundedBest (step best idx) := by
    intro best idx hwell hentry
    rcases hentry with ⟨hne, hbound⟩
    unfold wellBest boundedBest step degree at *
    have hzero' : ¬basis[idx]?.getD 0 = 0 := by
      simpa [Array.getD_eq_getD_getElem?] using hne
    have hbound' : CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
        (yWeight params) ≤ params.weightedDegreeBound := by
      simpa [Array.getD_eq_getD_getElem?] using hbound
    cases best with
    | none =>
        simp [hzero', Array.getD_eq_getD_getElem?]
        exact hbound'
    | some current =>
        by_cases hbetter :
            koetterPivotBetter
              ({ index := idx
                 discrepancy := 0
                 weightedDegree :=
                  CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                KoetterPivot F)
              current = true
        · have hbetter' :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true := by
            simpa [Array.getD_eq_getD_getElem?] using hbetter
          simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
          exact hbound'
        · have hbetter' :
              ¬koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true := by
            simpa [Array.getD_eq_getD_getElem?] using hbetter
          have hcurrentLe := koetterPivotBetter_not_weightedDegree_le hbetter
          have hcurrentBound : current.weightedDegree ≤ params.weightedDegreeBound :=
            le_trans hcurrentLe hbound
          simpa [hzero', hbetter'] using (And.intro hwell hcurrentBound)
  have hfold : ∀ (xs : List Nat) best,
      wellBest best →
      boundedBest best ∨ (∃ idx, idx ∈ xs ∧ boundedEntry idx) →
        boundedBest (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best _hwell h
        rcases h with hbest | hmem
        · simpa using hbest
        · rcases hmem with ⟨idx, hidx, _⟩
          simp at hidx
    | cons idx xs ih =>
        intro best hwell h
        simp only [List.foldl_cons]
        apply ih
        · exact hstep_well best idx hwell
        · rcases h with hbest | hmem
          · exact Or.inl (hstep_bounded_preserve best idx hbest)
          · rcases hmem with ⟨j, hj, hentry⟩
            simp at hj
            rcases hj with hji | hjxs
            · subst j
              exact Or.inl (hstep_of_entry best idx hwell hentry)
            · exact Or.inr ⟨j, hjxs, hentry⟩
  rcases hExists with ⟨idx, hidx, hne, hbound⟩
  have hbestBounded : boundedBest ((List.range basis.size).foldl step none) := by
    apply hfold
    · simp [wellBest]
    · exact Or.inr ⟨idx, by simpa using hidx, hne, hbound⟩
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest, boundedBest] at hbestBounded
  | some pivot =>
      refine ⟨basis.getD pivot.index 0, ?_⟩
      have hdeg' : CBivariate.natWeightedDegree (basis[pivot.index]?.getD 0) 1
          (yWeight params) ≤ params.weightedDegreeBound := by
        have hp := hbestBounded
        simp [hbest, boundedBest, degree, Array.getD_eq_getD_getElem?] at hp
        rw [← hp.1]
        exact hp.2
      simp [hdeg']

private theorem koetterSelectPivot_some_discrepancy {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    pivot.discrepancy = koetterDiscrepancy constraint (basis.getD pivot.index 0) ∧
      pivot.discrepancy ≠ 0 := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot =>
        pivot.discrepancy = koetterDiscrepancy constraint (basis.getD pivot.index 0) ∧
          pivot.discrepancy ≠ 0
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best idx, good best → good (step best idx) := by
    intro best idx hbest
    unfold good step
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best <;> simpa [good, hzero', Array.getD_eq_getD_getElem?] using hbest
    · have hne : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := by
        exact hzero
      cases best with
      | none =>
          have hne' : koetterDiscrepancy constraint (basis[idx]?.getD 0) ≠ 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hne
          simp [good, hne']
      | some current =>
          have hne' : koetterDiscrepancy constraint (basis[idx]?.getD 0) ≠ 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hne
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [good, hne', hbetter']
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [good, hbetter', Array.getD_eq_getD_getElem?] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best, good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hbest
        simp only [List.foldl_cons]
        exact ih (step best idx) (hstep best idx hbest)
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    exact hfoldGoodAux (List.range basis.size) none (by simp [good])
  simpa [h, good] using hfoldGood

private theorem koetterSelectPivot_some_index_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    pivot.index < basis.size := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => pivot.index < basis.size
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best idx, idx ∈ List.range basis.size → good best → good (step best idx) := by
    intro best idx hidxMem hbest
    have hidx : idx < basis.size := by
      simpa using hidxMem
    unfold good step
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      simpa [hzero'] using hbest
    · cases best with
      | none =>
          have hzero' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          simpa [hzero'] using hidx
      | some current =>
          have hzero' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hidx
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best,
      (∀ idx, idx ∈ xs → idx < basis.size) → good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best _hxs hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hxs hbest
        simp only [List.foldl_cons]
        apply ih
        · intro j hj
          exact hxs j (by simp [hj])
        · exact hstep best idx (by simpa using hxs idx (by simp)) hbest
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    apply hfoldGoodAux (List.range basis.size) none
    · intro idx hidx
      simpa using hidx
    · simp [good]
  simpa [h, good] using hfoldGood

private theorem koetterSelectPivot_none_discrepancy_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)}
    (h : koetterSelectPivot params constraint basis = none) :
    ∀ idx, idx < basis.size → koetterDiscrepancy constraint (basis.getD idx 0) = 0 := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change (List.range basis.size).foldl step none = none at h
  have hstepNone : ∀ best idx, step best idx = none →
      best = none ∧ koetterDiscrepancy constraint (basis.getD idx 0) = 0 := by
    intro best idx hstep
    unfold step at hstep
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none => exact ⟨rfl, hzero⟩
      | some _current =>
          simp [hzero'] at hstep
    · have hzero' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none =>
          simp [hzero'] at hstep
      | some current =>
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                      (yWeight params) } :
                  KoetterPivot F)
                current = true
          · simp [hzero', hbetter] at hstep
          · simp [hzero', hbetter] at hstep
  have hfoldNoneAux : ∀ (xs : List Nat) best, xs.foldl step best = none →
      best = none ∧
        ∀ idx, idx ∈ xs → koetterDiscrepancy constraint (basis.getD idx 0) = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro best hfold
        exact ⟨hfold, by simp⟩
    | cons idx xs ih =>
        intro best hfold
        simp only [List.foldl_cons] at hfold
        rcases ih (step best idx) hfold with ⟨hstepEq, hxs⟩
        rcases hstepNone best idx hstepEq with ⟨hbest, hidxZero⟩
        refine ⟨hbest, ?_⟩
        intro j hj
        simp at hj
        cases hj with
        | inl hji =>
            subst j
            exact hidxZero
        | inr htail =>
            exact hxs j htail
  have hall := (hfoldNoneAux (List.range basis.size) none h).2
  intro idx hi
  exact hall idx (by simpa using hi)

private theorem koetterUpdatedEntry_satisfies_current {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) (idx : Nat)
    (hPivotDisc : pivot.discrepancy = koetterDiscrepancy constraint (basis.getD pivot.index 0))
    (hPivotNe : pivot.discrepancy ≠ 0)
    (hLower : ∀ a, constraint.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
        (basis.getD pivot.index 0) = 0) :
    koetterDiscrepancy constraint
      (koetterUpdatedEntry constraint basis pivot idx) = 0 := by
  unfold koetterUpdatedEntry koetterDiscrepancy
  by_cases hidx : idx == pivot.index
  · have hidxEq : idx = pivot.index := beq_iff_eq.mp hidx
    rw [if_pos hidx]
    subst idx
    cases hx : constraint.xOrder with
    | zero =>
        rw [CBivariate.hasseDerivativeEval_linearXFactor_mul_zero_xOrder]
    | succ a =>
        rw [CBivariate.hasseDerivativeEval_linearXFactor_mul_succ_xOrder]
        exact hLower a hx
  · rw [if_neg hidx]
    by_cases hdelta : CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder
        constraint.x constraint.y (basis.getD idx 0) == 0
    · rw [if_pos hdelta]
      exact beq_iff_eq.mp hdelta
    · rw [if_neg hdelta]
      rw [CBivariate.hasseDerivativeEval_sub]
      rw [CBivariate.hasseDerivativeEval_CC_mul]
      rw [hPivotDisc]
      change
        CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
              constraint.y (basis.getD idx 0) -
            CBivariate.hasseDerivativeEval constraint.xOrder constraint.yOrder constraint.x
                constraint.y (basis.getD idx 0) /
              koetterDiscrepancy constraint (basis.getD pivot.index 0) *
                koetterDiscrepancy constraint (basis.getD pivot.index 0) =
          0
      rw [div_mul_cancel₀]
      · ring
      · rw [← hPivotDisc]
        exact hPivotNe

private theorem koetterUpdatedEntry_preserves_prior {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (current prior : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) {idx : Nat} (hi : idx < basis.size)
    (hpivot : pivot.index < basis.size)
    (hPrior : ∀ k, k < basis.size → koetterDiscrepancy prior (basis.getD k 0) = 0)
    (hPriorLower : ∀ k, k < basis.size → ∀ a, prior.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a prior.yOrder prior.x prior.y (basis.getD k 0) = 0) :
    koetterDiscrepancy prior (koetterUpdatedEntry current basis pivot idx) = 0 := by
  sorry

private theorem foldl_setIfInBounds_size {α : Type*}
    (f : Nat → α) (xs : List Nat) (arr : Array α) :
    (xs.foldl (fun out idx ↦ out.setIfInBounds idx (f idx)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons idx xs ih =>
      simp [List.foldl_cons, ih, Array.size_setIfInBounds]

private theorem foldl_range_setIfInBounds_getD_of_lt_aux {α : Type*}
    (f : Nat → α) (arr : Array α) (d : α) :
    ∀ n, n ≤ arr.size → ∀ idx, idx < n →
      ((List.range n).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).getD idx d =
        f idx := by
  intro n
  induction n with
  | zero =>
      intro _hle idx hi
      omega
  | succ n ih =>
      intro hle idx hi
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hidx : idx = n
      · subst idx
        have hprefixSize :
            ((List.range n).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).size =
              arr.size :=
          foldl_setIfInBounds_size f (List.range n) arr
        have hnlt : n <
            ((List.range n).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).size := by
          rw [hprefixSize]
          omega
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt hnlt]
        rfl
      · have hnidx : n ≠ idx := fun h ↦ hidx h.symm
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hnidx]
        simpa [Array.getD_eq_getD_getElem?] using ih (by omega) idx (by omega)

private theorem foldl_range_setIfInBounds_getD_of_lt {α : Type*}
    (f : Nat → α) (arr : Array α) (d : α) {idx : Nat} (hi : idx < arr.size) :
    ((List.range arr.size).foldl (fun out j ↦ out.setIfInBounds j (f j)) arr).getD idx d =
      f idx :=
  foldl_range_setIfInBounds_getD_of_lt_aux f arr d arr.size (by rfl) idx hi

private theorem koetterUpdateBasis_size {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) :
    (koetterUpdateBasis constraint basis pivot).size = basis.size := by
  unfold koetterUpdateBasis
  exact foldl_setIfInBounds_size
    (fun idx ↦ koetterUpdatedEntry constraint basis pivot idx) (List.range basis.size) basis

private theorem koetterUpdateBasis_getD_of_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (constraint : InterpolationConstraint F) (basis : Array (CBivariate F))
    (pivot : KoetterPivot F) {idx : Nat} (hi : idx < basis.size) :
    (koetterUpdateBasis constraint basis pivot).getD idx 0 =
      koetterUpdatedEntry constraint basis pivot idx := by
  unfold koetterUpdateBasis
  exact foldl_range_setIfInBounds_getD_of_lt
    (fun idx ↦ koetterUpdatedEntry constraint basis pivot idx) basis 0 hi

private theorem koetterProcessConstraint_satisfies_current {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (constraint : InterpolationConstraint F)
    (state : KoetterState F)
    (hLower : ∀ pivot, koetterSelectPivot params constraint state.basis = some pivot →
      ∀ a, constraint.xOrder = a + 1 →
        CBivariate.hasseDerivativeEval a constraint.yOrder constraint.x constraint.y
          (state.basis.getD pivot.index 0) = 0) :
    ∀ idx, idx < (koetterProcessConstraint params constraint state).basis.size →
      koetterDiscrepancy constraint
        ((koetterProcessConstraint params constraint state).basis.getD idx 0) = 0 := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params constraint state.basis with
  | none =>
      intro idx hi
      simp at hi ⊢
      simpa [Array.getD_eq_getD_getElem?] using
        koetterSelectPivot_none_discrepancy_zero hpivot idx hi
  | some pivot =>
      intro idx hi
      simp at hi ⊢
      have hsize := koetterUpdateBasis_size constraint state.basis pivot
      have hiOld : idx < state.basis.size := by
        simpa [hsize] using hi
      rw [← Array.getD_eq_getD_getElem?]
      rw [koetterUpdateBasis_getD_of_lt constraint state.basis pivot hiOld]
      rcases koetterSelectPivot_some_discrepancy hpivot with ⟨hdisc, hne⟩
      exact koetterUpdatedEntry_satisfies_current constraint state.basis pivot idx hdisc hne
        (hLower pivot hpivot)

private theorem koetterProcessConstraint_preserves_prior {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (current prior : InterpolationConstraint F)
    (state : KoetterState F)
    (hPrior : ∀ idx, idx < state.basis.size →
      koetterDiscrepancy prior (state.basis.getD idx 0) = 0)
    (hPriorLower : ∀ idx, idx < state.basis.size → ∀ a, prior.xOrder = a + 1 →
      CBivariate.hasseDerivativeEval a prior.yOrder prior.x prior.y
        (state.basis.getD idx 0) = 0) :
    ∀ idx, idx < (koetterProcessConstraint params current state).basis.size →
      koetterDiscrepancy prior
        ((koetterProcessConstraint params current state).basis.getD idx 0) = 0 := by
  unfold koetterProcessConstraint
  cases hpivot : koetterSelectPivot params current state.basis with
  | none =>
      intro idx hi
      simp at hi ⊢
      simpa [Array.getD_eq_getD_getElem?] using hPrior idx hi
  | some pivot =>
      intro idx hi
      simp at hi ⊢
      have hsize := koetterUpdateBasis_size current state.basis pivot
      have hiOld : idx < state.basis.size := by
        simpa [hsize] using hi
      rw [← Array.getD_eq_getD_getElem?]
      rw [koetterUpdateBasis_getD_of_lt current state.basis pivot hiOld]
      exact koetterUpdatedEntry_preserves_prior current prior state.basis pivot hiOld
        (koetterSelectPivot_some_index_lt hpivot) hPrior hPriorLower

private def lowerXConstraint {F : Type*} (constraint : InterpolationConstraint F) (a : Nat) :
    InterpolationConstraint F :=
  { x := constraint.x, y := constraint.y, xOrder := a, yOrder := constraint.yOrder }

private def koetterBasisSatisfiesConstraints {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (basis : Array (CBivariate F)) (constraints : List (InterpolationConstraint F)) : Prop :=
  ∀ constraint, constraint ∈ constraints → ∀ idx, idx < basis.size →
    koetterDiscrepancy constraint (basis.getD idx (0 : CBivariate F)) = 0

private def koetterConstraintsLowerClosed {F : Type*}
    (constraints : List (InterpolationConstraint F)) : Prop :=
  ∀ constraint, constraint ∈ constraints → ∀ a,
    constraint.xOrder = a + 1 → lowerXConstraint constraint a ∈ constraints

private def koetterConstraintLowerIn {F : Type*}
    (processed : List (InterpolationConstraint F)) (constraint : InterpolationConstraint F) :
    Prop :=
  ∀ a, constraint.xOrder = a + 1 → lowerXConstraint constraint a ∈ processed

private def koetterConstraintsLowerBefore {F : Type*}
    (constraints : List (InterpolationConstraint F)) : Prop :=
  ∀ pre current post a, constraints = pre ++ current :: post →
    current.xOrder = a + 1 → lowerXConstraint current a ∈ pre

private theorem foldl_append_toArray_toList {α β : Type*}
    (chunk : β → List α) :
    ∀ (xs : List β) (acc : Array α),
      (xs.foldl (fun out x ↦ out ++ (chunk x).toArray) acc).toList =
        acc.toList ++ xs.flatMap chunk := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [List.append_assoc]

private theorem array_foldl_append_toArray_toList {α β : Type*}
    (chunk : β → List α) (xs : Array β) (acc : Array α) :
    (xs.foldl (fun out x ↦ out ++ (chunk x).toArray) acc).toList =
      acc.toList ++ xs.toList.flatMap chunk := by
  simpa using foldl_append_toArray_toList chunk xs.toList acc

private theorem array_eq_of_toList {α : Type*} {a b : Array α} (h : a.toList = b.toList) :
    a = b := by
  simpa using congrArg List.toArray h

private def interpolationConstraintsList {F : Type*}
    (points : Array (F × F)) (multiplicity : Nat) : List (InterpolationConstraint F) :=
  points.toList.flatMap fun point =>
    (List.range multiplicity).flatMap fun a =>
      (List.range (multiplicity - a)).map fun b =>
        ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
          InterpolationConstraint F)

private theorem interpolationConstraintsPointStep_eq_append {F : Type*}
    (point : F × F) (multiplicity : Nat) (acc : Array (InterpolationConstraint F)) :
    (List.range multiplicity).foldl
      (fun out a ↦
        out ++ ((List.range (multiplicity - a)).map fun b ↦
          ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
            InterpolationConstraint F)).toArray)
      acc =
    acc ++ ((List.range multiplicity).flatMap fun a ↦
      (List.range (multiplicity - a)).map fun b ↦
        ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
          InterpolationConstraint F)).toArray := by
  apply array_eq_of_toList
  rw [foldl_append_toArray_toList]
  simp [List.append_assoc]

private theorem interpolationConstraints_toList_eq_list {F : Type*}
    (points : Array (F × F)) (multiplicity : Nat) :
    (interpolationConstraints points multiplicity).toList =
      interpolationConstraintsList points multiplicity := by
  unfold interpolationConstraints interpolationConstraintsList
  simp
  have hrange : ∀ n, List.range' 0 n = List.range n := by
    intro n
    exact (List.range_eq_range' (n := n)).symm
  simp [hrange]
  rw [show
      (fun b (a : F × F) ↦
        List.foldl
          (fun b a_1 ↦
            b ++ (List.map (InterpolationConstraint.mk a.1 a.2 a_1)
              (List.range (multiplicity - a_1))).toArray)
          b (List.range multiplicity)) =
      (fun b point ↦
        b ++ ((List.range multiplicity).flatMap fun a ↦
          (List.range (multiplicity - a)).map fun b ↦
            ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
              InterpolationConstraint F)).toArray) by
    funext b point
    exact interpolationConstraintsPointStep_eq_append point multiplicity b]
  rw [array_foldl_append_toArray_toList]
  simp

private theorem interpolationConstraintsList_lowerBefore {F : Type*}
    (points : Array (F × F)) (multiplicity : Nat) :
    koetterConstraintsLowerBefore (interpolationConstraintsList points multiplicity) := by
  sorry

private theorem koetterProcessConstraint_satisfies_cons {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (current : InterpolationConstraint F)
    (state : KoetterState F) (processed : List (InterpolationConstraint F))
    (hSat : koetterBasisSatisfiesConstraints state.basis processed)
    (hClosed : koetterConstraintsLowerClosed processed)
    (hCurrentLower : koetterConstraintLowerIn processed current) :
    koetterBasisSatisfiesConstraints
      (koetterProcessConstraint params current state).basis (current :: processed) := by
  intro constraint hconstraint idx hi
  simp at hconstraint
  cases hconstraint with
  | inl hcur =>
      subst constraint
      apply koetterProcessConstraint_satisfies_current
      intro pivot hpivot a ha
      exact hSat (lowerXConstraint current a) (hCurrentLower a ha) pivot.index
        (koetterSelectPivot_some_index_lt hpivot)
      exact hi
  | inr hprior =>
      apply koetterProcessConstraint_preserves_prior
      · intro k hk
        exact hSat constraint hprior k hk
      · intro k hk a ha
        exact hSat (lowerXConstraint constraint a) (hClosed constraint hprior a ha) k hk
      · exact hi

private theorem koetterConstraintLowerIn_of_before {F : Type*}
    {original processed remaining : List (InterpolationConstraint F)}
    {current : InterpolationConstraint F}
    (hsplit : processed.reverse ++ current :: remaining = original)
    (hbefore : koetterConstraintsLowerBefore original) :
    koetterConstraintLowerIn processed current := by
  intro a ha
  have hlowerRev : lowerXConstraint current a ∈ processed.reverse := by
    exact hbefore processed.reverse current remaining a hsplit.symm ha
  simpa [List.mem_reverse] using hlowerRev

private theorem koetterConstraintsLowerClosed_cons_of_before {F : Type*}
    {original processed remaining : List (InterpolationConstraint F)}
    {current : InterpolationConstraint F}
    (hsplit : processed.reverse ++ current :: remaining = original)
    (hbefore : koetterConstraintsLowerBefore original)
    (hClosed : koetterConstraintsLowerClosed processed) :
    koetterConstraintsLowerClosed (current :: processed) := by
  intro constraint hmem a ha
  simp at hmem
  cases hmem with
  | inl hcur =>
      subst constraint
      have hlowerRev : lowerXConstraint current a ∈ processed.reverse := by
        exact hbefore processed.reverse current remaining a hsplit.symm ha
      simp [List.mem_reverse] at hlowerRev
      simp [hlowerRev]
  | inr hprocessed =>
      have hlower := hClosed constraint hprocessed a ha
      simp [hlower]

private theorem koetterProcessConstraints_fold_satisfies {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (original : List (InterpolationConstraint F))
    (hbefore : koetterConstraintsLowerBefore original) :
    ∀ remaining processed state,
      processed.reverse ++ remaining = original →
      koetterBasisSatisfiesConstraints state.basis processed →
      koetterConstraintsLowerClosed processed →
      koetterBasisSatisfiesConstraints
        (remaining.foldl (fun state constraint ↦ koetterProcessConstraint params constraint state)
          state).basis original := by
  intro remaining
  induction remaining with
  | nil =>
      intro processed state hsplit hSat _hClosed
      intro constraint hmem idx hi
      have hmemProcessed : constraint ∈ processed := by
        have : constraint ∈ processed.reverse := by
          simpa [hsplit.symm] using hmem
        simpa [List.mem_reverse] using this
      exact hSat constraint hmemProcessed idx hi
  | cons current remaining ih =>
      intro processed state hsplit hSat hClosed
      simp only [List.foldl_cons]
      apply ih (current :: processed) (koetterProcessConstraint params current state)
      · rw [List.reverse_cons, List.append_assoc]
        simpa using hsplit
      · exact koetterProcessConstraint_satisfies_cons params current state processed hSat hClosed
          (koetterConstraintLowerIn_of_before hsplit hbefore)
      · exact koetterConstraintsLowerClosed_cons_of_before hsplit hbefore hClosed

private theorem koetterRawInterpolate_sound_of_lowerBefore {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hbefore : koetterConstraintsLowerBefore
      (interpolationConstraints points params.multiplicity).toList)
    (h : koetterRawInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold koetterRawInterpolate at h
  let constraints := interpolationConstraints points params.multiplicity
  let initial := koetterInitialState (F := F) params
  let finalState := koetterProcessConstraints params constraints initial
  have hselect : koetterSelectFinal? params finalState.basis = some Q := by
    simpa [constraints, initial, finalState, koetterProcessConstraints] using h
  have hne := koetterSelectFinal?_some_ne_zero hselect
  have hdeg := koetterSelectFinal?_some_weightedDegree_le hselect
  rcases koetterSelectFinal?_some_entry_lt hselect with ⟨idx, hidx, hQidx⟩
  refine ⟨hne, hdeg, ?_⟩
  intro point hpoint a b hab
  have hconstraintMem :
      ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
        InterpolationConstraint F) ∈ constraints.toList := by
    rw [interpolationConstraints_toList_eq_list]
    unfold interpolationConstraintsList
    apply List.mem_flatMap.mpr
    refine ⟨point, hpoint, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨a, by simpa using (show a < params.multiplicity by omega), ?_⟩
    apply List.mem_map.mpr
    refine ⟨b, ?_, rfl⟩
    simpa using (show b < params.multiplicity - a by omega)
  have hSat := koetterProcessConstraints_fold_satisfies params constraints.toList hbefore
    constraints.toList [] initial (by simp)
    (by intro c hc; simp at hc)
    (by intro c hc; simp at hc)
  have hSatFinal : koetterBasisSatisfiesConstraints finalState.basis constraints.toList := by
    simpa [finalState, koetterProcessConstraints] using hSat
  rw [hQidx]
  exact hSatFinal ({ x := point.1, y := point.2, xOrder := a, yOrder := b })
    hconstraintMem idx hidx

/-- Raw positive-message Koetter soundness proof obligation.

This is the direct module-invariant statement: after all Hasse constraints are
processed, any selected raw Koetter polynomial is already a valid interpolation
witness. -/
theorem koetterRawInterpolate_sound_of_messageDegree_gt_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (_hMessage : ¬ params.messageDegree ≤ 1)
    (h : koetterRawInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  have hbefore :
      koetterConstraintsLowerBefore
        (interpolationConstraints points params.multiplicity).toList := by
    rw [interpolationConstraints_toList_eq_list]
    exact interpolationConstraintsList_lowerBefore points params.multiplicity
  exact koetterRawInterpolate_sound_of_lowerBefore hbefore h

private theorem koetterRawInterpolate_some_of_exists_final_entry {F : Type*}
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

/-- Raw positive-message Koetter completeness proof obligation.

This is the minimal-basis statement: if any valid witness exists in the finite
positive-`Y`-weight search space, the raw Koetter final selection returns one. -/
theorem koetterRawInterpolate_complete_of_messageDegree_gt_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    (hMessage : ¬ params.messageDegree ≤ 1) :
    (exists Q, ValidInterpolationWitness points params Q) →
      exists Q, koetterRawInterpolate points params = some Q := by
  intro hExists
  apply koetterRawInterpolate_some_of_exists_final_entry
  sorry

/-- Checked direct Koetter completeness proof obligation for the public
positive-message branch. -/
theorem koetterCheckedRawInterpolate_complete_of_messageDegree_gt_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    (hMessage : ¬ params.messageDegree ≤ 1) :
    (exists Q, ValidInterpolationWitness points params Q) →
      exists Q, koetterCheckedRawInterpolate points params = some Q := by
  intro hExists
  rcases koetterRawInterpolate_complete_of_messageDegree_gt_one
      (F := F) (points := points) (params := params) hMessage hExists with
    ⟨Q, hQ⟩
  have hWitness := koetterRawInterpolate_sound_of_messageDegree_gt_one
    (F := F) (points := points) (params := params) hMessage hQ
  refine ⟨Q, ?_⟩
  unfold koetterCheckedRawInterpolate
  simp [hQ, koetterWitnessIsValidBool_complete hWitness]

/-- Completeness for the public Koetter interpolation operation.

For positive message degree this is the direct Koetter completeness statement,
not a dense-backend fallback. -/
theorem koetterInterpolate_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} :
    (exists Q, ValidInterpolationWitness points params Q) →
      exists Q, koetterInterpolate points params = some Q := by
  intro hExists
  unfold koetterInterpolate
  by_cases hLow : params.messageDegree ≤ 1
  · refine ⟨lowMessageDegreeInterpolation points params.multiplicity, ?_⟩
    simp [hLow]
  · simp [hLow]
    exact koetterCheckedRawInterpolate_complete_of_messageDegree_gt_one
      (F := F) (points := points) (params := params) hLow hExists

/-- Public Koetter interpolation context.

The executable operation has no dense interpolation fallback. The positive-message
completeness field depends on the direct Koetter proof obligations above. -/
def koetterInterpContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] : GSInterpContext F where
  interpolate := koetterInterpolate
  sound := by
    intro points params Q h
    exact koetterInterpolate_sound h
  complete := by
    intro points params hExists
    exact koetterInterpolate_complete hExists

/-- Public Koetter interpolation backend soundness. -/
theorem koetterInterpContext_correct (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params Q,
      (koetterInterpContext F).interpolate points params = some Q →
        ValidInterpolationWitness points params Q :=
  (koetterInterpContext F).sound

/-- Public Koetter interpolation backend completeness. -/
theorem koetterInterpContext_complete (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [Nontrivial F] [DecidableEq F] :
    ∀ points params,
      (exists Q, ValidInterpolationWitness points params Q) →
        exists Q, (koetterInterpContext F).interpolate points params = some Q :=
  (koetterInterpContext F).complete

end GuruswamiSudan

end CompPoly
