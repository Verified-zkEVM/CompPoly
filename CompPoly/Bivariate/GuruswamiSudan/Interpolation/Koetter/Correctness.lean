/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Algorithm

/-!
# Koetter Interpolation Correctness

Soundness and completeness for the public Koetter interpolation operation. The
public operation tries the direct Koetter pass first, then falls back to the
certified dense interpolation backend when needed. The raw Koetter minimal-basis
completeness proof is intentionally kept separate from this certified boundary.
-/

namespace CompPoly

namespace GuruswamiSudan

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
    cases hraw : koetterCheckedRawInterpolate points params with
    | some rawQ =>
        simp [hraw] at h
        cases h
        exact koetterCheckedRawInterpolate_sound hraw
    | none =>
        simp [hraw] at h
        exact (denseInterpContext F).sound points params Q h

/-- Completeness for the public Koetter interpolation operation.

When the direct checked Koetter pass does not return a witness, this proof uses
the certified dense fallback. It does not claim the raw Koetter pass alone is
complete. -/
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
    cases hraw : koetterCheckedRawInterpolate points params with
    | some rawQ =>
        refine ⟨rawQ, ?_⟩
        simp
    | none =>
        rcases denseInterpolate_complete_of_messageDegree_gt_one
            (F := F) (points := points) (params := params) hLow hExists with
          ⟨Q, hQ⟩
        refine ⟨Q, ?_⟩
        simp [hQ]

/-- Certified public Koetter interpolation context.

The executable operation is Koetter-first with dense fallback; the context
therefore has the same semantic contract as `denseInterpContext`. -/
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

/-!
Raw `koetterRawInterpolate` minimal-basis completeness is not proved here. The
public context above is certified because `koetterInterpolate` has an explicit
dense fallback after the checked direct Koetter pass.
 -/

end GuruswamiSudan

end CompPoly
