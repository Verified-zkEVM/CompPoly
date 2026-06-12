/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.OddTrial
import CompPoly.Univariate.Roots.LasVegas.Probability.Recursive

/-!
# Repeated Odd Trials and Geometric Fallback Bounds

Independent repeated odd-field split trials for one unresolved factor, the
geometric bound on reaching enumeration fallback, and the one-factor witness of
the recursive fallback model. The `_of_uniformProbe` variants discharge the
per-trial half-success hypothesis from the actual uniform probe source.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Independent repeated odd-field split trials for one unresolved factor. -/
noncomputable def repeatedOddSplitTrialsPMF {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) :
    Nat → Nat → PMF (List (TrialResult F))
  | 0, _offset => pure []
  | attempts + 1, offset => do
      let trial ← oddSplitTrialPMF M D enumeration q coefficientCount g offset
      let trials ← repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
        (offset + 1)
      pure (trial :: trials)

/-- Probability that the one-factor loop reaches fallback after all split attempts fail. -/
noncomputable def fallbackAfterOddAttemptsProbability {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat) :
    ℝ≥0∞ :=
  eventProbability
    (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts offset)
    {trials | TrialResult.allFailed trials}

private theorem toOuterMeasure_map_cons_allFailed {F : Type*} [Zero F]
    (dist : PMF (List (TrialResult F))) (trial : TrialResult F) :
    (dist.map (List.cons trial)).toOuterMeasure {trials | TrialResult.allFailed trials} =
      if ¬ trial.IsSuccess then
        dist.toOuterMeasure {trials | TrialResult.allFailed trials}
      else
        0 := by
  cases trial <;>
    simp [PMF.toOuterMeasure_map_apply, TrialResult.IsSuccess, TrialResult.allFailed]

private theorem fallbackAfterOddAttemptsProbability_succ {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat) :
    fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g
        (attempts + 1) offset =
      eventProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g offset)
          {trial | ¬ trial.IsSuccess} *
        fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g
          attempts (offset + 1) := by
  change (PMF.bind (oddSplitTrialPMF M D enumeration q coefficientCount g offset)
      (fun trial ↦ PMF.map (List.cons trial)
        (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
          (offset + 1)))).toOuterMeasure
        {trials | TrialResult.allFailed trials} =
    (oddSplitTrialPMF M D enumeration q coefficientCount g offset).toOuterMeasure
      {trial | ¬ trial.IsSuccess} *
      (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
        (offset + 1)).toOuterMeasure
        {trials | TrialResult.allFailed trials}
  rw [PMF.toOuterMeasure_bind_apply]
  trans (∑' trial, (if ¬ trial.IsSuccess then
        (oddSplitTrialPMF M D enumeration q coefficientCount g offset) trial else 0) *
        (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts
          (offset + 1)).toOuterMeasure
          {trials | TrialResult.allFailed trials})
  · apply tsum_congr
    intro trial
    rw [toOuterMeasure_map_cons_allFailed]
    by_cases hfail : ¬ trial.IsSuccess <;> simp [hfail]
  · conv_rhs =>
      rw [PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro trial
    by_cases hsuccess : trial.IsSuccess <;> simp [hsuccess]

/--
If every one-factor trial succeeds with probability at least `1 / 2`, the
probability of using fallback after `attempts` trials is at most `2^-attempts`.
-/
theorem fallbackAfterOddAttempts_probability_le_geometric {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset : Nat)
    (hstep : ∀ i, i < attempts →
      (2 : ℝ≥0∞)⁻¹ ≤
        trialSuccessProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g (offset + i))) :
    fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g attempts offset ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  induction attempts generalizing offset with
  | zero =>
      rw [fallbackAfterOddAttemptsProbability, eventProbability, repeatedOddSplitTrialsPMF]
      exact le_trans
        ((pure ([] : List (TrialResult F)) : PMF (List (TrialResult F))).toOuterMeasure.mono
          (Set.subset_univ _))
        (by simp [PMF.toOuterMeasure_apply])
  | succ attempts ih =>
      rw [fallbackAfterOddAttemptsProbability_succ]
      let half : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹
      have hfail : eventProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g offset)
          {trial | ¬ trial.IsSuccess} ≤ half := by
        exact trialFailureProbability_le_half_of_success _ (hstep 0 (by omega))
      have hrest :
          fallbackAfterOddAttemptsProbability M D enumeration q coefficientCount g attempts
              (offset + 1) ≤
            half ^ attempts := by
        exact ih (offset + 1) (by
          intro i hi
          have h := hstep (i + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      refine (mul_le_mul' hfail hrest).trans ?_
      change half * half ^ attempts ≤ half ^ (attempts + 1)
      rw [pow_succ]
      exact le_of_eq (_root_.mul_comm (a := half) (b := half ^ attempts))

/--
For a squarefree finite-field root product over an odd field, the uniform probe
source reaches enumeration fallback after `attempts` one-factor trials with
probability at most `2^-attempts`.
-/
theorem fallbackAfterOddAttempts_probability_le_geometric_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts offset : Nat)
    (hfield : OddUniformFieldModel F q enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    fallbackAfterOddAttemptsProbability M D enumeration.toFieldEnumeration q
        (CPolynomial.natDegree g) g attempts offset ≤
      ((2 : ℝ≥0∞)⁻¹) ^ attempts := by
  apply fallbackAfterOddAttempts_probability_le_geometric
  intro i _hi
  exact oddSplitTrial_success_probability_ge_half M D enumeration g (offset + i)
    hfield hrootProduct hdegree

/--
The repeated one-factor odd-field trial source satisfies the recursive fallback
model by concentrating the bad-rank mass at rank `0`.
-/
theorem repeatedOddSplitTrialsPMF_recursiveFallbackProbabilityModel {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (q coefficientCount : Nat)
    (g : CPolynomial F) (attempts offset degree : Nat)
    (hdegree : 2 ≤ degree)
    (hstep : ∀ i, i < attempts →
      (2 : ℝ≥0∞)⁻¹ ≤
        trialSuccessProbability
          (oddSplitTrialPMF M D enumeration q coefficientCount g (offset + i))) :
    RecursiveFallbackProbabilityModel
      (repeatedOddSplitTrialsPMF M D enumeration q coefficientCount g attempts offset)
      {trials | TrialResult.allFailed trials}
      attempts degree := by
  refine
    ⟨fun j ↦ if j = 0 then {trials | TrialResult.allFailed trials} else ∅,
      ?_, ?_, ?_⟩
  · intro trials htrials
    exact Set.mem_iUnion.mpr ⟨0, by simpa using htrials⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      have hzero_mem : 0 ∈ Finset.range (degree - 1) := by
        simp
        omega
      exact (hj hzero_mem).elim
    · simp [hj0, eventProbability]
  · intro j _hj
    by_cases hj0 : j = 0
    · subst j
      simpa [fallbackAfterOddAttemptsProbability] using
        fallbackAfterOddAttempts_probability_le_geometric M D enumeration q coefficientCount
          g attempts offset hstep
    · simp [hj0, eventProbability]

/--
The one-factor recursive fallback model witness, with the per-trial
half-success hypothesis discharged from the actual uniform probe source.
-/
theorem repeatedOddSplitTrialsPMF_recursiveFallbackProbabilityModel_of_uniformProbe {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (g : CPolynomial F) (attempts offset degree : Nat)
    (hdeg : 2 ≤ degree)
    (hfield : OddUniformFieldModel F q enumeration)
    (hrootProduct : RootProductProbabilityInput q g)
    (hdegree : 2 ≤ CPolynomial.natDegree g) :
    RecursiveFallbackProbabilityModel
      (repeatedOddSplitTrialsPMF M D enumeration.toFieldEnumeration q
        (CPolynomial.natDegree g) g attempts offset)
      {trials | TrialResult.allFailed trials}
      attempts degree := by
  apply repeatedOddSplitTrialsPMF_recursiveFallbackProbabilityModel M D
    enumeration.toFieldEnumeration q (CPolynomial.natDegree g) g attempts offset degree hdeg
  intro i _hi
  exact oddSplitTrial_success_probability_ge_half M D enumeration g (offset + i)
    hfield hrootProduct hdegree

end FiniteField

end Roots

end CPolynomial

end CompPoly
