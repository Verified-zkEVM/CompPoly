/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Executable
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear

/-!
# Guruswami-Sudan Concrete Implementations

Named concrete dense-interpolation/Roth-Ruckenstein implementations and
correctness theorem aliases for the implementations exercised by the benchmark
suite.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Dense interpolation backend over canonical KoalaBear. -/
def koalaBearDenseInterpBackend : GSInterpBackend KoalaBear.Field :=
  denseInterpBackend KoalaBear.Field

/-- Dense interpolation backend over native-word fast KoalaBear. -/
def fastKoalaBearDenseInterpBackend : GSInterpBackend KoalaBear.Fast.Field :=
  denseInterpBackend KoalaBear.Fast.Field

/-- Roth-Ruckenstein root backend over canonical KoalaBear. -/
def koalaBearRothRootBackend : GSRootBackend KoalaBear.Field :=
  rothRuckensteinRootBackend KoalaBear.Field koalaBearFieldRootBackend

/-- Roth-Ruckenstein root backend over canonical KoalaBear with NTTFast field roots. -/
def koalaBearRothNttFastRootBackend : GSRootBackend KoalaBear.Field :=
  rothRuckensteinRootBackend KoalaBear.Field koalaBearNttFastFieldRootBackend

/-- Roth-Ruckenstein root backend over native-word fast KoalaBear. -/
def fastKoalaBearRothRootBackend : GSRootBackend KoalaBear.Fast.Field :=
  rothRuckensteinRootBackend KoalaBear.Fast.Field fastKoalaBearFieldRootBackend

/-- Roth-Ruckenstein root backend over native-word fast KoalaBear with NTTFast field roots. -/
def fastKoalaBearRothNttFastRootBackend : GSRootBackend KoalaBear.Fast.Field :=
  rothRuckensteinRootBackend KoalaBear.Fast.Field fastKoalaBearNttFastFieldRootBackend

/-- Filtered dense/Roth context over canonical KoalaBear. -/
def koalaBearDenseRothContext : GSFilteredCoreContext KoalaBear.Field :=
  filteredCoreContextOfBackends koalaBearDenseInterpBackend koalaBearRothRootBackend

/-- Filtered dense/Roth context over canonical KoalaBear with NTTFast field roots. -/
def koalaBearDenseRothNttFastContext : GSFilteredCoreContext KoalaBear.Field :=
  filteredCoreContextOfBackends koalaBearDenseInterpBackend koalaBearRothNttFastRootBackend

/-- Filtered dense/Roth context over native-word fast KoalaBear. -/
def fastKoalaBearDenseRothContext : GSFilteredCoreContext KoalaBear.Fast.Field :=
  filteredCoreContextOfBackends fastKoalaBearDenseInterpBackend fastKoalaBearRothRootBackend

/-- Filtered dense/Roth context over native-word fast KoalaBear with NTTFast field roots. -/
def fastKoalaBearDenseRothNttFastContext : GSFilteredCoreContext KoalaBear.Fast.Field :=
  filteredCoreContextOfBackends fastKoalaBearDenseInterpBackend fastKoalaBearRothNttFastRootBackend

/-- Concrete soundness for the canonical KoalaBear dense/Roth core. -/
theorem koalaBearDenseRothGsCore_sound {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hp : p ∈ (gsCore points koalaBearDenseInterpBackend koalaBearRothRootBackend params).toList) :
    ∃ Q,
      koalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothRootBackend) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth core. -/
theorem koalaBearDenseRothGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points koalaBearDenseInterpBackend koalaBearRothRootBackend params).toList :=
  gsCore_complete_of_enough_matches (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothRootBackend) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the canonical KoalaBear dense/Roth filtered core. -/
theorem koalaBearDenseRothGsFilteredCore_sound
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hp :
      p ∈ (gsFilteredCore points koalaBearDenseInterpBackend koalaBearRothRootBackend
        params radius).toList) :
    ∃ Q,
      koalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothRootBackend) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth filtered core. -/
theorem koalaBearDenseRothGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points koalaBearDenseInterpBackend koalaBearRothRootBackend
      params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothRootBackend) hInterpExists hpdeg hdistinct hmatches hpass

/-- Concrete soundness for the canonical KoalaBear dense/Roth-NTTFast core. -/
theorem koalaBearDenseRothNttFastGsCore_sound
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hp :
      p ∈ (gsCore points koalaBearDenseInterpBackend koalaBearRothNttFastRootBackend
        params).toList) :
    ∃ Q,
      koalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothNttFastRootBackend) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth-NTTFast core. -/
theorem koalaBearDenseRothNttFastGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points koalaBearDenseInterpBackend koalaBearRothNttFastRootBackend params).toList :=
  gsCore_complete_of_enough_matches (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothNttFastRootBackend) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the canonical KoalaBear dense/Roth-NTTFast filtered core. -/
theorem koalaBearDenseRothNttFastGsFilteredCore_sound
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hp :
      p ∈ (gsFilteredCore points koalaBearDenseInterpBackend koalaBearRothNttFastRootBackend
        params radius).toList) :
    ∃ Q,
      koalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothNttFastRootBackend) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth-NTTFast filtered core. -/
theorem koalaBearDenseRothNttFastGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points koalaBearDenseInterpBackend koalaBearRothNttFastRootBackend
      params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpBackend := koalaBearDenseInterpBackend)
    (rootBackend := koalaBearRothNttFastRootBackend) hInterpExists hpdeg hdistinct hmatches hpass

/-- Concrete soundness for the fast KoalaBear dense/Roth core. -/
theorem fastKoalaBearDenseRothGsCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsCore points fastKoalaBearDenseInterpBackend fastKoalaBearRothRootBackend
        params).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothRootBackend) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth core. -/
theorem fastKoalaBearDenseRothGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points fastKoalaBearDenseInterpBackend fastKoalaBearRothRootBackend
      params).toList :=
  gsCore_complete_of_enough_matches (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothRootBackend) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the fast KoalaBear dense/Roth filtered core. -/
theorem fastKoalaBearDenseRothGsFilteredCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsFilteredCore points fastKoalaBearDenseInterpBackend fastKoalaBearRothRootBackend
        params radius).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothRootBackend) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth filtered core. -/
theorem fastKoalaBearDenseRothGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points fastKoalaBearDenseInterpBackend fastKoalaBearRothRootBackend
      params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothRootBackend) hInterpExists hpdeg hdistinct hmatches hpass

/-- Concrete soundness for the fast KoalaBear dense/Roth-NTTFast core. -/
theorem fastKoalaBearDenseRothNttFastGsCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsCore points fastKoalaBearDenseInterpBackend fastKoalaBearRothNttFastRootBackend
        params).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothNttFastRootBackend) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth-NTTFast core. -/
theorem fastKoalaBearDenseRothNttFastGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points fastKoalaBearDenseInterpBackend fastKoalaBearRothNttFastRootBackend
      params).toList :=
  gsCore_complete_of_enough_matches (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothNttFastRootBackend) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the fast KoalaBear dense/Roth-NTTFast filtered core. -/
theorem fastKoalaBearDenseRothNttFastGsFilteredCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsFilteredCore points fastKoalaBearDenseInterpBackend
        fastKoalaBearRothNttFastRootBackend params radius).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothNttFastRootBackend) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth-NTTFast filtered core. -/
theorem fastKoalaBearDenseRothNttFastGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points fastKoalaBearDenseInterpBackend
      fastKoalaBearRothNttFastRootBackend params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpBackend := fastKoalaBearDenseInterpBackend)
    (rootBackend := fastKoalaBearRothNttFastRootBackend)
    hInterpExists hpdeg hdistinct hmatches hpass

end GuruswamiSudan

end CompPoly
