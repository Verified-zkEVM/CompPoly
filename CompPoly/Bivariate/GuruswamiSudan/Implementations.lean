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
correctness theorem specializations for the implementations exercised by the
benchmark suite.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Dense interpolation backend over canonical KoalaBear. -/
def koalaBearDenseInterpContext : GSInterpContext KoalaBear.Field :=
  denseInterpContext KoalaBear.Field

/-- Dense interpolation backend over native-word fast KoalaBear. -/
def fastKoalaBearDenseInterpContext : GSInterpContext KoalaBear.Fast.Field :=
  denseInterpContext KoalaBear.Fast.Field

/-- Koetter-first interpolation backend over canonical KoalaBear, with dense fallback. -/
def koalaBearKoetterInterpContext : GSInterpContext KoalaBear.Field :=
  koetterInterpContext KoalaBear.Field

/-- Koetter-first interpolation backend over native-word fast KoalaBear, with dense fallback. -/
def fastKoalaBearKoetterInterpContext : GSInterpContext KoalaBear.Fast.Field :=
  koetterInterpContext KoalaBear.Fast.Field

/-- Roth-Ruckenstein root backend over canonical KoalaBear. -/
def koalaBearRothRootContext : GSRootContext KoalaBear.Field :=
  rothRuckensteinRootContext KoalaBear.Field koalaBearFieldRootContext

/-- Roth-Ruckenstein root backend over canonical KoalaBear with NTTFast field roots. -/
def koalaBearRothNttFastRootContext : GSRootContext KoalaBear.Field :=
  rothRuckensteinRootContext KoalaBear.Field koalaBearNttFastFieldRootContext

/-- Roth-Ruckenstein root backend over native-word fast KoalaBear. -/
def fastKoalaBearRothRootContext : GSRootContext KoalaBear.Fast.Field :=
  rothRuckensteinRootContext KoalaBear.Fast.Field fastKoalaBearFieldRootContext

/-- Roth-Ruckenstein root backend over native-word fast KoalaBear with NTTFast field roots. -/
def fastKoalaBearRothNttFastRootContext : GSRootContext KoalaBear.Fast.Field :=
  rothRuckensteinRootContext KoalaBear.Fast.Field fastKoalaBearNttFastFieldRootContext

/-- Filtered dense/Roth context over canonical KoalaBear. -/
def koalaBearDenseRothContext : GSFilteredCoreContext KoalaBear.Field :=
  filteredCoreContextOfInterpRootContexts koalaBearDenseInterpContext koalaBearRothRootContext

/-- Filtered dense/Roth context over canonical KoalaBear with NTTFast field roots. -/
def koalaBearDenseRothNttFastContext : GSFilteredCoreContext KoalaBear.Field :=
  filteredCoreContextOfInterpRootContexts koalaBearDenseInterpContext
    koalaBearRothNttFastRootContext

/-- Filtered dense/Roth context over native-word fast KoalaBear. -/
def fastKoalaBearDenseRothContext : GSFilteredCoreContext KoalaBear.Fast.Field :=
  filteredCoreContextOfInterpRootContexts fastKoalaBearDenseInterpContext
    fastKoalaBearRothRootContext

/-- Filtered dense/Roth context over native-word fast KoalaBear with NTTFast field roots. -/
def fastKoalaBearDenseRothNttFastContext : GSFilteredCoreContext KoalaBear.Fast.Field :=
  filteredCoreContextOfInterpRootContexts fastKoalaBearDenseInterpContext
    fastKoalaBearRothNttFastRootContext

/-- Filtered Koetter/Roth context over canonical KoalaBear. -/
def koalaBearKoetterRothContext : GSFilteredCoreContext KoalaBear.Field :=
  filteredCoreContextOfInterpRootContexts koalaBearKoetterInterpContext koalaBearRothRootContext

/-- Filtered Koetter/Roth context over canonical KoalaBear with NTTFast field roots. -/
def koalaBearKoetterRothNttFastContext : GSFilteredCoreContext KoalaBear.Field :=
  filteredCoreContextOfInterpRootContexts koalaBearKoetterInterpContext
    koalaBearRothNttFastRootContext

/-- Filtered Koetter/Roth context over native-word fast KoalaBear. -/
def fastKoalaBearKoetterRothContext : GSFilteredCoreContext KoalaBear.Fast.Field :=
  filteredCoreContextOfInterpRootContexts fastKoalaBearKoetterInterpContext
    fastKoalaBearRothRootContext

/-- Filtered Koetter/Roth context over native-word fast KoalaBear with NTTFast field roots. -/
def fastKoalaBearKoetterRothNttFastContext : GSFilteredCoreContext KoalaBear.Fast.Field :=
  filteredCoreContextOfInterpRootContexts fastKoalaBearKoetterInterpContext
    fastKoalaBearRothNttFastRootContext

/-- Concrete soundness for the canonical KoalaBear dense/Roth core. -/
theorem koalaBearDenseRothGsCore_sound {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hp : p ∈ (gsCore points koalaBearDenseInterpContext koalaBearRothRootContext params).toList) :
    ∃ Q,
      koalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothRootContext) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth core. -/
theorem koalaBearDenseRothGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points koalaBearDenseInterpContext koalaBearRothRootContext params).toList :=
  gsCore_complete_of_enough_matches (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothRootContext) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the canonical KoalaBear dense/Roth filtered core. -/
theorem koalaBearDenseRothGsFilteredCore_sound
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hp :
      p ∈ (gsFilteredCore points koalaBearDenseInterpContext koalaBearRothRootContext
        params radius).toList) :
    ∃ Q,
      koalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothRootContext) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth filtered core. -/
theorem koalaBearDenseRothGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points koalaBearDenseInterpContext koalaBearRothRootContext
      params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothRootContext) hInterpExists hpdeg hdistinct hmatches hpass

/-- Concrete soundness for the canonical KoalaBear dense/Roth-NTTFast core. -/
theorem koalaBearDenseRothNttFastGsCore_sound
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hp :
      p ∈ (gsCore points koalaBearDenseInterpContext koalaBearRothNttFastRootContext
        params).toList) :
    ∃ Q,
      koalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothNttFastRootContext) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth-NTTFast core. -/
theorem koalaBearDenseRothNttFastGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points koalaBearDenseInterpContext koalaBearRothNttFastRootContext params).toList :=
  gsCore_complete_of_enough_matches (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothNttFastRootContext) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the canonical KoalaBear dense/Roth-NTTFast filtered core. -/
theorem koalaBearDenseRothNttFastGsFilteredCore_sound
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hp :
      p ∈ (gsFilteredCore points koalaBearDenseInterpContext koalaBearRothNttFastRootContext
        params radius).toList) :
    ∃ Q,
      koalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothNttFastRootContext) hp

/-- Concrete completeness for the canonical KoalaBear dense/Roth-NTTFast filtered core. -/
theorem koalaBearDenseRothNttFastGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Field × KoalaBear.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points koalaBearDenseInterpContext koalaBearRothNttFastRootContext
      params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpContext := koalaBearDenseInterpContext)
    (rootContext := koalaBearRothNttFastRootContext) hInterpExists hpdeg hdistinct hmatches hpass

/-- Concrete soundness for the fast KoalaBear dense/Roth core. -/
theorem fastKoalaBearDenseRothGsCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsCore points fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
        params).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothRootContext) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth core. -/
theorem fastKoalaBearDenseRothGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
      params).toList :=
  gsCore_complete_of_enough_matches (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothRootContext) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the fast KoalaBear dense/Roth filtered core. -/
theorem fastKoalaBearDenseRothGsFilteredCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsFilteredCore points fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
        params radius).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothRootContext) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth filtered core. -/
theorem fastKoalaBearDenseRothGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points fastKoalaBearDenseInterpContext fastKoalaBearRothRootContext
      params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothRootContext) hInterpExists hpdeg hdistinct hmatches hpass

/-- Concrete soundness for the fast KoalaBear dense/Roth-NTTFast core. -/
theorem fastKoalaBearDenseRothNttFastGsCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsCore points fastKoalaBearDenseInterpContext fastKoalaBearRothNttFastRootContext
        params).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 :=
  gsCore_sound (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothNttFastRootContext) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth-NTTFast core. -/
theorem fastKoalaBearDenseRothNttFastGsCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points fastKoalaBearDenseInterpContext fastKoalaBearRothNttFastRootContext
      params).toList :=
  gsCore_complete_of_enough_matches (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothNttFastRootContext) hInterpExists hpdeg hdistinct hmatches

/-- Concrete soundness for the fast KoalaBear dense/Roth-NTTFast filtered core. -/
theorem fastKoalaBearDenseRothNttFastGsFilteredCore_sound
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hp :
      p ∈ (gsFilteredCore points fastKoalaBearDenseInterpContext
        fastKoalaBearRothNttFastRootContext params radius).toList) :
    ∃ Q,
      fastKoalaBearDenseInterpContext.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 ∧
              candidateMismatchCount points p ≤ radius :=
  gsFilteredCore_sound (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothNttFastRootContext) hp

/-- Concrete completeness for the fast KoalaBear dense/Roth-NTTFast filtered core. -/
theorem fastKoalaBearDenseRothNttFastGsFilteredCore_complete_of_enough_matches
    {points : Array (KoalaBear.Fast.Field × KoalaBear.Fast.Field)}
    {params : GSInterpParams} {radius : Nat} {p : CPolynomial KoalaBear.Fast.Field}
    (hInterpExists : ∃ Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches : params.weightedDegreeBound < params.multiplicity * matchingPointCount points p)
    (hpass : passesCandidateDistance points radius p = true) :
    p ∈ (gsFilteredCore points fastKoalaBearDenseInterpContext
      fastKoalaBearRothNttFastRootContext params radius).toList :=
  gsFilteredCore_complete_of_enough_matches (interpContext := fastKoalaBearDenseInterpContext)
    (rootContext := fastKoalaBearRothNttFastRootContext)
    hInterpExists hpdeg hdistinct hmatches hpass

end GuruswamiSudan

end CompPoly
