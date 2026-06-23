/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Executable
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Fast
import CompPoly.Univariate.BatchEval.Context
import CompPoly.Univariate.NTT.KoalaBear

/-!
# Guruswami-Sudan Concrete Implementations

Named concrete dense and Lee-O'Sullivan interpolation/Roth-Ruckenstein
implementations and correctness theorem specializations for the decoder surface.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Dense interpolation backend over canonical KoalaBear. -/
def koalaBearDenseInterpContext : GSInterpContext KoalaBear.Field :=
  denseInterpContext KoalaBear.Field

/-- Dense interpolation backend over native-word fast KoalaBear. -/
def fastKoalaBearDenseInterpContext : GSInterpContext KoalaBear.Fast.Field :=
  denseInterpContext KoalaBear.Fast.Field

/-- NTTFast-backed univariate multiplication over canonical KoalaBear. -/
def koalaBearNttFastMulContext : CPolynomial.MulContext KoalaBear.Field :=
  CPolynomial.MulContext.nttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?

/-- NTTFast-backed univariate monic remainders over canonical KoalaBear. -/
def koalaBearNttFastModContext : CPolynomial.ModContext KoalaBear.Field :=
  CPolynomial.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.bestDomainForLength?

/-- NTTFast-backed subproduct batch evaluation over canonical KoalaBear. -/
def koalaBearNttFastBatchEvalContext : CPolynomial.BatchEvalContext KoalaBear.Field :=
  CPolynomial.BatchEvalContext.subproduct KoalaBear.Field
    koalaBearNttFastMulContext koalaBearNttFastModContext

/-- NTTFast-backed univariate multiplication over native-word fast KoalaBear. -/
def fastKoalaBearNttFastMulContext : CPolynomial.MulContext KoalaBear.Fast.Field :=
  CPolynomial.MulContext.nttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?

/-- NTTFast-backed univariate monic remainders over native-word fast KoalaBear. -/
def fastKoalaBearNttFastModContext : CPolynomial.ModContext KoalaBear.Fast.Field :=
  CPolynomial.ModContext.reversalNttFast CPolynomial.NTT.KoalaBear.fastBestDomainForLength?

/-- NTTFast-backed subproduct batch evaluation over native-word fast KoalaBear. -/
def fastKoalaBearNttFastBatchEvalContext :
    CPolynomial.BatchEvalContext KoalaBear.Fast.Field :=
  CPolynomial.BatchEvalContext.subproduct KoalaBear.Fast.Field
    fastKoalaBearNttFastMulContext fastKoalaBearNttFastModContext

/-- Lee-O'Sullivan interpolation over canonical KoalaBear with direct vanishing setup. -/
def koalaBearLeeDirectInterpContext : GSInterpContext KoalaBear.Field :=
  LeeOSullivan.leeOSullivanInterpContext
    (CPolynomial.VanishingPolynomialContext.direct (F := KoalaBear.Field))
    (CPolynomial.BatchEvalContext.horner KoalaBear.Field)
    (PolynomialMatrix.muldersStorjohannFastReducerContext KoalaBear.Field)

/-- Lee-O'Sullivan interpolation over canonical KoalaBear with subproduct-tree vanishing setup. -/
def koalaBearLeeSubproductInterpContext : GSInterpContext KoalaBear.Field :=
  LeeOSullivan.leeOSullivanInterpContext
    (CPolynomial.VanishingPolynomialContext.subproduct
      koalaBearNttFastMulContext)
    koalaBearNttFastBatchEvalContext
    (PolynomialMatrix.muldersStorjohannFastReducerContext KoalaBear.Field)

/-- Lee-O'Sullivan interpolation over native-word fast KoalaBear with direct vanishing setup. -/
def fastKoalaBearLeeDirectInterpContext : GSInterpContext KoalaBear.Fast.Field :=
  LeeOSullivan.leeOSullivanInterpContext
    (CPolynomial.VanishingPolynomialContext.direct (F := KoalaBear.Fast.Field))
    (CPolynomial.BatchEvalContext.horner KoalaBear.Fast.Field)
    (PolynomialMatrix.muldersStorjohannFastReducerContext KoalaBear.Fast.Field)

/-- Lee-O'Sullivan interpolation over native-word fast KoalaBear with
subproduct-tree vanishing setup. -/
def fastKoalaBearLeeSubproductInterpContext : GSInterpContext KoalaBear.Fast.Field :=
  LeeOSullivan.leeOSullivanInterpContext
    (CPolynomial.VanishingPolynomialContext.subproduct
      fastKoalaBearNttFastMulContext)
    fastKoalaBearNttFastBatchEvalContext
    (PolynomialMatrix.muldersStorjohannFastReducerContext KoalaBear.Fast.Field)

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
