/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField.NTT
import CompPoly.Fields.KoalaBear
import CompPoly.Univariate.NTT.KoalaBear

/-!
# KoalaBear Guruswami-Sudan Field-Root Backends

Concrete finite-field root backends for canonical KoalaBear and native-word fast
KoalaBear. Both use the generic odd finite-field algorithm directly over their
field carriers.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Odd finite-field context for canonical KoalaBear. -/
def koalaBearOddFiniteFieldContext :
    CPolynomial.Roots.FiniteField.OddFiniteFieldContext KoalaBear.Field where
  q := KoalaBear.fieldSize
  finite := by infer_instance
  card_eq := by
    sorry
  q_odd := by
    unfold KoalaBear.fieldSize
    decide
  frobenius_fixed := by
    intro a
    sorry

/-- Complete GS-facing finite-field root backend for canonical KoalaBear. -/
def koalaBearFieldRootBackend : FieldRootBackend KoalaBear.Field :=
  deterministicOddFiniteFieldRootBackend KoalaBear.Field koalaBearOddFiniteFieldContext

/-- Complete GS-facing finite-field root backend for canonical KoalaBear with NTT arithmetic. -/
def koalaBearNttFieldRootBackend : FieldRootBackend KoalaBear.Field :=
  nttOddFiniteFieldRootBackend KoalaBear.Field
    koalaBearOddFiniteFieldContext CPolynomial.NTT.KoalaBear.bestDomainForLength?

/-- Complete GS-facing finite-field root backend for canonical KoalaBear with NTTFast arithmetic. -/
def koalaBearNttFastFieldRootBackend : FieldRootBackend KoalaBear.Field :=
  nttFastOddFiniteFieldRootBackend KoalaBear.Field
    koalaBearOddFiniteFieldContext CPolynomial.NTT.KoalaBear.bestDomainForLength?

/-- Odd finite-field context for native-word fast KoalaBear. -/
def fastKoalaBearOddFiniteFieldContext :
    CPolynomial.Roots.FiniteField.OddFiniteFieldContext KoalaBear.Fast.Field where
  q := KoalaBear.fieldSize
  finite := by
    sorry
  card_eq := by
    sorry
  q_odd := by
    unfold KoalaBear.fieldSize
    decide
  frobenius_fixed := by
    intro a
    sorry

/-- Complete GS-facing finite-field root backend for native-word fast KoalaBear. -/
def fastKoalaBearFieldRootBackend : FieldRootBackend KoalaBear.Fast.Field :=
  deterministicOddFiniteFieldRootBackend
    KoalaBear.Fast.Field fastKoalaBearOddFiniteFieldContext

/--
Complete GS-facing finite-field root backend for native-word fast KoalaBear with
NTT arithmetic.
-/
def fastKoalaBearNttFieldRootBackend : FieldRootBackend KoalaBear.Fast.Field :=
  nttOddFiniteFieldRootBackend KoalaBear.Fast.Field
    fastKoalaBearOddFiniteFieldContext CPolynomial.NTT.KoalaBear.fastBestDomainForLength?

/--
Complete GS-facing finite-field root backend for native-word fast KoalaBear with
NTTFast arithmetic.
-/
def fastKoalaBearNttFastFieldRootBackend : FieldRootBackend KoalaBear.Fast.Field :=
  nttFastOddFiniteFieldRootBackend KoalaBear.Fast.Field
    fastKoalaBearOddFiniteFieldContext CPolynomial.NTT.KoalaBear.fastBestDomainForLength?

end GuruswamiSudan

end CompPoly
