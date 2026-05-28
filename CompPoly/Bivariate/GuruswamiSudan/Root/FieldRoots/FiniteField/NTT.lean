/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Univariate.Context

/-!
# NTT Finite-Field Root Adapters

Generic GS field-root backend constructors for finite fields with NTT domain
lookups.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Deterministic odd finite-field root backend using NTT multiplication and reversal-based
monic remainders. -/
def nttOddFiniteFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (CPolynomial.NTT.FittingDomain F requiredLen)) :
    FieldRootBackend F :=
  deterministicOddFiniteFieldRootBackendWith F
    (CPolynomial.Raw.MulContext.ntt bestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNtt bestDomainForLength?) ctx

/-- Deterministic odd finite-field root backend using NTTFast multiplication and reversal-based
monic remainders. -/
def nttFastOddFiniteFieldRootBackend (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    (ctx : CPolynomial.Roots.FiniteField.OddFiniteFieldContext F)
    (bestDomainForLength? : (requiredLen : Nat) →
      Option (CPolynomial.NTT.FittingDomain F requiredLen)) :
    FieldRootBackend F :=
  deterministicOddFiniteFieldRootBackendWith F
    (CPolynomial.Raw.MulContext.nttFast bestDomainForLength?)
    (CPolynomial.Raw.ModContext.reversalNttFast bestDomainForLength?) ctx

end GuruswamiSudan

end CompPoly
