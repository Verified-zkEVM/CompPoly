/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.KoalaBear
import CompPoly.Univariate.NTT.Domain

/-!
# KoalaBear NTT Domains

Concrete radix-2 NTT domains over the KoalaBear field.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace KoalaBear

/-- Build a finite index into the KoalaBear two-adic generator table. -/
def bitsOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Fin (KoalaBear.twoAdicity + 1) :=
  ⟨logN, Nat.lt_succ_of_le hlogN⟩

/-- KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def domainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Field where
  logN := logN
  omega := KoalaBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      KoalaBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)

/-- KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def bestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain KoalaBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    domainOfLogN (by intro _ _; rfl) requiredLen

/-- Fast KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def fastDomainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Fast.Field where
  logN := logN
  omega := KoalaBear.Fast.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    have h := (KoalaBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)).map_of_injective
      KoalaBear.Fast.ringEquiv.symm.injective
    simpa [KoalaBear.Fast.twoAdicGenerators_eq_map, bitsOfLogN, KoalaBear.Fast.ringEquiv,
      KoalaBear.Fast.ofField] using h

/-- Fast KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def fastBestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain KoalaBear.Fast.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    fastDomainOfLogN (by intro _ _; rfl) requiredLen

end KoalaBear
end NTT
end CPolynomial
end CompPoly
