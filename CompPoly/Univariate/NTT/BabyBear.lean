/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.Fields.BabyBear
public import CompPoly.Univariate.NTT.Domain

/-!
# BabyBear NTT Domains

Concrete radix-2 NTT domains over the BabyBear field.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace BabyBear

/-- Build a finite index into the BabyBear two-adic generator table. -/
def bitsOfLogN (logN : Nat) (hlogN : logN ≤ BabyBear.twoAdicity) :
    Fin (BabyBear.twoAdicity + 1) :=
  ⟨logN, Nat.lt_succ_of_le hlogN⟩

/-- BabyBear radix-2 NTT domain for a supported two-adic size. -/
def domainOfLogN (logN : Nat) (hlogN : logN ≤ BabyBear.twoAdicity) :
    Domain BabyBear.Field where
  logN := logN
  omega := BabyBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      BabyBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)

/-- BabyBear NTT domain lookup for dynamic multiplication contexts. -/
def bestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain BabyBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? BabyBear.twoAdicity
    domainOfLogN (by intro _ _; rfl) requiredLen

/-- Fast BabyBear radix-2 NTT domain for a supported two-adic size. -/
def fastDomainOfLogN (logN : Nat) (hlogN : logN ≤ BabyBear.twoAdicity) :
    Domain BabyBear.Fast.Field where
  logN := logN
  omega := BabyBear.Fast.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    have h := (BabyBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)).map_of_injective
      BabyBear.Fast.ringEquiv.symm.injective
    simpa [BabyBear.Fast.twoAdicGenerators_eq_map, bitsOfLogN, BabyBear.Fast.ringEquiv,
      BabyBear.Fast.ofField] using h

/-- Fast BabyBear NTT domain lookup for dynamic multiplication contexts. -/
def fastBestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain BabyBear.Fast.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? BabyBear.twoAdicity
    fastDomainOfLogN (by intro _ _; rfl) requiredLen

end BabyBear
end NTT
end CPolynomial
end CompPoly
