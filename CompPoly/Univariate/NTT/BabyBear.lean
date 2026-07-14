/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.BabyBear
import CompPoly.Univariate.NTT.Domain

/-!
# BabyBear NTT Domains

Concrete radix-2 NTT domains over the BabyBear field.
-/

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

end BabyBear
end NTT
end CPolynomial
end CompPoly
