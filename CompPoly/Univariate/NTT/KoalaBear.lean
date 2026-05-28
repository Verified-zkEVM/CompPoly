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

/-- The KoalaBear NTT domain size is nonzero in the field for supported two-adic sizes. -/
theorem twoPowNatCast_ne_zero
    (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    (((2 ^ logN : Nat) : KoalaBear.Field) ≠ 0) := by
  intro hzero
  have hpow_pos : 0 < 2 ^ logN := by
    positivity
  have hpow_le : 2 ^ logN ≤ 2 ^ KoalaBear.twoAdicity := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlogN
  have hpow_lt : 2 ^ logN < KoalaBear.fieldSize := by
    have htop : 2 ^ KoalaBear.twoAdicity < KoalaBear.fieldSize := by
      simp [KoalaBear.twoAdicity, KoalaBear.fieldSize]
    exact lt_of_le_of_lt hpow_le htop
  have hdiv : KoalaBear.fieldSize ∣ 2 ^ logN := by
    exact (ZMod.natCast_eq_zero_iff (2 ^ logN) KoalaBear.fieldSize).mp hzero
  exact (not_le_of_gt hpow_lt) (Nat.le_of_dvd hpow_pos hdiv)

/-- KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def domainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Field where
  logN := logN
  omega := KoalaBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      KoalaBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)
  natCast_ne_zero := twoPowNatCast_ne_zero logN hlogN

/-- KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def bestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain KoalaBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    domainOfLogN (by intro _ _; rfl) requiredLen

/-- Fast KoalaBear two-adic generators are primitive roots of the same orders. -/
theorem fast_isPrimitiveRoot_twoAdicGenerator
    (bits : Fin (KoalaBear.twoAdicity + 1)) :
    IsPrimitiveRoot (KoalaBear.Fast.ofField KoalaBear.twoAdicGenerators[bits])
      (2 ^ (bits : Nat)) := by
  have hbasic : IsPrimitiveRoot KoalaBear.twoAdicGenerators[bits] (2 ^ (bits : Nat)) :=
    KoalaBear.isPrimitiveRoot_twoAdicGenerator bits
  have hfast :
      IsPrimitiveRoot (KoalaBear.Fast.ringEquiv.symm KoalaBear.twoAdicGenerators[bits])
        (2 ^ (bits : Nat)) := by
    exact hbasic.map_of_injective KoalaBear.Fast.ringEquiv.symm.injective
  simpa using hfast

/-- The fast KoalaBear NTT domain size is nonzero for supported two-adic sizes. -/
theorem fast_twoPowNatCast_ne_zero
    (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    (((2 ^ logN : Nat) : KoalaBear.Fast.Field) ≠ 0) := by
  intro hzero
  exact twoPowNatCast_ne_zero logN hlogN (by
    calc
      (((2 ^ logN : Nat) : KoalaBear.Field)) =
          KoalaBear.Fast.toField (((2 ^ logN : Nat) : KoalaBear.Fast.Field)) := by
        rw [KoalaBear.Fast.toField_natCast]
      _ = KoalaBear.Fast.toField 0 := congrArg KoalaBear.Fast.toField hzero
      _ = 0 := KoalaBear.Fast.toField_zero)

/-- Fast KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def fastDomainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Fast.Field where
  logN := logN
  omega := KoalaBear.Fast.ofField
    KoalaBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      fast_isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)
  natCast_ne_zero := fast_twoPowNatCast_ne_zero logN hlogN

/-- Fast KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def fastBestDomainForLength? (requiredLen : Nat) :
    Option (FittingDomain KoalaBear.Fast.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    fastDomainOfLogN (by intro _ _; rfl) requiredLen

end KoalaBear
end NTT
end CPolynomial
end CompPoly
