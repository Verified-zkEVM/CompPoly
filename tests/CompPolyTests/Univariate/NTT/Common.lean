/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Fields.KoalaBear

/-!
  # Univariate NTT Test Helpers

  Shared concrete KoalaBear domains used by the NTT test files.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace TestCommon

def testBitsOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Fin (KoalaBear.twoAdicity + 1) :=
  ⟨logN, Nat.lt_succ_of_le hlogN⟩

private theorem koalaBear_twoPow_natCast_ne_zero
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

def testDomainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    Domain KoalaBear.Field where
  logN := logN
  omega := KoalaBear.twoAdicGenerators[testBitsOfLogN logN hlogN]
  primitive := by
    simpa [testBitsOfLogN] using
      KoalaBear.isPrimitiveRoot_twoAdicGenerator (testBitsOfLogN logN hlogN)
  natCast_ne_zero := koalaBear_twoPow_natCast_ne_zero logN hlogN

def testDomain8 : Domain KoalaBear.Field :=
  testDomainOfLogN 3 (by decide)

def testDomain32 : Domain KoalaBear.Field :=
  testDomainOfLogN 5 (by decide)

def testDomain64 : Domain KoalaBear.Field :=
  testDomainOfLogN 6 (by decide)

end TestCommon
end NTT
end CPolynomial
end CompPoly
