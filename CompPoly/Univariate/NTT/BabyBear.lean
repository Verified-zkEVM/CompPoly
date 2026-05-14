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
def bitsOfLogN (logN : Nat) (hlogN : logN ≤ _root_.BabyBear.twoAdicity) :
    Fin (_root_.BabyBear.twoAdicity + 1) :=
  ⟨logN, Nat.lt_succ_of_le hlogN⟩

/-- The BabyBear NTT domain size is nonzero in the field for supported two-adic sizes. -/
theorem twoPowNatCast_ne_zero
    (logN : Nat) (hlogN : logN ≤ _root_.BabyBear.twoAdicity) :
    (((2 ^ logN : Nat) : _root_.BabyBear.Field) ≠ 0) := by
  intro hzero
  have hpow_pos : 0 < 2 ^ logN := by
    positivity
  have hpow_le : 2 ^ logN ≤ 2 ^ _root_.BabyBear.twoAdicity := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlogN
  have hpow_lt : 2 ^ logN < _root_.BabyBear.fieldSize := by
    have htop : 2 ^ _root_.BabyBear.twoAdicity < _root_.BabyBear.fieldSize := by
      simp [_root_.BabyBear.twoAdicity, _root_.BabyBear.fieldSize]
    exact lt_of_le_of_lt hpow_le htop
  have hdiv : _root_.BabyBear.fieldSize ∣ 2 ^ logN := by
    exact (ZMod.natCast_eq_zero_iff (2 ^ logN) _root_.BabyBear.fieldSize).mp hzero
  exact (not_le_of_gt hpow_lt) (Nat.le_of_dvd hpow_pos hdiv)

/-- BabyBear radix-2 NTT domain for a supported two-adic size. -/
def domainOfLogN (logN : Nat) (hlogN : logN ≤ _root_.BabyBear.twoAdicity) :
    Domain _root_.BabyBear.Field where
  logN := logN
  omega := _root_.BabyBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      _root_.BabyBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)
  natCast_ne_zero := twoPowNatCast_ne_zero logN hlogN

end BabyBear
end NTT
end CPolynomial
end CompPoly
