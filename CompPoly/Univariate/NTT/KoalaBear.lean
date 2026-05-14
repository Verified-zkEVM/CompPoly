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
def bitsOfLogN (logN : Nat) (hlogN : logN ≤ _root_.KoalaBear.twoAdicity) :
    Fin (_root_.KoalaBear.twoAdicity + 1) :=
  ⟨logN, Nat.lt_succ_of_le hlogN⟩

/-- The KoalaBear NTT domain size is nonzero in the field for supported two-adic sizes. -/
theorem twoPowNatCast_ne_zero
    (logN : Nat) (hlogN : logN ≤ _root_.KoalaBear.twoAdicity) :
    (((2 ^ logN : Nat) : _root_.KoalaBear.Field) ≠ 0) := by
  intro hzero
  have hpow_pos : 0 < 2 ^ logN := by
    positivity
  have hpow_le : 2 ^ logN ≤ 2 ^ _root_.KoalaBear.twoAdicity := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hlogN
  have hpow_lt : 2 ^ logN < _root_.KoalaBear.fieldSize := by
    have htop : 2 ^ _root_.KoalaBear.twoAdicity < _root_.KoalaBear.fieldSize := by
      simp [_root_.KoalaBear.twoAdicity, _root_.KoalaBear.fieldSize]
    exact lt_of_le_of_lt hpow_le htop
  have hdiv : _root_.KoalaBear.fieldSize ∣ 2 ^ logN := by
    exact (ZMod.natCast_eq_zero_iff (2 ^ logN) _root_.KoalaBear.fieldSize).mp hzero
  exact (not_le_of_gt hpow_lt) (Nat.le_of_dvd hpow_pos hdiv)

/-- KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def domainOfLogN (logN : Nat) (hlogN : logN ≤ _root_.KoalaBear.twoAdicity) :
    Domain _root_.KoalaBear.Field where
  logN := logN
  omega := _root_.KoalaBear.twoAdicGenerators[bitsOfLogN logN hlogN]
  primitive := by
    simpa [bitsOfLogN] using
      _root_.KoalaBear.isPrimitiveRoot_twoAdicGenerator (bitsOfLogN logN hlogN)
  natCast_ne_zero := twoPowNatCast_ne_zero logN hlogN

end KoalaBear
end NTT
end CPolynomial
end CompPoly
