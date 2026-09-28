/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Tower.Concrete.Field
public import CompPoly.Fields.Binary.Tower.Concrete.Field

/-!
# Canonical tower power regressions

Symbolic checks identify natural and integer powers with the actual field projections and
binary algorithms. Executable checks cover large exponents, zero, and a tower product that
differs from integer multiplication of the underlying words.
-/

public meta section

namespace CompPolyTests.TowerPowers

open ConcreteBinaryTower

private def natPower {F : Type*} [Field F] (a : F) (n : ℕ) : F := a ^ n
private def intPower {F : Type*} [Field F] (a : F) (n : ℤ) : F := a ^ n

example (p : ConcreteBTFieldProps k) (a : ConcreteBTField k) (n : ℕ) :
    (mkFieldInstance p).npow n a = @npowBinRec _ _ ⟨concrete_mul⟩ n a := rfl
example (p : ConcreteBTFieldProps k) (a : ConcreteBTField k) (n : ℤ) :
    (mkFieldInstance p).zpow n a =
      @zpowRec _ _ ⟨concrete_mul⟩ ⟨concrete_inv⟩ (@npowBinRec _ _ ⟨concrete_mul⟩) n a := rfl

example (a : ConcreteBTField k) (n : ℕ) : natPower a n = a ^ n := rfl
example (a : ConcreteBTField k) (n : ℤ) : intPower a n = a ^ n := rfl
example (a : ConcreteBTField k) (n : ℕ) :
    (inferInstance : Field (ConcreteBTField k)).npow n a = npowBinRec n a := rfl
example (a : ConcreteBTField k) (n : ℤ) :
    (inferInstance : Field (ConcreteBTField k)).zpow n a = zpowRec npowBinRec n a := rfl
example (a : ConcreteBTField k) (n : ℕ) : concrete_pow_nat a n = natPower a n :=
  concrete_pow_nat_eq_pow a n
example (a : ConcreteBTField k) (n : ℕ) :
    intPower a (-(n : ℤ)) = (natPower a n)⁻¹ := by simp [intPower, natPower]

-- The first tower generator has order three, and its square is word three, not zero.
#guard (natPower (F := ConcreteBTField 1) (fromNat 2) 2).toNat == 3
#guard (natPower (F := ConcreteBTField 1) (fromNat 2) (2 ^ 128)).toNat == 2
#guard (intPower (F := ConcreteBTField 1) (fromNat 2) (-((2 ^ 128 : ℕ) : ℤ))).toNat == 3
#guard natPower (0 : ConcreteBTField 3) 0 == 1
#guard natPower (0 : ConcreteBTField 3) (2 ^ 128) == 0
#guard intPower (0 : ConcreteBTField 3) 0 == 1
#guard intPower (0 : ConcreteBTField 3) (-((2 ^ 128 : ℕ) : ℤ)) == 0
#guard natPower (F := ConcreteBTField 3) (fromNat 0x80) (2 ^ 128) == fromNat (k := 3) 0x80
#guard intPower (F := ConcreteBTField 3) (fromNat 0x80) (-((2 ^ 128 : ℕ) : ℤ)) ==
  concrete_inv (k := 3) (fromNat 0x80)

end CompPolyTests.TowerPowers
