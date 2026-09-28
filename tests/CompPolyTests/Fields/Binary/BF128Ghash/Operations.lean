/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF128Ghash.Impl
public import CompPoly.Fields.Binary.BF128Ghash.Impl

/-!
# Canonical GHASH operation regressions

These checks pass the synthesized field dictionary to generic callers, rather than relying
on standalone operation instances. They cover total inversion and division, binary powers,
and characteristic-two casts and scalar actions. Numeric guards are implementation checks;
the symbolic projection equalities and quotient agreement are kernel-checked proofs.
-/

public meta section

namespace CompPolyTests.GhashOperations

open BF128Ghash

private def inverse {F : Type*} [Field F] (a : F) : F := a⁻¹
private def divide {F : Type*} [Field F] (a b : F) : F := a / b
private def natPower {F : Type*} [Field F] (a : F) (n : ℕ) : F := a ^ n
private def intPower {F : Type*} [Field F] (a : F) (n : ℤ) : F := a ^ n
private def rationalCast {F : Type*} [Field F] (q : ℚ) : F := q
private def nnrationalCast {F : Type*} [Field F] (q : ℚ≥0) : F := q
private def rationalSmul {F : Type*} [Field F] (q : ℚ) (a : F) : F := q • a
private def nnrationalSmul {F : Type*} [Field F] (q : ℚ≥0) (a : F) : F := q • a

example (a : ConcreteBF128Ghash) : inverse a = invItohTsujii a := rfl
example (a b : ConcreteBF128Ghash) : divide a b = a * invItohTsujii b := rfl
example (a : ConcreteBF128Ghash) (n : ℕ) : natPower a n = npowBinRec n a := rfl
example (a : ConcreteBF128Ghash) (n : ℤ) :
    intPower a n = zpowRec npowBinRecAuto n a := rfl
example (a : ConcreteBF128Ghash) : toQuot (inverse a) = (toQuot a)⁻¹ := toQuot_inv a
example (n : ℕ) (a : ConcreteBF128Ghash) :
    (inferInstance : Field ConcreteBF128Ghash).nsmul n a = (if n % 2 = 0 then 0 else a) := rfl
example (n : ℤ) (a : ConcreteBF128Ghash) :
    (inferInstance : Field ConcreteBF128Ghash).zsmul n a = (if n % 2 = 0 then 0 else a) := rfl
example (q : ℚ) : rationalCast (F := ConcreteBF128Ghash) q = Rat.castRec q := rfl
example (q : ℚ≥0) : nnrationalCast (F := ConcreteBF128Ghash) q = NNRat.castRec q := rfl
example (q : ℚ) (a : ConcreteBF128Ghash) : rationalSmul q a = Rat.castRec q * a := rfl
example (q : ℚ≥0) (a : ConcreteBF128Ghash) : nnrationalSmul q a = NNRat.castRec q * a := rfl

private def high : ConcreteBF128Ghash := ofBitVec (0x80000000000000000000000000000000#128)

#guard (inverse (ofBitVec (2#128))).toBitVec == 0x80000000000000000000000000000043#128
#guard (inverse high).toBitVec == 0x0b604395d27ef1a8b604395d27ef1a8ee#128
#guard inverse (0 : ConcreteBF128Ghash) == 0
#guard divide high high == 1
#guard divide high 0 == 0
#guard divide (0 : ConcreteBF128Ghash) high == 0
#guard natPower high (2 ^ 128 - 2) == inverse high
#guard natPower (0 : ConcreteBF128Ghash) 0 == 1
#guard natPower (0 : ConcreteBF128Ghash) (2 ^ 128) == 0
#guard intPower high (-((2 ^ 128 - 1 : ℕ) : ℤ)) == 1
#guard intPower high (-1) == inverse high
#guard intPower (0 : ConcreteBF128Ghash) (-1) == 0
#guard (rationalCast (F := ConcreteBF128Ghash) (3 / 5)) == 1
#guard (rationalCast (F := ConcreteBF128Ghash) (1 / 2)) == 0
#guard (nnrationalCast (F := ConcreteBF128Ghash) (3 / 5)) == 1
#guard (nnrationalCast (F := ConcreteBF128Ghash) (1 / 2)) == 0
#guard rationalSmul (-3 / 5) high == high
#guard rationalSmul (1 / 2) high == 0
#guard nnrationalSmul (3 / 5) high == high
#guard nnrationalSmul (1 / 2) high == 0

end CompPolyTests.GhashOperations
