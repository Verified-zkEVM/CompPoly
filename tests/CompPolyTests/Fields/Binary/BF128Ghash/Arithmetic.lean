/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.BF128Ghash.Arithmetic
public import CompPoly.Fields.Binary.BF128Ghash.Arithmetic

/-!
# Standalone GHASH arithmetic

The word algorithms and nominal arithmetic compile without polynomial quotients or
irreducibility certificates. These checks protect that import boundary and distinguish
polynomial multiplication and explicit coordinates from ordinary word arithmetic.
-/

public meta section

namespace CompPolyTests.GhashArithmetic

open BF128Ghash BinaryField

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    if name == `CompPoly.Fields.Binary.Common ||
        name == `CompPoly.Fields.Binary.BF128Ghash.Impl ||
        name == `CompPoly.Fields.Binary.BF128Ghash.Basic ||
        name == `CompPoly.Fields.Binary.BF128Ghash.Prelude ||
        name.toString.startsWith "CompPoly.Fields.Binary.BF128Ghash.XPow" ||
        name.toString.startsWith "Mathlib.FieldTheory." ||
        name.toString.startsWith "Mathlib.RingTheory.AdjoinRoot" then
      throwError "Arithmetic imported field certificates: {name}"
  for name in #[`Polynomial, `AdjoinRoot, `BF128Ghash.ghashPoly,
      `BF128Ghash.toQuot, `BF128Ghash.instFieldConcreteBF128Ghash] do
    if env.contains name then
      throwError "Arithmetic exposed a certificate declaration: {name}"

example (x : ConcreteBF128Ghash) : ofBitVec x.toBitVec = x := ofBitVec_toBitVec x

example (_x : ConcreteBF128Ghash) (_word : BitVec 128) : True := by
  fail_if_success
    let _raw : BitVec 128 := _x
  fail_if_success
    let _field : ConcreteBF128Ghash := _word
  trivial

#guard (carryLessMul (w := 16) (3#8) (3#8)).toNat == 5
#guard (clMul (BitVec.ofNat 128 (2 ^ 127)) (BitVec.ofNat 128 (2 ^ 127))).toNat ==
  2 ^ 254
#guard (reduce_clMul (BitVec.ofNat 256 (2 ^ 128))).toNat == 135
#guard ((ofBitVec (BitVec.ofNat 128 (2 ^ 127))) * ofBitVec 2).toBitVec.toNat == 135
#guard ((ofBitVec 3) * ofBitVec 3).toBitVec.toNat == 5
#guard ((2 : Nat) : ConcreteBF128Ghash) == 0
#guard ((-3 : Int) : ConcreteBF128Ghash) == 1
#guard (invItohTsujii (ofBitVec 2)).toBitVec.toNat ==
  0x80000000000000000000000000000043
#guard (invItohTsujii 0).toBitVec.toNat == 0
#guard (invItohTsujii 1).toBitVec.toNat == 1

end CompPolyTests.GhashArithmetic
