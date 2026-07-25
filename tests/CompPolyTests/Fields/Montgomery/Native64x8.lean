/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

import CompPoly.Fields.Montgomery.Native64x8Mul

/-!
# Eight-limb Montgomery arithmetic tests

Regression checks for the raw `Limbs8` operations against externally computed values for the
Vesta base field.  `montX` denotes the Montgomery representative `X * 2 ^ 256 mod q`.
-/

namespace CompPolyTests.Fields.Native64x8

open _root_.Montgomery.Native64x8

private def q : Limbs8 := Vesta.instMont64x8Field.modulusLimbs

private def negInv : UInt64 := Vesta.instMont64x8Field.montgomeryNegInv

private def rMod : Limbs8 := Vesta.instMont64x8Field.rModModulus

private def modulus : ℕ := Vesta.baseFieldSize

private def a : Limbs8 :=
  ⟨0x90abcdef, 0x12345678, 0x90abcdef, 0x12345678, 0x90abcdef, 0x12345678, 0x90abcdef,
    0x12345678⟩

private def b : Limbs8 :=
  ⟨0x98765432, 0x1fedcba0, 0x98765432, 0x1fedcba0, 0x98765432, 0x1fedcba0, 0x98765432,
    0xfedcba0⟩

private def montA : Limbs8 :=
  ⟨0x4657fff9, 0xb89185c2, 0x7fa63616, 0xac5206fd, 0xca71bcaa, 0x4a1382e8, 0xd2416c1e,
    0x3ec0c11b⟩

private def montB : Limbs8 :=
  ⟨0x96717045, 0xa13e865, 0xeda4684, 0x5fa53078, 0xadca6010, 0x8c0bc7ff, 0x6af4be5b,
    0x2bde1e93⟩

private def montAB : Limbs8 :=
  ⟨0x5bfbc390, 0xa6073176, 0x8f8933a9, 0xbed1aec1, 0x630437f1, 0xba615782, 0x92dc822b,
    0x77a4b3f⟩

-- the modulus limbs recompose to the Vesta base field size
#guard q.toNat = modulus

-- conditional subtraction
#guard condSub q q = Limbs8.zero
#guard condSub q Limbs8.zero = Limbs8.zero

-- addition
#guard (add q a b).toNat = (a.toNat + b.toNat) % modulus
#guard add q a (neg q a) = Limbs8.zero

-- subtraction and negation
#guard (sub q a b).toNat = (a.toNat + (modulus - b.toNat)) % modulus
#guard (sub q b a).toNat = (b.toNat + (modulus - a.toNat)) % modulus
#guard (neg q a).toNat = (modulus - a.toNat) % modulus
#guard neg q Limbs8.zero = Limbs8.zero

-- Montgomery multiplication
#guard mul q negInv montA montB = montAB
#guard mul q negInv rMod rMod = rMod
#guard mul q negInv rMod Limbs8.zero = Limbs8.zero
#guard square q negInv rMod = rMod

end CompPolyTests.Fields.Native64x8
