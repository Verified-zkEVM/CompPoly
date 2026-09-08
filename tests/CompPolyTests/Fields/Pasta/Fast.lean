/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.Pasta

/-!
# Fast Pasta Field Tests

Regression checks for the raw eight-limb operations and the Pallas/Vesta fast-field
instantiations against externally computed values.
-/

public meta section

namespace CompPolyTests.Fields.Pasta

open _root_.Montgomery.Native64x8

private def q : Limbs8 := Vesta.Fast.instMont64x8Field.modulusLimbs

private def negInv : UInt64 := Vesta.Fast.instMont64x8Field.montgomeryNegInv

private def rMod : Limbs8 := Vesta.Fast.instMont64x8Field.rModModulus

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

#guard q.toNat = modulus
#guard condSub q q = Limbs8.zero
#guard condSub q Limbs8.zero = Limbs8.zero
#guard (add q a b).toNat = (a.toNat + b.toNat) % modulus
#guard add q a (neg q a) = Limbs8.zero
#guard (sub q a b).toNat = (a.toNat + (modulus - b.toNat)) % modulus
#guard (sub q b a).toNat = (b.toNat + (modulus - a.toNat)) % modulus
#guard (neg q a).toNat = (modulus - a.toNat) % modulus
#guard neg q Limbs8.zero = Limbs8.zero
#guard mul q negInv montA montB = montAB
#guard mul q negInv rMod rMod = rMod
#guard mul q negInv rMod Limbs8.zero = Limbs8.zero
#guard square q negInv rMod = rMod

private abbrev F := Vesta.Fast.Field

#guard (0 : F).toNat = 0
#guard (1 : F).toNat = 1
#guard (37 : F).toNat = 37
#guard ((Vesta.baseFieldSize : F)).toNat = 0
#guard ((12345 : F) * 12345).toNat = 12345 * 12345
#guard ((0 : F) - 1).toNat = Vesta.baseFieldSize - 1
#guard (-(1 : F)).toNat = Vesta.baseFieldSize - 1
#guard (((Vesta.baseFieldSize - 1 : ℕ) : F) * ((Vesta.baseFieldSize - 1 : ℕ) : F)).toNat = 1
#guard ((123456789 : F) ^ 17).toNat = 123456789 ^ 17 % Vesta.baseFieldSize
#guard ((37 : F)⁻¹ * 37).toNat = 1
#guard ((37 : F) / 37).toNat = 1
#guard ((0 : F)⁻¹).toNat = 0

private def pq : Limbs8 := Pallas.Fast.instMont64x8Field.modulusLimbs

private def pNegInv : UInt64 := Pallas.Fast.instMont64x8Field.montgomeryNegInv

private def pMontA : Limbs8 :=
  ⟨0x73c65f1d, 0x4e0a938e, 0xd71d5fef, 0x6a1193b, 0xe42540dc, 0xcb40dac3, 0xc6cffd09,
    0x335fa2c8⟩

private def pMontB : Limbs8 :=
  ⟨0x5153d947, 0x26211be3, 0x38e82d52, 0xcb949678, 0xb6f80c7e, 0xf369686f, 0x7c2907b8,
    0xd91e296⟩

private def pMontAB : Limbs8 :=
  ⟨0x8d6b3f08, 0xe5c0528e, 0x22646fad, 0xaec941cc, 0xfec4a4c0, 0x4f5e09aa, 0x69b735b5,
    0x179b8aa1⟩

#guard pq.toNat = Pallas.baseFieldSize
#guard mul pq pNegInv pMontA pMontB = pMontAB
#guard (add pq a b).toNat = (a.toNat + b.toNat) % Pallas.baseFieldSize
#guard condSub pq pq = Limbs8.zero

private abbrev G := Pallas.Fast.Field

#guard (37 : G).toNat = 37
#guard ((12345 : G) * 12345).toNat = 12345 * 12345
#guard ((37 : G)⁻¹ * 37).toNat = 1

#guard ((123456789 : F) ^ 17).toField = ((123456789 : Vesta.BaseField) ^ 17)
#guard ((37 : F)⁻¹).toField = ((37 : Vesta.BaseField)⁻¹)
#guard Vesta.Fast.ofField ((37 : Vesta.BaseField)⁻¹) = (37 : F)⁻¹
#guard ((123456789 : G) ^ 17).toField = ((123456789 : Pallas.BaseField) ^ 17)
#guard ((37 : G)⁻¹).toField = ((37 : Pallas.BaseField)⁻¹)

end CompPolyTests.Fields.Pasta
