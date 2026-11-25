/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.Pasta

/-!
# Fast Pasta Field Tests

Regression checks for the raw four-limb operations and the Pallas/Vesta fast-field
instantiations against externally computed values.
-/

public meta section

namespace CompPolyTests.Fields.Pasta

open _root_.Montgomery.Native64x4

private def q : Limbs4 := Vesta.Fast.instMont64x4Field.modulusLimbs

private def negInv : UInt64 := Vesta.Fast.instMont64x4Field.montgomeryNegInv

private def rMod : Limbs4 := Vesta.Fast.instMont64x4Field.rModModulus

private def modulus : ℕ := Vesta.baseFieldSize

private def a : Limbs4 :=
  ⟨0x1234567890abcdef, 0x1234567890abcdef, 0x1234567890abcdef, 0x1234567890abcdef⟩

private def b : Limbs4 :=
  ⟨0x1fedcba098765432, 0x1fedcba098765432, 0x1fedcba098765432, 0xfedcba098765432⟩

private def montA : Limbs4 :=
  ⟨0xb89185c24657fff9, 0xac5206fd7fa63616, 0x4a1382e8ca71bcaa, 0x3ec0c11bd2416c1e⟩

private def montB : Limbs4 :=
  ⟨0xa13e86596717045, 0x5fa530780eda4684, 0x8c0bc7ffadca6010, 0x2bde1e936af4be5b⟩

private def montAB : Limbs4 :=
  ⟨0xa60731765bfbc390, 0xbed1aec18f8933a9, 0xba615782630437f1, 0x77a4b3f92dc822b⟩

#guard q.toNat = modulus
#guard condSub q q = Limbs4.zero
#guard condSub q Limbs4.zero = Limbs4.zero
#guard (add q a b).toNat = (a.toNat + b.toNat) % modulus
#guard add q a (neg q a) = Limbs4.zero
#guard (sub q a b).toNat = (a.toNat + (modulus - b.toNat)) % modulus
#guard (sub q b a).toNat = (b.toNat + (modulus - a.toNat)) % modulus
#guard (neg q a).toNat = (modulus - a.toNat) % modulus
#guard neg q Limbs4.zero = Limbs4.zero
#guard mul q negInv montA montB = montAB
#guard mul q negInv rMod rMod = rMod
#guard mul q negInv rMod Limbs4.zero = Limbs4.zero
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

private def pq : Limbs4 := Pallas.Fast.instMont64x4Field.modulusLimbs

private def pNegInv : UInt64 := Pallas.Fast.instMont64x4Field.montgomeryNegInv

private def pMontA : Limbs4 :=
  ⟨0x4e0a938e73c65f1d, 0x6a1193bd71d5fef, 0xcb40dac3e42540dc, 0x335fa2c8c6cffd09⟩

private def pMontB : Limbs4 :=
  ⟨0x26211be35153d947, 0xcb94967838e82d52, 0xf369686fb6f80c7e, 0xd91e2967c2907b8⟩

private def pMontAB : Limbs4 :=
  ⟨0xe5c0528e8d6b3f08, 0xaec941cc22646fad, 0x4f5e09aafec4a4c0, 0x179b8aa169b735b5⟩

#guard pq.toNat = Pallas.baseFieldSize
#guard mul pq pNegInv pMontA pMontB = pMontAB
#guard (add pq a b).toNat = (a.toNat + b.toNat) % Pallas.baseFieldSize
#guard condSub pq pq = Limbs4.zero

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
