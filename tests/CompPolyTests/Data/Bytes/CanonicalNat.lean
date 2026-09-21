/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Data.Bytes.CanonicalNat
public meta import CompPoly.Fields.BabyBear.Basic
public meta import CompPoly.Fields.Goldilocks.Basic
public meta import CompPoly.Fields.BN254.Basic
public import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Fields.BabyBear.Basic
public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.BN254.Basic

/-!
# `CanonicalNat` and `ByteCodec` on `ZMod`

The spec prime fields serialize through `instCanonicalNatZMod` and `instByteCodecZMod`. Checked
here: widths, known byte vectors, round trips through every derived interface, rejection of an
out-of-range exact-width string, and the reduce-modulo-order challenge decoder.
-/

public meta section

namespace CompPolyTests.CanonicalNat

open CompPoly CompPoly.Bytes

/-! ## Widths, in the kernel and at runtime -/

example : ByteCodec.width BabyBear.Field = 4 := by decide
example : ByteCodec.width Goldilocks.Field = 8 := by decide
example : ByteCodec.width BN254.ScalarField = 32 := by decide
example : HasSize.size BabyBear.Field UInt8 = 4 := by decide

#guard ByteCodec.width BabyBear.Field = 4
#guard ByteCodec.width Goldilocks.Field = 8
#guard ByteCodec.width BN254.ScalarField = 32

/-! ## Known vectors -/

-- BabyBear `p = 0x78000001`, so `-1 = 0x78000000`.
#guard (ByteCodec.toBytes (1 : BabyBear.Field)).toList = [1, 0, 0, 0]
#guard (ByteCodec.toBytes (-1 : BabyBear.Field)).toList = [0x00, 0x00, 0x00, 0x78]
#guard (ByteCodec.toByteArray (-1 : BabyBear.Field)).data = #[0x00, 0x00, 0x00, 0x78]
#guard (serialize (-1 : BabyBear.Field) : ByteArray).data = #[0x00, 0x00, 0x00, 0x78]

-- Goldilocks `p = 0xFFFFFFFF00000001`, so `-1 = 0xFFFFFFFF00000000`.
#guard (ByteCodec.toBytes (-1 : Goldilocks.Field)).toList = [0, 0, 0, 0, 0xff, 0xff, 0xff, 0xff]
#guard (ByteCodec.toBytes (2 ^ 32 : Goldilocks.Field)).toList = [0, 0, 0, 0, 1, 0, 0, 0]

-- The kernel evaluates an encoding.
example : (ByteCodec.toBytes (-1 : BabyBear.Field)).toList = [0x00, 0x00, 0x00, 0x78] := by
  decide

-- BN254 scalar field `r = 0x30644e72...f0000001`, 32 bytes, `r - 1` least significant first.
#guard (ByteCodec.toBytes (0 : BN254.ScalarField)).toList = List.replicate 32 0
#guard (ByteCodec.toBytes (-1 : BN254.ScalarField)).toList =
  [0x00, 0x00, 0x00, 0xf0, 0x93, 0xf5, 0xe1, 0x43, 0x91, 0x70, 0xb9, 0x79, 0x48, 0xe8, 0x33, 0x28,
   0x5d, 0x58, 0x81, 0x81, 0xb6, 0x45, 0x50, 0xb8, 0x29, 0xa0, 0x31, 0xe1, 0x72, 0x4e, 0x64, 0x30]

/-! ## Round trips -/

#guard (ByteCodec.ofBytes? (ByteCodec.toBytes (12345 : BabyBear.Field)) :
  Option BabyBear.Field) = some 12345
#guard (DeserializeOption.deserialize (serialize (12345 : BabyBear.Field) : ByteArray) :
  Option BabyBear.Field) = some 12345
-- Fixed-width vector instances are stated at `ByteCodec.width F`, not at a literal.
#guard (DeserializeOption.deserialize
  (serialize (-7 : Goldilocks.Field) : Vector UInt8 (ByteCodec.width Goldilocks.Field)) :
  Option Goldilocks.Field) = some (-7)
#guard (DeserializeOption.deserialize (serialize (-7 : BN254.ScalarField) : ByteArray) :
  Option BN254.ScalarField) = some (-7)

/-! ## Rejection -/

-- `0xffffffff ≥ p`, so the exact-width decoder refuses it.
#guard (ByteCodec.ofByteArray? ⟨#[0xff, 0xff, 0xff, 0xff]⟩ : Option BabyBear.Field) = none
-- `p` itself is not a canonical residue.
#guard (ByteCodec.ofByteArray? ⟨#[0x01, 0x00, 0x00, 0x78]⟩ : Option BabyBear.Field) = none
-- `p - 1` is.
#guard (ByteCodec.ofByteArray? ⟨#[0x00, 0x00, 0x00, 0x78]⟩ : Option BabyBear.Field) = some (-1)
-- Wrong size.
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 0]⟩ : Option BabyBear.Field) = none
#guard (ByteCodec.ofByteArray? ⟨#[1, 0, 0, 0, 0]⟩ : Option BabyBear.Field) = none

/-! ## Reduce modulo the order -/

-- `1 + 2^32 ≡ 1 + 2^32 - 2p = 268435455 (mod p)`.
#guard (Deserialize.deserialize (⟨#[1, 0, 0, 0, 1, 0, 0, 0]⟩ : ByteArray) : BabyBear.Field)
  = 268435455
#guard (Deserialize.deserialize (#v[1, 0, 0, 0, 1, 0, 0, 0] : Vector UInt8 8) : BabyBear.Field)
  = 268435455
-- An exact-width encoding reads back as the element.
#guard (Deserialize.deserialize (serialize (-1 : BabyBear.Field) : ByteArray) : BabyBear.Field)
  = -1
-- The residue itself, at any width.
#guard (Deserialize.deserialize (⟨#[0x01, 0x00, 0x00, 0x78]⟩ : ByteArray) : BabyBear.Field) = 0

/-! ## Class laws are usable as stated -/

example (x : BabyBear.Field) : CanonicalNat.toNat x = x.val := rfl
example : CanonicalNat.bound BabyBear.Field = BabyBear.fieldSize := rfl
example : Fintype.card BabyBear.Field = CanonicalNat.bound BabyBear.Field :=
  CanonicalNat.card_eq
example : Serialize.IsInjective BabyBear.Field ByteArray := inferInstance
example : Serde Goldilocks.Field ByteArray := inferInstance
example : HasSize BN254.ScalarField UInt8 := inferInstance
example (n : ℕ) : Deserialize BabyBear.Field (Vector UInt8 n) := inferInstance

end CompPolyTests.CanonicalNat
