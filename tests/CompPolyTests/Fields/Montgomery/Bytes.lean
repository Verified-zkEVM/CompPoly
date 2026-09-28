/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Fields.Montgomery.Native32Bytes
public meta import CompPoly.Fields.Montgomery.Native64x8Bytes
public meta import CompPoly.Fields.BabyBear.Fast
public meta import CompPoly.Fields.KoalaBear.Fast
public meta import CompPoly.Fields.BN254.Fast
public meta import CompPoly.Fields.BLS12_381.Fast
public import CompPoly.Fields.Montgomery.Native32Bytes
public import CompPoly.Fields.Montgomery.Native64x8Bytes
public import CompPoly.Fields.BabyBear.Fast
public import CompPoly.Fields.KoalaBear.Fast
public import CompPoly.Fields.BN254.Fast
public import CompPoly.Fields.BLS12_381.Fast

/-!
# Serialization of the Montgomery carriers

The fast carriers store Montgomery residues. Checked here: their bytes are the bytes of the
abstract element (they agree with the `ZMod` codec under `ofField`), decoding lands on the
converted element, and a stored word is never emitted raw.
-/

public meta section

namespace CompPolyTests.MontgomeryBytes

open CompPoly

/-! ## Widths -/

example : ByteCodec.width BabyBear.Fast.Field = 4 := by decide
example : ByteCodec.width BN254.Fast.ScalarField = 32 := by decide
#guard ByteCodec.width KoalaBear.Fast.Field = 4
#guard ByteCodec.width BLS12_381.Fast.ScalarField = 32

/-! ## Agreement with the spec field -/

#guard (ByteCodec.toBytes (BabyBear.Fast.ofField (-1))).toList
  = (ByteCodec.toBytes (-1 : BabyBear.Field)).toList
#guard (ByteCodec.toBytes (BabyBear.Fast.ofField 12345)).toList
  = (ByteCodec.toBytes (12345 : BabyBear.Field)).toList
#guard (ByteCodec.toBytes (KoalaBear.Fast.ofField (-2))).toList
  = (ByteCodec.toBytes (-2 : KoalaBear.Field)).toList
#guard (ByteCodec.toBytes (BN254.Fast.ofField (-1))).toList
  = (ByteCodec.toBytes (-1 : BN254.ScalarField)).toList
#guard (ByteCodec.toBytes (BLS12_381.Fast.ofField 7)).toList
  = (ByteCodec.toBytes (7 : BLS12_381.ScalarField)).toList

-- The canonical value, not the Montgomery word: `1` in BabyBear is stored as `R mod p`.
#guard (ByteCodec.toBytes (1 : BabyBear.Fast.Field)).toList = [1, 0, 0, 0]
#guard (1 : BabyBear.Fast.Field).val ≠ 1

/-! ## Round trips -/

#guard (ByteCodec.ofBytes? (ByteCodec.toBytes (BabyBear.Fast.ofField 99)) :
  Option BabyBear.Fast.Field) = some (BabyBear.Fast.ofField 99)
#guard (DeserializeOption.deserialize (serialize (BN254.Fast.ofField (-5)) : ByteArray) :
  Option BN254.Fast.ScalarField) = some (BN254.Fast.ofField (-5))
#guard (Deserialize.deserialize (serialize (KoalaBear.Fast.ofField 77) : ByteArray) :
  KoalaBear.Fast.Field) = KoalaBear.Fast.ofField 77
-- Decoding the spec field's bytes gives the converted element.
#guard (ByteCodec.ofByteArray? (ByteCodec.toByteArray (-1 : BabyBear.Field)) :
  Option BabyBear.Fast.Field) = some (BabyBear.Fast.ofField (-1))
#guard (ByteCodec.ofByteArray? (ByteCodec.toByteArray (BN254.Fast.ofField 9)) :
  Option BN254.ScalarField) = some 9
-- Out of range is refused.
#guard (ByteCodec.ofByteArray? ⟨#[0xff, 0xff, 0xff, 0xff]⟩ : Option BabyBear.Fast.Field) = none

/-! ## The agreement theorems, at the concrete fields -/

example (n : BabyBear.Field) :
    ByteCodec.toBytes (BabyBear.Fast.ofField n) = ByteCodec.toBytes n :=
  Montgomery.Native32.FastField.toBytes_ofField n
example (n : BN254.ScalarField) :
    ByteCodec.toBytes (BN254.Fast.ofField n) = ByteCodec.toBytes n :=
  Montgomery.Native64x8.FastField.toBytes_ofField n
example (x : BabyBear.Fast.Field) :
    (Deserialize.deserialize (serialize x : ByteArray) : BabyBear.Fast.Field) = x :=
  CanonicalNat.deserialize_serialize_byteArray rfl x
example : Serialize.IsInjective BabyBear.Fast.Field ByteArray := inferInstance

end CompPolyTests.MontgomeryBytes
