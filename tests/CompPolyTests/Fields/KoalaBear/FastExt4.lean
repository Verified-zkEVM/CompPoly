/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.KoalaBear.FastExt4

/-!
# Fast KoalaBear quartic extension tests

Compiled checks of `KoalaBear.Fast.Ext4`: known answers computed with Plonky3's
`BinomialExtensionField<KoalaBear, 4>` (`p3-field` 0.4.2), agreement with the spec field
`KoalaBear.Ext4`, and the byte codec.
-/

public meta section

namespace CompPolyTests.Fields.KoalaBear.FastExt4

open CompPoly KoalaBear.Fast Montgomery.Native32

/-- An element from canonical coordinates. -/
def mk (a b c d : Nat) : Ext4 :=
  ⟨ofField (a : KoalaBear.Field), ofField (b : KoalaBear.Field), ofField (c : KoalaBear.Field),
    ofField (d : KoalaBear.Field)⟩

/-- Canonical coordinates. -/
def coords (x : Ext4) : List Nat :=
  [x.c0, x.c1, x.c2, x.c3].map fun c ↦ (FastField.toField c).val

def a : Ext4 := mk 1 2 3 4
def b : Ext4 := mk 2130706432 123456789 987654321 5

-- Known answers from Plonky3.
#guard coords (a * b) == [1847544654, 1321776519, 1234567956, 214972577]
#guard coords a⁻¹ == [476435702, 408373459, 502227710, 126094261]
#guard coords b⁻¹ == [1900592659, 1697951523, 2029979453, 1087580901]

-- Field laws on the fast carrier.
#guard a * a⁻¹ == 1
#guard b * b⁻¹ == 1
#guard (0 : Ext4)⁻¹ == 0
#guard (a + b) * b == a * b + b * b
#guard (a - b) * a == a * a - b * a
#guard a / b * b == a

-- Agreement with the spec field, including its Fermat inverse.
#guard Ext4.toSpec (a * b) == Ext4.toSpec a * Ext4.toSpec b
#guard Ext4.toSpec a⁻¹ == (Ext4.toSpec a)⁻¹
#guard Ext4.ofSpec (Ext4.toSpec b) == b

-- The codec round-trips and matches the spec field's encoding.
#guard ByteCodec.ofBytes? (ByteCodec.toBytes b) == some b
#guard (ByteCodec.toBytes (Ext4.toSpec b)).toList == (ByteCodec.toBytes b).toList

end CompPolyTests.Fields.KoalaBear.FastExt4
