/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.BabyBear.FastExt4

/-!
# Fast BabyBear quartic extension tests

Compiled checks of `BabyBear.Fast.Ext4`: known answers computed with Plonky3's
`BinomialExtensionField<BabyBear, 4>` (`p3-field` 0.4.2), agreement with the spec field
`Ext4.Spec` over the fast base field, and the byte codec.
-/

public meta section

namespace CompPolyTests.Fields.BabyBear.FastExt4

open CompPoly BabyBear.Fast Montgomery.Native32

/-- An element from canonical coordinates. -/
def mk (a b c d : Nat) : Ext4 :=
  ⟨ofField (a : BabyBear.Field), ofField (b : BabyBear.Field), ofField (c : BabyBear.Field),
    ofField (d : BabyBear.Field)⟩

/-- Canonical coordinates. -/
def coords (x : Ext4) : List Nat :=
  [x.c0, x.c1, x.c2, x.c3].map fun c ↦ (FastField.toField c).val

def a : Ext4 := mk 1 2 3 4
def b : Ext4 := mk 2013265920 123456789 987654321 5

-- Known answers from Plonky3.
#guard coords (a * b) == [1785904840, 1301662735, 1234568116, 332413089]
#guard coords a⁻¹ == [1587469345, 920666518, 1160282443, 647153706]
#guard coords b⁻¹ == [1787456803, 987985264, 1366459329, 1869413295]

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

end CompPolyTests.Fields.BabyBear.FastExt4
