/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.KoalaBear.FastExt5

/-!
# Fast KoalaBear quintic extension tests

Compiled checks of `KoalaBear.Fast.Ext5`: known answers computed with Plonky3's
`QuinticTrinomialExtensionField<KoalaBear>` (revision `47e442f`), agreement with the spec field
`KoalaBear.Ext5`, and the byte codec.
-/

public meta section

namespace CompPolyTests.Fields.KoalaBear.FastExt5

open CompPoly KoalaBear.Fast Montgomery.Native32

/-- An element from canonical coordinates. -/
def mk (a b c d e : Nat) : Ext5 :=
  ⟨ofField (a : KoalaBear.Field), ofField (b : KoalaBear.Field), ofField (c : KoalaBear.Field),
    ofField (d : KoalaBear.Field), ofField (e : KoalaBear.Field)⟩

/-- Canonical coordinates. -/
def coords (x : Ext5) : List Nat :=
  [x.c0, x.c1, x.c2, x.c3, x.c4].map fun c ↦ (FastField.toField c).val

def a : Ext5 := mk 1 2 3 4 5
def b : Ext5 := mk 2130706432 123456789 987654321 5 42
def x : Ext5 := mk 0 1 0 0 0

-- Known answers from Plonky3.
#guard coords (a * b) == [306488251, 800315672, 928079837, 1668820335, 1326083540]
#guard coords (b * b) == [1070553826, 1749204957, 1899975306, 523365048, 1025025694]
#guard coords a⁻¹ == [1611162735, 1325413701, 869369788, 708311242, 352135173]
#guard coords b⁻¹ == [1101584238, 1628058112, 1159448964, 1870579729, 1078787205]
#guard coords (x * x * x * x * x) == [1, 0, 2130706432, 0, 0]
#guard coords (x * x * x * x * x * x * x * x) == [2130706432, 0, 1, 1, 0]

-- Field laws on the fast carrier.
#guard a * a⁻¹ == 1
#guard b * b⁻¹ == 1
#guard (0 : Ext5)⁻¹ == 0
#guard (a + b) * b == a * b + b * b
#guard (a - b) * a == a * a - b * a
#guard a / b * b == a

-- Agreement with the spec field, including its inverse.
#guard Ext5.toSpec (a * b) == Ext5.toSpec a * Ext5.toSpec b
#guard Ext5.toSpec a⁻¹ == (Ext5.toSpec a)⁻¹
#guard Ext5.ofSpec (Ext5.toSpec b) == b

-- The codec round-trips and matches the spec field's encoding.
#guard ByteCodec.ofBytes? (ByteCodec.toBytes b) == some b
#guard (ByteCodec.toBytes (Ext5.toSpec b)).toList == (ByteCodec.toBytes b).toList

end CompPolyTests.Fields.KoalaBear.FastExt5
