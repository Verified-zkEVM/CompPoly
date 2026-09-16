/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Binary.Aes.Arithmetic
public import CompPoly.Fields.Binary.Aes.Arithmetic

/-!
# AES byte operations without field certificates

The arithmetic import supplies byte coordinates and executable reduced multiplication without
loading polynomial quotients, irreducibility certificates, or field laws. These checks exercise
modulus reduction and keep that import boundary explicit.
-/

public meta section

assert_not_exists Field AesField.modulus CompPoly.Extension.Ext.toQuot

open AesField

#guard ((ofBitVec (0x80#8)) * ofBitVec (2#8)).toBitVec == 0x1b#8
#guard ((ofBitVec (0x57#8)) * ofBitVec (0x13#8)).toBitVec == 0xfe#8
#guard ((ofBitVec (0x57#8)) * ofBitVec (0x83#8)).toBitVec == 0xc1#8
#guard ((ofBitVec (0x80#8)) + ofBitVec (0x01#8)).toBitVec == 0x81#8
#guard (0x80#8) * (2#8) == 0#8

example (a : BitVec 8) : toBitVec (ofBitVec a) = a := toBitVec_ofBitVec a
example (a : AesField) : ofBitVec (toBitVec a) = a := ofBitVec_toBitVec a
