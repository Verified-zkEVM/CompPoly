/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.KoalaBear.Fast.Defs

/-!
# Fast KoalaBear Field — Conversions

Conversions between the fast Montgomery representation and the canonical
`KoalaBear.Field` / `Nat` views, re-exported from the shared implementation in
`CompPoly.Fields.Montgomery.Native32Field` at the KoalaBear instance.
-/

namespace KoalaBear
namespace Fast

/-- Reduce a `UInt64` modulo the KoalaBear prime and return a Montgomery fast element. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  Montgomery.Native32.reduceUInt64 KoalaBear.fieldSize x

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.FastField.ofUInt32 KoalaBear.fieldSize x

/-- Convert from the canonical `ZMod` KoalaBear field into fast Montgomery form. -/
@[inline]
def ofField (x : KoalaBear.Field) : Field :=
  Montgomery.Native32.ofField x

/-- Reducing a `UInt64` gives the canonical natural residue modulo KoalaBear. -/
@[simp]
theorem toNat_reduceUInt64 (x : UInt64) :
    (reduceUInt64 x).toNat = x.toNat % KoalaBear.fieldSize :=
  Montgomery.Native32.toNat_reduceUInt64 x

/-- Reducing a `UInt64` agrees with casting that word into the canonical field. -/
@[simp]
theorem toField_reduceUInt64 (x : UInt64) :
    (reduceUInt64 x).toField = (x.toNat : KoalaBear.Field) :=
  Montgomery.Native32.toField_reduceUInt64 x

end Fast
end KoalaBear
