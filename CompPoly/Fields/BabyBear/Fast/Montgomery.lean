/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import CompPoly.Fields.BabyBear.Fast.Prelude

/-!
# Fast BabyBear Field — Montgomery Reduction

The native-word Montgomery reducers specialized to BabyBear. The definitions and their
correctness proofs are shared across every fast 32-bit-word field; they live once in
`CompPoly.Fields.Montgomery.Native32Field`, parameterized by the `Mont32Field` instance
supplied in `CompPoly.Fields.BabyBear.Fast.Prelude`. This module just re-exports them at
the BabyBear instance. Because the shared definitions are `@[inline]`, fixing the instance
folds the constants to literals: the compiled code is identical to a hand-written
monomorphic reducer, with no `Mont32Field` dictionary at runtime.
-/

namespace BabyBear
namespace Fast

open Montgomery.Native32

/-- Reduce a native word known to be below twice the BabyBear prime. -/
@[inline]
def reduceUInt32Lt2ModulusRaw (x : UInt32) : UInt32 :=
  Montgomery.Native32.reduceUInt32Lt2ModulusRaw (F := BabyBear.Field) x

theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * BabyBear.fieldSize) :
    (reduceUInt32Lt2ModulusRaw x).toNat < BabyBear.fieldSize :=
  Montgomery.Native32.reduceUInt32Lt2ModulusRaw_lt (F := BabyBear.Field) x h

/-- Reduce a native word known to be below twice the BabyBear prime. -/
@[inline]
def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * BabyBear.fieldSize) :
    Field :=
  Montgomery.Native32.reduceUInt32Lt2Modulus (F := BabyBear.Field) x h

theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * BabyBear.fieldSize) :
    ((reduceUInt32Lt2Modulus x h).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) :=
  Montgomery.Native32.reduceUInt32Lt2Modulus_cast (F := BabyBear.Field) x h

/-- Reduce a native word below `2^32` modulo the BabyBear prime. -/
@[inline]
def reduceUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.reduceUInt32 (F := BabyBear.Field) x

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBoundedRaw (x : UInt64) : UInt32 :=
  Montgomery.Native32.montgomeryReduceBoundedRaw (F := BabyBear.Field) x

theorem montgomeryReduceBoundedRaw_lt (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    (montgomeryReduceBoundedRaw x).toNat < BabyBear.fieldSize :=
  Montgomery.Native32.montgomeryReduceBoundedRaw_lt (F := BabyBear.Field) x h

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceBounded (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) : Field :=
  Montgomery.Native32.montgomeryReduceBounded (F := BabyBear.Field) x h

theorem montgomeryReduceBounded_cast (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    ((montgomeryReduceBounded x h).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ :=
  Montgomery.Native32.montgomeryReduceBounded_cast (F := BabyBear.Field) x h

/-- Montgomery reduction of a 64-bit word. Hot bounded callers use `montgomeryReduceBounded`. -/
@[inline]
def montgomeryReduce (x : UInt64) : Field :=
  Montgomery.Native32.montgomeryReduce (F := BabyBear.Field) x

end Fast
end BabyBear
