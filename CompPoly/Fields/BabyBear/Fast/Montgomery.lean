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
  Montgomery.Native32.reduceUInt32Lt2ModulusRaw BabyBear.fieldSize x

theorem reduceUInt32Lt2ModulusRaw_lt (x : UInt32)
    (h : x.toNat < 2 * BabyBear.fieldSize) :
    (reduceUInt32Lt2ModulusRaw x).toNat < BabyBear.fieldSize :=
  Montgomery.Native32.reduceUInt32Lt2ModulusRaw_lt x h

/-- Reduce a native word known to be below twice the BabyBear prime. -/
@[inline]
def reduceUInt32Lt2Modulus (x : UInt32) (h : x.toNat < 2 * BabyBear.fieldSize) : Field :=
  Montgomery.Native32.reduceUInt32Lt2Modulus x h

theorem reduceUInt32Lt2Modulus_cast (x : UInt32)
    (h : x.toNat < 2 * BabyBear.fieldSize) :
    ((reduceUInt32Lt2Modulus x h).val.toNat : BabyBear.Field) = (x.toNat : BabyBear.Field) :=
  Montgomery.Native32.reduceUInt32Lt2Modulus_cast x h

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduceRaw (x : UInt64) : UInt32 :=
  Montgomery.Native32.montgomeryReduceRaw BabyBear.fieldSize x

theorem montgomeryReduceRaw_lt (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    (montgomeryReduceRaw x).toNat < BabyBear.fieldSize :=
  Montgomery.Native32.montgomeryReduceRaw_lt x h

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def montgomeryReduce (x : UInt64) (h : x.toNat < BabyBear.fieldSize * UInt32.size) : Field :=
  Montgomery.Native32.montgomeryReduce x h

theorem montgomeryReduce_cast (x : UInt64)
    (h : x.toNat < BabyBear.fieldSize * UInt32.size) :
    ((montgomeryReduce x h).val.toNat : BabyBear.Field) =
      (x.toNat : BabyBear.Field) * (UInt32.size : BabyBear.Field)⁻¹ :=
  Montgomery.Native32.montgomeryReduce_cast x h

end Fast
end BabyBear
