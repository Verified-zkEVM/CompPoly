/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

/-!
# Fast Goldilocks: runtime definitions (zero-import)

The runtime definitions of the native-word Goldilocks arithmetic, split out of
`CompPoly.Fields.Goldilocks.Fast` verbatim. All correctness statements about them
live in that sibling module, which imports this one.

This module deliberately has **zero imports**: downstream consumers put it into
`precompileModules` native-compilation lanes, and `precompileModules` compiles the
entire import closure, so the runtime definitions must not pull in mathlib.
-/

@[expose] public section

namespace Goldilocks.Fast

/-! ## Word constants -/

/-- Goldilocks modulus `2^64 - 2^32 + 1` as a native word. -/
@[inline]
def modulus : UInt64 := 0xffffffff00000001

/-- Two's complement of the modulus: `2^64 - modulus = 2^32 - 1 = 0xFFFFFFFF`. -/
@[inline]
def negModulus : UInt64 := 0xffffffff

/-! ## Raw word kernels

Every kernel takes canonical `UInt64` inputs and returns a canonical representative
below the modulus. Correctness lives in `CompPoly.Fields.Goldilocks.Fast`. -/


/-- Full 64-by-64 product as `(lo, hi)` words, computed from 32-bit limbs. -/
@[inline]
def wideMul (x y : UInt64) : UInt64 × UInt64 :=
  let xLo := x &&& negModulus
  let xHi := x >>> 32
  let yLo := y &&& negModulus
  let yHi := y >>> 32
  let p00 := xLo * yLo
  let p01 := xLo * yHi
  let p10 := xHi * yLo
  let p11 := xHi * yHi
  let carry := (p00 >>> 32) + (p01 &&& negModulus) + (p10 &&& negModulus)
  let hi := p11 + (p01 >>> 32) + (p10 >>> 32) + (carry >>> 32)
  (x * y, hi)

/-- Raw one-word reduction for a `UInt64` value.

Since every `UInt64` is below `2^64 = p + 2^32 - 1`, one subtraction by `p`
is enough to canonicalize a native word.
-/
@[inline]
def reduceUInt64Raw (x : UInt64) : UInt64 :=
  if x < modulus then x else x - modulus

/-- Raw reduction of a 128-bit integer represented by low and high words modulo Goldilocks. -/
@[inline]
def reduceUInt128Raw (lo hi : UInt64) : UInt64 :=
  let hi_hi := hi >>> 32
  let hi_lo := hi &&& negModulus

  let borrow := lo < hi_hi
  let t0 := lo - hi_hi
  let t0 := if borrow then t0 - negModulus else t0

  let t1 := hi_lo * negModulus

  let t2 := t0 + t1
  let overflow := t2 < t0
  let t2 := if overflow then t2 + negModulus else t2

  reduceUInt64Raw t2

/-- Raw reduction of a 64-by-64 product modulo Goldilocks. -/
@[inline]
def reduceMulRaw (x y : UInt64) : UInt64 :=
  let product := wideMul x y
  reduceUInt128Raw product.1 product.2

/-- Raw one-step reduction for a 65-bit addition represented by low word and carry. -/
@[inline]
def reduceAddWithCarryRaw (lo : UInt64) (carry : Bool) : UInt64 :=
  if carry then
    lo + negModulus
  else
    reduceUInt64Raw lo

/-- Raw modular negation in canonical form. -/
@[inline]
def negRaw (x : UInt64) : UInt64 :=
  if x = 0 then 0 else modulus - x

/-- Raw modular subtraction in canonical form. -/
@[inline]
def subRaw (x y : UInt64) : UInt64 :=
  if y ≤ x then x - y else x - y - negModulus

end Goldilocks.Fast
