/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast.Arithmetic

/-!
# Extern-Backed Fast Goldilocks Operations

This module provides opt-in extern-backed multiplication and inversion routines
for the fast Goldilocks representation.

The verified implementation in `CompPoly.Fields.Goldilocks.Fast` remains the
default field implementation. The functions here move selected low-level
operations to external code for performance, so their arithmetic correctness
depends on the linked extern implementations.

These declarations are a trusted native boundary: Lean checks that the wrappers
have the stated types, but it does not verify the C implementations behind the
`@[extern]` symbols. Use this module when native performance is needed and the
linked C code is accepted as part of the trusted computing base.
-/

namespace Goldilocks
namespace Fast
namespace Ext

/-- High 64 bits of a 64-by-64 unsigned multiplication.

Together with Lean's native wrapping multiplication, this gives the two words of
the full 128-bit product.

This is an extern performance primitive. Its correctness is trusted from the
linked native implementation in `native/goldilocks_native.c`.
-/
@[extern "lean_uint64_mul_hi"]
opaque mulHi (a b : UInt64) : UInt64

/-- Extern Goldilocks multiplication returning a canonical `UInt64` representative.

This is an extern performance primitive. Lean does not verify that the native
routine implements Goldilocks multiplication correctly. The native symbol is
implemented in `native/goldilocks_native.c`.
-/
@[extern "lean_goldilocks_mul"]
opaque goldilocksMul (a b : UInt64) : UInt64

/-- Multiplication using extern `UInt64.mulHi` for the high word and Lean reduction. -/
@[inline]
def mulWithMulHi (x y : Field) : Field :=
  let lo := x.val * y.val
  let hi := mulHi x.val y.val
  ⟨Reduction.reduceUInt128Raw lo hi, Reduction.reduceUInt128Raw_lt lo hi⟩

/-- Multiplication using an extern Goldilocks multiplication primitive.

The external function is expected to return a canonical representative; this
wrapper still passes the result through `reduceUInt64` to inhabit the fast field
type safely.
-/
@[inline]
def mulNative (x y : Field) : Field :=
  reduceUInt64 (goldilocksMul x.val y.val)

/-- Squaring using extern `UInt64.mulHi` for multiplication. -/
@[inline]
def squareWithMulHi (x : Field) : Field :=
  mulWithMulHi x x

/-- Squaring using the extern Goldilocks multiplication primitive. -/
@[inline]
def squareNative (x : Field) : Field :=
  mulNative x x

/-- Repeated squaring using extern-backed multiplication. -/
@[inline]
def squareNNative (x : Field) : Nat → Field
  | 0 => x
  | n + 1 => squareNNative (squareNative x) n

/-- Inversion using the Goldilocks `p - 2` addition chain and extern multiplication. -/
@[noinline]
def invNative (x : Field) : Field :=
  let t2 := mulNative (squareNative x) x
  let t4 := mulNative (squareNNative t2 2) t2
  let t8 := mulNative (squareNNative t4 4) t4
  let t16 := mulNative (squareNNative t8 8) t8
  let t31 :=
    mulNative (squareNNative t16 15)
      (mulNative (squareNNative t8 7)
        (mulNative (squareNNative t4 3)
          (mulNative (squareNative t2) x)))
  let t32m2 := squareNative t31
  let t32m1 := mulNative t32m2 x
  mulNative (squareNNative t32m2 32) t32m1

/-- Division using extern-backed inversion and multiplication. -/
@[inline]
def divNative (x y : Field) : Field :=
  mulNative x (invNative y)

end Ext
end Fast
end Goldilocks
