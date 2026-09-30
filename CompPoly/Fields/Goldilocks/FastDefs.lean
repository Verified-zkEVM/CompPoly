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
below the modulus, except the `Lazy` kernels: those accept and return arbitrary words
congruent to the intended value, so a chain of them pays one canonicalization at the
end instead of one per step. Correctness lives in `CompPoly.Fields.Goldilocks.Fast`. -/


/-- Full 64-by-64 product as `(lo, hi)` words, computed from 32-bit limbs.

The middle terms are folded through `t` and `u`, which never overflow, so no carry
bookkeeping is needed. This shape is also what lets clang fuse the four limb
products into one widening multiply even when `x` and `y` are the same word. -/
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
  let t := (p00 >>> 32) + p01
  let u := (t &&& negModulus) + p10
  let hi := p11 + (t >>> 32) + (u >>> 32)
  (x * y, hi)

/-- Raw one-word reduction for a `UInt64` value.

Since every `UInt64` is below `2^64 = p + 2^32 - 1`, one subtraction by `p`
is enough to canonicalize a native word.
-/
@[inline]
def reduceUInt64Raw (x : UInt64) : UInt64 :=
  if x < modulus then x else x - modulus

/-- Rare path of the 128-bit fold, taken when the low word borrows against the top limb
(probability about `2^-32` on random inputs). Kept out of line so the common path
compiles to a predicted branch instead of a select on the critical path. -/
@[noinline]
def foldUInt128Borrow (lo hi_hi hi_lo : UInt64) : UInt64 :=
  let t0 := lo - hi_hi - negModulus
  let t1 := hi_lo * negModulus
  let t2 := t0 + t1
  if t2 < t0 then t2 + negModulus else t2

/-- Fold a 128-bit value `lo + hi * 2^64` into one congruent word using
`2^64 ≡ 2^32 - 1`. The result is not canonicalized.

The middle term `hi_lo * (2^32 - 1)` is formed as `(hi <<< 32) - hi_lo`, two one-cycle
operations rather than a three-cycle multiply. -/
@[inline]
def foldUInt128Lazy (lo hi : UInt64) : UInt64 :=
  let hi_hi := hi >>> 32
  let hi_lo := hi &&& negModulus
  if lo < hi_hi then foldUInt128Borrow lo hi_hi hi_lo
  else
    let t0 := lo - hi_hi
    let t1 := (hi <<< 32) - hi_lo
    let t2 := t0 + t1
    if t2 < t0 then t2 + negModulus else t2

/-- Raw reduction of a 128-bit integer represented by low and high words modulo Goldilocks. -/
@[inline]
def reduceUInt128Raw (lo hi : UInt64) : UInt64 :=
  reduceUInt64Raw (foldUInt128Lazy lo hi)

/-- Product of two arbitrary words as one congruent, not necessarily canonical, word. -/
@[inline]
def mulLazy (x y : UInt64) : UInt64 :=
  let product := wideMul x y
  foldUInt128Lazy product.1 product.2

/-- Raw reduction of a 64-by-64 product modulo Goldilocks. -/
@[inline]
def reduceMulRaw (x y : UInt64) : UInt64 :=
  reduceUInt64Raw (mulLazy x y)

/-- Raw modular addition of canonical words.

Computed as `x - (p - y)`: the subtraction borrows exactly when `x + y < p`, so one
borrow-selected correction yields the canonical sum, with no separate compare against `p`. -/
@[inline]
def addRaw (x y : UInt64) : UInt64 :=
  let u := modulus - y
  let s := x - u
  if x < u then s - negModulus else s

/-- Raw modular negation in canonical form. -/
@[inline]
def negRaw (x : UInt64) : UInt64 :=
  if x = 0 then 0 else modulus - x

/-- Raw modular subtraction in canonical form. -/
@[inline]
def subRaw (x y : UInt64) : UInt64 :=
  if y ≤ x then x - y else x - y - negModulus

/-! ## Lazy exponentiation -/


/-- Square-and-multiply on unreduced words: `powLazy acc x n` computes `acc * x^n`. -/
def powLazy (acc x : UInt64) (n : Nat) : UInt64 :=
  if h : n = 0 then acc
  else
    let acc := if n % 2 = 1 then mulLazy acc x else acc
    powLazy acc (mulLazy x x) (n / 2)
termination_by n
decreasing_by omega

/-- `x^(2^n)` on unreduced words. -/
def squareNLazy (x : UInt64) : Nat → UInt64
  | 0 => x
  | n + 1 => squareNLazy (mulLazy x x) n

/-- Fermat chain for `x^(p - 2)` on unreduced words; the caller canonicalizes once.

`p - 2 = 0xFFFFFFFEFFFFFFFF`: build `x^(2^31 - 1)`, derive `x^(2^32 - 2)` and
`x^(2^32 - 1)`, then combine them as `(2^32 - 2) * 2^32 + (2^32 - 1)`. -/
def invLazy (x : UInt64) : UInt64 :=
  let t2 := mulLazy (mulLazy x x) x
  let t4 := mulLazy (squareNLazy t2 2) t2
  let t8 := mulLazy (squareNLazy t4 4) t4
  let t16 := mulLazy (squareNLazy t8 8) t8
  let t31 :=
    mulLazy (squareNLazy t16 15)
      (mulLazy (squareNLazy t8 7)
        (mulLazy (squareNLazy t4 3)
          (mulLazy (mulLazy t2 t2) x)))
  let t32m2 := mulLazy t31 t31
  let t32m1 := mulLazy t32m2 x
  mulLazy (squareNLazy t32m2 32) t32m1

end Goldilocks.Fast
