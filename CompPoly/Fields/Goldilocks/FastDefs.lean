/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

/-!
# Fast Goldilocks: runtime definitions (zero-import)

Runtime word kernels of the native Goldilocks field, proved correct in
`CompPoly.Fields.Goldilocks.FastReduction`. This module has zero imports so that
`precompileModules` lanes, which compile the whole import closure, can take it without Mathlib.
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

Kernels take and return canonical words below the modulus; the `Lazy` ones take and
return any congruent word, so a chain canonicalizes once at the end. -/


/-- Full 64-by-64 product as `(lo, hi)` words from 32-bit limbs, in the shape clang fuses
into one widening multiply. -/
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

/-- Canonicalize a word by one conditional subtraction, since every `UInt64` is below `2 * p`. -/
@[inline]
def reduceUInt64Raw (x : UInt64) : UInt64 :=
  if x < modulus then x else x - modulus

/-- Borrow arm of the 128-bit fold, out of line so the common path takes a predicted branch. -/
@[noinline]
def foldUInt128Borrow (lo hiHi hiLo : UInt64) : UInt64 :=
  let t0 := lo - hiHi - negModulus
  let t1 := hiLo * negModulus
  let t2 := t0 + t1
  if t2 < t0 then t2 + negModulus else t2

/-- Fold `lo + hi * 2^64` into one congruent, not necessarily canonical, word using
`2^64 ≡ 2^32 - 1`; the middle term is `(hi <<< 32) - hiLo` rather than a multiply. -/
@[inline]
def foldUInt128Lazy (lo hi : UInt64) : UInt64 :=
  let hiHi := hi >>> 32
  let hiLo := hi &&& negModulus
  if lo < hiHi then foldUInt128Borrow lo hiHi hiLo
  else
    let t0 := lo - hiHi
    let t1 := (hi <<< 32) - hiLo
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

/-- Canonical sum as `x - (p - y)`, which borrows exactly when `x + y < p`. -/
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

/-- Fermat chain for `x^(p - 2)` on unreduced words, with
`p - 2 = (2^32 - 2) * 2^32 + (2^32 - 1)`. -/
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
