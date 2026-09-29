/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

/-!
# Four-limb Montgomery arithmetic: runtime definitions (zero-import)

The runtime definitions of the four-limb Montgomery arithmetic over 64-bit limbs.  All
correctness statements about them live in `CompPoly.Fields.Montgomery.Native64x4`, which
imports this one.  Products are widened with `mulHi`, four 32-bit partial products; every
word helper returns its low word and carry as a pair that the caller destructures, so the
compiler keeps all accumulators in registers and nothing is boxed.

This module deliberately has **zero imports**, for `precompileModules` consumers.
-/

@[expose] public section

namespace Montgomery
namespace Native64x4

/-! ## Word helpers -/

/-- High word of the 64-bit product `a * b`, from four 32-bit partial products. -/
@[inline] def mulHi (a b : UInt64) : UInt64 :=
  let mask : UInt64 := 0xffffffff
  let a0 := a &&& mask
  let a1 := a >>> 32
  let b0 := b &&& mask
  let b1 := b >>> 32
  let w0 := a0 * b0
  let t := a1 * b0 + (w0 >>> 32)
  let w1 := (t &&& mask) + a0 * b1
  a1 * b1 + (t >>> 32) + (w1 >>> 32)

/-- Add-with-carry: the low word and the carry-out of `x + y + c`, for `c ≤ 1`. -/
@[inline] def adc (x y c : UInt64) : UInt64 × UInt64 :=
  let s := x + y
  let s' := s + c
  (s', (if s < x then 1 else 0) + (if s' < s then 1 else 0))

/-- Subtract-with-borrow: the low word and the borrow-out of `x - y - b`, for `b ≤ 1`. -/
@[inline] def sbb (x y b : UInt64) : UInt64 × UInt64 :=
  let d := x - y
  (d - b, (if x < y then 1 else 0) + (if d < b then 1 else 0))

/-- Multiply-accumulate: the low and high words of `t + a * b + c`. -/
@[inline] def mac (t a b c : UInt64) : UInt64 × UInt64 :=
  let s := t + a * b
  let s' := s + c
  (s', mulHi a b + (if s < t then 1 else 0) + (if s' < s then 1 else 0))

/-- The Montgomery multiplier of a limb: `(s * negInv) mod 2 ^ 64`. -/
@[inline] def montM (s negInv : UInt64) : UInt64 := s * negInv

/-! ## Four-limb values -/

/-- A 256-bit value as four little-endian 64-bit limbs. -/
structure Limbs4 where
  /-- Limb of weight `2 ^ 0`. -/
  l0 : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  l1 : UInt64
  /-- Limb of weight `2 ^ 128`. -/
  l2 : UInt64
  /-- Limb of weight `2 ^ 192`. -/
  l3 : UInt64
deriving DecidableEq, Repr, Inhabited

namespace Limbs4

/-- The zero value. -/
def zero : Limbs4 := ⟨0, 0, 0, 0⟩

/-- The value one. -/
def one : Limbs4 := ⟨1, 0, 0, 0⟩

/-- Split a natural number into four 64-bit limbs, discarding bits above `2 ^ 256`. -/
@[inline] def ofNat (n : Nat) : Limbs4 :=
  ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64), UInt64.ofNat (n >>> 128), UInt64.ofNat (n >>> 192)⟩

/-- The natural number represented by the limbs: `∑ lᵢ * 2 ^ (64 * i)`. -/
def toNat (x : Limbs4) : Nat :=
  x.l0.toNat + 2 ^ 64 * x.l1.toNat + 2 ^ 128 * x.l2.toNat + 2 ^ 192 * x.l3.toNat

end Limbs4

/-! ## Limbwise addition and subtraction

The limb chains return their words flat, and a `Limbs4` is only built at the end of a branch:
a value bound before a branch and returned by one side is allocated whether or not that side
runs. -/

/-- Limbwise add-with-carry: the four sum limbs and the carry out of the top limb. -/
@[inline] def addLimbs (a b : Limbs4) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (s0, c) := adc a.l0 b.l0 0
  let (s1, c) := adc a.l1 b.l1 c
  let (s2, c) := adc a.l2 b.l2 c
  let (s3, c) := adc a.l3 b.l3 c
  (s0, s1, s2, s3, c)

/-- Limbwise subtract-with-borrow: the four difference limbs and the borrow out of the top
limb. -/
@[inline] def subLimbs (a b : Limbs4) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (d0, bo) := sbb a.l0 b.l0 0
  let (d1, bo) := sbb a.l1 b.l1 bo
  let (d2, bo) := sbb a.l2 b.l2 bo
  let (d3, bo) := sbb a.l3 b.l3 bo
  (d0, d1, d2, d3, bo)

/-! ## Conditional subtraction and field operations -/

/-- Subtract the modulus once if the value is at least the modulus. -/
@[inline] def condSub (q t : Limbs4) : Limbs4 :=
  let (d0, d1, d2, d3, bo) := subLimbs t q
  if bo == 0 then ⟨d0, d1, d2, d3⟩ else t

/-- Modular addition; a carry out of the top limb forces the (wrapping, exact) subtraction
of the modulus, and never happens for a modulus below `2 ^ 255`. -/
@[inline] def add (q a b : Limbs4) : Limbs4 :=
  let (s0, s1, s2, s3, c) := addLimbs a b
  let (d0, d1, d2, d3, bo) := subLimbs ⟨s0, s1, s2, s3⟩ q
  if c != 0 then ⟨d0, d1, d2, d3⟩ else if bo == 0 then ⟨d0, d1, d2, d3⟩ else ⟨s0, s1, s2, s3⟩

/-- Modular subtraction: on a borrow, the modulus is added back. -/
@[inline] def sub (q a b : Limbs4) : Limbs4 :=
  let (d0, d1, d2, d3, bo) := subLimbs a b
  if bo == 0 then ⟨d0, d1, d2, d3⟩
  else
    let (r0, r1, r2, r3, _) := addLimbs ⟨d0, d1, d2, d3⟩ q
    ⟨r0, r1, r2, r3⟩

/-- Modular negation. -/
@[inline] def neg (q a : Limbs4) : Limbs4 := sub q Limbs4.zero a

/-! ## CIOS multiplication -/

/-- The CIOS accumulator between rounds: four limbs plus one head limb. -/
structure State5 where
  /-- Limb of weight `2 ^ 0`. -/
  t0 : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  t1 : UInt64
  /-- Limb of weight `2 ^ 128`. -/
  t2 : UInt64
  /-- Limb of weight `2 ^ 192`. -/
  t3 : UInt64
  /-- Head limb of weight `2 ^ 256`. -/
  t4 : UInt64
deriving DecidableEq, Repr, Inhabited

/-- The CIOS accumulator after the multiply half of a round: five limbs plus a carry limb. -/
structure State6 where
  /-- Limb of weight `2 ^ 0`. -/
  t0 : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  t1 : UInt64
  /-- Limb of weight `2 ^ 128`. -/
  t2 : UInt64
  /-- Limb of weight `2 ^ 192`. -/
  t3 : UInt64
  /-- Limb of weight `2 ^ 256`. -/
  t4 : UInt64
  /-- Carry limb of weight `2 ^ 320`. -/
  t5 : UInt64
deriving DecidableEq, Repr, Inhabited

namespace State5

/-- The zero accumulator. -/
@[inline] def zero : State5 := ⟨0, 0, 0, 0, 0⟩

/-- The four low limbs of the accumulator. -/
@[inline] def toLimbs4 (t : State5) : Limbs4 := ⟨t.t0, t.t1, t.t2, t.t3⟩

/-- The natural number represented by the accumulator. -/
def toNat (t : State5) : Nat := t.toLimbs4.toNat + 2 ^ 256 * t.t4.toNat

end State5

namespace State6

/-- The natural number represented by the accumulator. -/
def toNat (t : State6) : Nat :=
  t.t0.toNat + 2 ^ 64 * t.t1.toNat + 2 ^ 128 * t.t2.toNat + 2 ^ 192 * t.t3.toNat +
    2 ^ 256 * t.t4.toNat + 2 ^ 320 * t.t5.toNat

end State6

/-- The multiply half of a CIOS round: accumulate `a * bi` into the accumulator.  The carry
out of the head limb is kept in the carry limb, so no information is lost. -/
@[inline] def mulAccum (a : Limbs4) (bi : UInt64) (t : State5) : State6 :=
  let (s0, k) := mac t.t0 a.l0 bi 0
  let (s1, k) := mac t.t1 a.l1 bi k
  let (s2, k) := mac t.t2 a.l2 bi k
  let (s3, k) := mac t.t3 a.l3 bi k
  let (s4, s5) := adc t.t4 k 0
  ⟨s0, s1, s2, s3, s4, s5⟩

/-- The reduce half of a CIOS round: add the multiple `montM s.t0 negInv` of the modulus that
cancels the low limb, then drop that limb.  `negInv` has to be `-q⁻¹ mod 2 ^ 64`. -/
@[inline] def mulReduce (q : Limbs4) (negInv : UInt64) (s : State6) : State5 :=
  let m := montM s.t0 negInv
  let (_, u) := mac s.t0 m q.l0 0
  let (t0, u) := mac s.t1 m q.l1 u
  let (t1, u) := mac s.t2 m q.l2 u
  let (t2, u) := mac s.t3 m q.l3 u
  let (t3, u) := adc s.t4 u 0
  ⟨t0, t1, t2, t3, s.t5 + u⟩

/-- One CIOS outer round: accumulate `a * bi` into the accumulator, then reduce away one
limb. -/
@[inline] def mulRound (q : Limbs4) (negInv : UInt64) (a : Limbs4) (bi : UInt64)
    (t : State5) : State5 :=
  mulReduce q negInv (mulAccum a bi t)

/-- `condSub` for an accumulator below `2 * q`; a set head limb forces the (wrapping, exact)
subtraction of the modulus, and never happens for a modulus below `2 ^ 255`. -/
@[inline] def condSubWide (q : Limbs4) (t : State5) : Limbs4 :=
  let (d0, d1, d2, d3, bo) := subLimbs t.toLimbs4 q
  if t.t4 != 0 then ⟨d0, d1, d2, d3⟩ else if bo == 0 then ⟨d0, d1, d2, d3⟩
  else ⟨t.t0, t.t1, t.t2, t.t3⟩

/-- CIOS Montgomery multiplication: four rounds followed by one conditional subtraction. -/
@[inline] def mul (q : Limbs4) (negInv : UInt64) (a b : Limbs4) : Limbs4 :=
  let t := mulRound q negInv a b.l0 State5.zero
  let t := mulRound q negInv a b.l1 t
  let t := mulRound q negInv a b.l2 t
  let t := mulRound q negInv a b.l3 t
  condSubWide q t

/-- Montgomery squaring. -/
@[inline] def square (q : Limbs4) (negInv : UInt64) (a : Limbs4) : Limbs4 :=
  mul q negInv a a

end Native64x4
end Montgomery
