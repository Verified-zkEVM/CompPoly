/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos, Gregor Mitscha-Baude
-/
module

/-!
# Four-limb Montgomery arithmetic: runtime definitions (zero-import)

The runtime definitions of the four-limb Montgomery arithmetic over 64-bit limbs; all
correctness statements live in `CompPoly.Fields.Montgomery.Native64x4`, which imports this
one.  Products widen through `mulHi` (four 32-bit partial products) and every word helper
returns a pair the caller destructures, so nothing is boxed.

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

/-- Add-with-carry: the low word and the carry-out of `x + y + c`, for `c ≤ 1`.
The two overflow flags cannot both be set; OR exposes the one-bit carry to code generation. -/
@[inline] def adc (x y c : UInt64) : UInt64 × UInt64 :=
  let s := x + y
  let s' := s + c
  (s', (if s < x then 1 else 0) ||| (if s' < s then 1 else 0))

/-- Subtract-with-borrow: the low word and the borrow-out of `x - y - b`, for `b ≤ 1`.
The two borrow flags cannot both be set; OR exposes the one-bit borrow to code generation. -/
@[inline] def sbb (x y b : UInt64) : UInt64 × UInt64 :=
  let d := x - y
  (d - b, (if x < y then 1 else 0) ||| (if d < b then 1 else 0))

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

Chains return flat words and a `Limbs4` is built only inside a branch: one bound before the
branch is allocated whether or not that side runs. -/

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
of the modulus. For canonical inputs and a modulus below `2 ^ 255`, the top carry is
impossible, so the spare-bit branch omits its test. -/
@[inline] def add (q a b : Limbs4) : Limbs4 :=
  let (s0, s1, s2, s3, c) := addLimbs a b
  let (d0, d1, d2, d3, bo) := subLimbs ⟨s0, s1, s2, s3⟩ q
  if q.l3 < 0x8000000000000000 then
    if bo == 0 then ⟨d0, d1, d2, d3⟩ else ⟨s0, s1, s2, s3⟩
  else
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

/-- The multiply half of a CIOS round, `t + a * bi`, keeping the carry out of the head limb. -/
@[inline] def mulAccum (a : Limbs4) (bi : UInt64) (t : State5) : State6 :=
  let (s0, k) := mac t.t0 a.l0 bi 0
  let (s1, k) := mac t.t1 a.l1 bi k
  let (s2, k) := mac t.t2 a.l2 bi k
  let (s3, k) := mac t.t3 a.l3 bi k
  let (s4, s5) := adc t.t4 k 0
  ⟨s0, s1, s2, s3, s4, s5⟩

/-- The reduce half of a CIOS round: add `montM s.t0 negInv * q`, which cancels the low limb,
and drop that limb; `negInv` must be `-q⁻¹ mod 2 ^ 64`. -/
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

/-- Four CIOS Montgomery rounds, retaining the carry limb and omitting normalization. -/
@[inline] def mulUnreduced (q : Limbs4) (negInv : UInt64) (a b : Limbs4) : State5 :=
  let t := mulRound q negInv a b.l0 State5.zero
  let t := mulRound q negInv a b.l1 t
  let t := mulRound q negInv a b.l2 t
  let t := mulRound q negInv a b.l3 t
  t

/-- CIOS Montgomery multiplication followed by one conditional subtraction. -/
@[inline] def mul (q : Limbs4) (negInv : UInt64) (a b : Limbs4) : Limbs4 :=
  condSubWide q (mulUnreduced q negInv a b)

/-- Accumulate a precomputed low/high product, preserving the full carry word. -/
@[inline] def macWords (t lo hi c : UInt64) : UInt64 × UInt64 :=
  let s := t + lo
  let s' := s + c
  (s', hi + (if s < t then 1 else 0) + (if s' < s then 1 else 0))

/-- Montgomery square sharing the ten distinct limb products across CIOS rounds. -/
@[inline] def squareCached (q : Limbs4) (negInv : UInt64) (a : Limbs4) : Limbs4 :=
  let lo00 := a.l0 * a.l0
  let hi00 := mulHi a.l0 a.l0
  let lo01 := a.l0 * a.l1
  let hi01 := mulHi a.l0 a.l1
  let lo02 := a.l0 * a.l2
  let hi02 := mulHi a.l0 a.l2
  let lo03 := a.l0 * a.l3
  let hi03 := mulHi a.l0 a.l3
  let lo11 := a.l1 * a.l1
  let hi11 := mulHi a.l1 a.l1
  let lo12 := a.l1 * a.l2
  let hi12 := mulHi a.l1 a.l2
  let lo13 := a.l1 * a.l3
  let hi13 := mulHi a.l1 a.l3
  let lo22 := a.l2 * a.l2
  let hi22 := mulHi a.l2 a.l2
  let lo23 := a.l2 * a.l3
  let hi23 := mulHi a.l2 a.l3
  let lo33 := a.l3 * a.l3
  let hi33 := mulHi a.l3 a.l3
  let t := State5.zero
  let (s0, c) := macWords t.t0 lo00 hi00 0
  let (s1, c) := macWords t.t1 lo01 hi01 c
  let (s2, c) := macWords t.t2 lo02 hi02 c
  let (s3, c) := macWords t.t3 lo03 hi03 c
  let (s4, s5) := adc t.t4 c 0
  let t := mulReduce q negInv ⟨s0, s1, s2, s3, s4, s5⟩
  let (s0, c) := macWords t.t0 lo01 hi01 0
  let (s1, c) := macWords t.t1 lo11 hi11 c
  let (s2, c) := macWords t.t2 lo12 hi12 c
  let (s3, c) := macWords t.t3 lo13 hi13 c
  let (s4, s5) := adc t.t4 c 0
  let t := mulReduce q negInv ⟨s0, s1, s2, s3, s4, s5⟩
  let (s0, c) := macWords t.t0 lo02 hi02 0
  let (s1, c) := macWords t.t1 lo12 hi12 c
  let (s2, c) := macWords t.t2 lo22 hi22 c
  let (s3, c) := macWords t.t3 lo23 hi23 c
  let (s4, s5) := adc t.t4 c 0
  let t := mulReduce q negInv ⟨s0, s1, s2, s3, s4, s5⟩
  let (s0, c) := macWords t.t0 lo03 hi03 0
  let (s1, c) := macWords t.t1 lo13 hi13 c
  let (s2, c) := macWords t.t2 lo23 hi23 c
  let (s3, c) := macWords t.t3 lo33 hi33 c
  let (s4, s5) := adc t.t4 c 0
  let t := mulReduce q negInv ⟨s0, s1, s2, s3, s4, s5⟩
  condSubWide q t

/-- Montgomery squaring. -/
@[inline] def square (q : Limbs4) (negInv : UInt64) (a : Limbs4) : Limbs4 :=
  mul q negInv a a

/-! ## Scalar inputs for inlined hot loops -/

namespace Scalar

/-- Scalar-limb add. Inline the call and immediately destructure the result to eliminate
intermediate limb objects. Inputs and output use Montgomery residues with the same
preconditions as `Native64x4.add`. -/
@[inline] def add (q0 q1 q2 q3 : UInt64)
    (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let r := Native64x4.add ⟨q0, q1, q2, q3⟩ ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩
  (r.l0, r.l1, r.l2, r.l3)

/-- Scalar-limb sub. Inline the call and immediately destructure the result to eliminate
intermediate limb objects. Inputs and output use Montgomery residues with the same
preconditions as `Native64x4.sub`. -/
@[inline] def sub (q0 q1 q2 q3 : UInt64)
    (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let r := Native64x4.sub ⟨q0, q1, q2, q3⟩ ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩
  (r.l0, r.l1, r.l2, r.l3)

/-- Scalar-limb mul. Inline the call and immediately destructure the result to eliminate
intermediate limb objects. Inputs and output use Montgomery residues with the same
preconditions as `Native64x4.mul`. -/
@[inline] def mul (q0 q1 q2 q3 : UInt64) (negInv : UInt64)
    (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let r := Native64x4.mul ⟨q0, q1, q2, q3⟩ negInv ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩
  (r.l0, r.l1, r.l2, r.l3)

/-- Scalar-limb square. Inline the call and immediately destructure the result to eliminate
intermediate limb objects. Inputs and output use Montgomery residues with the same
preconditions as `Native64x4.square`. -/
@[inline] def square (q0 q1 q2 q3 : UInt64) (negInv : UInt64)
    (a0 a1 a2 a3 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let r := Native64x4.square ⟨q0, q1, q2, q3⟩ negInv ⟨a0, a1, a2, a3⟩
  (r.l0, r.l1, r.l2, r.l3)

end Scalar

end Native64x4
end Montgomery
