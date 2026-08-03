/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
import CompPoly.Fields.Montgomery.Native256.Limb
import CompPoly.Fields.Montgomery.Native256.UInt128L

/-!
# 256-bit limb word (`UInt256L`)

The four-`UInt64`-limb word of the proof-free binary-GCD engine: subtract, comparison,
`mulLimb`, and the scan multiply `mulSmall`. `toNat` is the specification hook for the
`decide`d constant guards of `Mont256Field`.
-/

namespace Montgomery.Native256

/-- A 256-bit value as four little-endian 64-bit limbs. -/
structure UInt256L where
  /-- Limb of weight `2 ^ 0`. -/
  l0 : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  l1 : UInt64
  /-- Limb of weight `2 ^ 128`. -/
  l2 : UInt64
  /-- Limb of weight `2 ^ 192`. -/
  l3 : UInt64
deriving DecidableEq

/-- The natural number represented by the limbs. -/
def UInt256L.toNat (x : UInt256L) : Nat :=
  x.l0.toNat + (x.l1.toNat <<< 64) + (x.l2.toNat <<< 128) + (x.l3.toNat <<< 192)

/-- Four-limb ripple-carry addition with carry-in, returning the low 256 bits together with
the final carry-out word. -/
@[inline] def UInt256L.addCarryOut (a b : UInt256L) (cin : UInt64) : UInt256L × UInt64 :=
  let (l0, c0) := addc a.l0 b.l0 cin
  let (l1, c1) := addc a.l1 b.l1 c0
  let (l2, c2) := addc a.l2 b.l2 c1
  let (l3, c3) := addc a.l3 b.l3 c2
  (⟨l0, l1, l2, l3⟩, c3)

/-- One limb of subtract-with-borrow: `(dᵢ, borrow')`, single-bit `borrow'` given single-bit
`borrow`. -/
@[inline] def subb (a b borrow : UInt64) : UInt64 × UInt64 :=
  let s1 := a - b
  let b1 := if a < b then 1 else 0
  let s2 := s1 - borrow
  let b2 := if s1 < borrow then 1 else 0
  (s2, b1 + b2)

/-- Wrapping 256-bit subtraction by ripple borrow. -/
@[inline] def UInt256L.sub (a b : UInt256L) : UInt256L :=
  let (l0, brw0) := subb a.l0 b.l0 0
  let (l1, brw1) := subb a.l1 b.l1 brw0
  let (l2, brw2) := subb a.l2 b.l2 brw1
  let (l3, _) := subb a.l3 b.l3 brw2
  ⟨l0, l1, l2, l3⟩

instance : Sub UInt256L := ⟨UInt256L.sub⟩

/-- Full 64×64→128 product as `UInt128L`. -/
@[inline] def mulLimb (a b : UInt64) : UInt128L :=
  let mask : UInt64 := 0xFFFFFFFF
  let aL := a &&& mask
  let aH := a >>> 32
  let bL := b &&& mask
  let bH := b >>> 32
  let ll := aL * bL
  let lh := aL * bH
  let hl := aH * bL
  let hh := aH * bH
  let cross := (ll >>> 32) + (lh &&& mask) + (hl &&& mask)
  let lo := (ll &&& mask) ||| (cross <<< 32)
  let hi := hh + (lh >>> 32) + (hl >>> 32) + (cross >>> 32)
  ⟨lo, hi⟩

/-- `lhs · rhs` with `lhs < 2^256`, `rhs < 2^64`. Returns the lowest limb and the
remaining four limbs of the 5-limb product. -/
@[inline] def mulSmall (lhs : UInt256L) (rhs : UInt64) : UInt64 × UInt256L :=
  let p0 : UInt128L := mulLimb lhs.l0 rhs
  let c0 : UInt128L := ⟨p0.hi, 0⟩
  let p1 : UInt128L := c0 + (mulLimb lhs.l1 rhs)
  let c1 : UInt128L := ⟨p1.hi, 0⟩
  let p2 : UInt128L := c1 + (mulLimb lhs.l2 rhs)
  let c2 : UInt128L := ⟨p2.hi, 0⟩
  let p3 : UInt128L := c2 + (mulLimb lhs.l3 rhs)
  (p0.lo, ⟨p1.lo, p2.lo, p3.lo, p3.hi⟩)

/-- Limb-lexicographic comparison from the top limb, which agrees with the numeric order. -/
@[inline] def UInt256L.cmp (a b : UInt256L) : Ordering :=
  if a.l3 ≠ b.l3 then compare a.l3 b.l3
  else if a.l2 ≠ b.l2 then compare a.l2 b.l2
  else if a.l1 ≠ b.l1 then compare a.l1 b.l1
  else compare a.l0 b.l0

instance : Ord UInt256L where
  compare := UInt256L.cmp

instance : LT UInt256L := ⟨fun a b => compare a b = Ordering.lt⟩

instance (a b : UInt256L) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b = Ordering.lt))

end Montgomery.Native256
