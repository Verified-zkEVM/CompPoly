/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

/-!
# Fast binary tower: runtime definitions (zero-import)

The runtime definitions of the packed binary tower arithmetic, split out of
`CompPoly.Fields.Binary.Tower.Fast` verbatim. All correctness statements about them
live in that sibling module, which imports this one.

This module deliberately has **zero imports**: downstream consumers put it into
`precompileModules` native-compilation lanes, and `precompileModules` compiles the
entire import closure, so the runtime definitions must not pull in mathlib.
-/

@[expose] public section

namespace ConcreteBinaryTower.Fast

/-! ## Raw word operations

Names carry the operand bit width (`mul8` multiplies level-3 values in the low 8 bits);
`mulByZk` multiplies by the tower generator `Z k`. A multiplication rung recombines the
Karatsuba half-products `p0 = a₀b₀`, `p2 = a₁b₁`, `p1 = (a₀+a₁)(b₀+b₁)` as
`lo = p0 + p2`, `hi = p1 + lo + Z·p2`; squaring drops the cross term; inversion is the
quadratic descent of `concrete_inv`. Inputs are assumed in range. -/

/-- GF(4) multiplication (level 1). `Z 0 = 1` collapses the generic recombination
`hi = p1 + lo + Z·p2` to `hi = p1 + p0`, saving a xor on the ladder's hottest rung. -/
@[inline] def mul2 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 1
  let a1 := a >>> 1
  let b0 := b &&& 1
  let b1 := b >>> 1
  let p0 := a0 &&& b0
  let p2 := a1 &&& b1
  let p1 := (a0 ^^^ a1) &&& (b0 ^^^ b1)
  ((p1 ^^^ p0) <<< 1) ||| (p0 ^^^ p2)

/-- Multiplication by the level-1 generator `Z 1`. -/
@[inline] def mulByZ1 (v : UInt64) : UInt64 :=
  let v0 := v &&& 1
  let v1 := v >>> 1
  ((v0 ^^^ v1) <<< 1) ||| v1

/-- GF(4) squaring. -/
@[inline] def sq2 (v : UInt64) : UInt64 :=
  let v0 := v &&& 1
  let v1 := v >>> 1
  (v1 <<< 1) ||| (v0 ^^^ v1)

/-- GF(4) inversion (`0 ↦ 0`), in the shape of the recursive twin so `inv2_eq_rec`
is `rfl`. -/
@[inline] def inv2 (v : UInt64) : UInt64 :=
  let v0 := v &&& 1
  let v1 := v >>> 1
  let next := v0 ^^^ v1
  let delta := (v0 &&& next) ^^^ v1
  ((delta &&& v1) <<< 1) ||| (delta &&& next)

/-- GF(2^4) multiplication (level 2). -/
@[inline] def mul4 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0x3
  let a1 := a >>> 2
  let b0 := b &&& 0x3
  let b1 := b >>> 2
  let p0 := mul2 a0 b0
  let p2 := mul2 a1 b1
  let p1 := mul2 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ1 p2) <<< 2) ||| lo

/-- Multiplication by the level-2 generator `Z 2`. -/
@[inline] def mulByZ2 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0x3
  let v1 := v >>> 2
  ((v0 ^^^ mulByZ1 v1) <<< 2) ||| v1

/-- GF(2^4) squaring. -/
@[inline] def sq4 (v : UInt64) : UInt64 :=
  let s0 := sq2 (v &&& 0x3)
  let s1 := sq2 (v >>> 2)
  ((mulByZ1 s1) <<< 2) ||| (s0 ^^^ s1)

/-- GF(2^4) inversion (`0 ↦ 0`). -/
@[inline] def inv4 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0x3
  let v1 := v >>> 2
  let next := v0 ^^^ mulByZ1 v1
  let delta := mul2 v0 next ^^^ sq2 v1
  let d := inv2 delta
  ((mul2 d v1) <<< 2) ||| (mul2 d next)

/-- GF(2^8) multiplication (level 3). -/
@[inline] def mul8 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xF
  let a1 := a >>> 4
  let b0 := b &&& 0xF
  let b1 := b >>> 4
  let p0 := mul4 a0 b0
  let p2 := mul4 a1 b1
  let p1 := mul4 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ2 p2) <<< 4) ||| lo

/-- Multiplication by the level-3 generator `Z 3`. -/
@[inline] def mulByZ3 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xF
  let v1 := v >>> 4
  ((v0 ^^^ mulByZ2 v1) <<< 4) ||| v1

/-- GF(2^8) squaring. -/
@[inline] def sq8 (v : UInt64) : UInt64 :=
  let s0 := sq4 (v &&& 0xF)
  let s1 := sq4 (v >>> 4)
  ((mulByZ2 s1) <<< 4) ||| (s0 ^^^ s1)

/-- GF(2^8) inversion (`0 ↦ 0`). -/
@[inline] def inv8 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xF
  let v1 := v >>> 4
  let next := v0 ^^^ mulByZ2 v1
  let delta := mul4 v0 next ^^^ sq4 v1
  let d := inv4 delta
  ((mul4 d v1) <<< 4) ||| (mul4 d next)

/-- GF(2^16) multiplication (level 4). -/
@[inline] def mul16 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFF
  let a1 := a >>> 8
  let b0 := b &&& 0xFF
  let b1 := b >>> 8
  let p0 := mul8 a0 b0
  let p2 := mul8 a1 b1
  let p1 := mul8 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ3 p2) <<< 8) ||| lo

/-- Multiplication by the level-4 generator `Z 4`. -/
@[inline] def mulByZ4 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFF
  let v1 := v >>> 8
  ((v0 ^^^ mulByZ3 v1) <<< 8) ||| v1

/-- GF(2^16) squaring. -/
@[inline] def sq16 (v : UInt64) : UInt64 :=
  let s0 := sq8 (v &&& 0xFF)
  let s1 := sq8 (v >>> 8)
  ((mulByZ3 s1) <<< 8) ||| (s0 ^^^ s1)

/-- GF(2^16) inversion (`0 ↦ 0`). -/
@[inline] def inv16 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFF
  let v1 := v >>> 8
  let next := v0 ^^^ mulByZ3 v1
  let delta := mul8 v0 next ^^^ sq8 v1
  let d := inv8 delta
  ((mul8 d v1) <<< 8) ||| (mul8 d next)

/-- GF(2^32) multiplication (level 5). Outlined: inlining the whole ladder above this
width exceeds the compiler's recursion depth. -/
def mul32 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFFFF
  let a1 := a >>> 16
  let b0 := b &&& 0xFFFF
  let b1 := b >>> 16
  let p0 := mul16 a0 b0
  let p2 := mul16 a1 b1
  let p1 := mul16 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ4 p2) <<< 16) ||| lo

/-- Multiplication by the level-5 generator `Z 5`. -/
@[inline] def mulByZ5 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFF
  let v1 := v >>> 16
  ((v0 ^^^ mulByZ4 v1) <<< 16) ||| v1

/-- GF(2^32) squaring. -/
@[inline] def sq32 (v : UInt64) : UInt64 :=
  let s0 := sq16 (v &&& 0xFFFF)
  let s1 := sq16 (v >>> 16)
  ((mulByZ4 s1) <<< 16) ||| (s0 ^^^ s1)

/-- GF(2^32) inversion (`0 ↦ 0`). -/
@[inline] def inv32 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFF
  let v1 := v >>> 16
  let next := v0 ^^^ mulByZ4 v1
  let delta := mul16 v0 next ^^^ sq16 v1
  let d := inv16 delta
  ((mul16 d v1) <<< 16) ||| (mul16 d next)

/-- GF(2^64) multiplication (level 6). Outlined, see `mul32`. -/
def mul64 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFFFFFFFF
  let a1 := a >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let p0 := mul32 a0 b0
  let p2 := mul32 a1 b1
  let p1 := mul32 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ5 p2) <<< 32) ||| lo

/-- Multiplication by the level-6 generator `Z 6`. -/
@[inline] def mulByZ6 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  ((v0 ^^^ mulByZ5 v1) <<< 32) ||| v1

/-- GF(2^64) squaring. -/
@[inline] def sq64 (v : UInt64) : UInt64 :=
  let s0 := sq32 (v &&& 0xFFFFFFFF)
  let s1 := sq32 (v >>> 32)
  ((mulByZ5 s1) <<< 32) ||| (s0 ^^^ s1)

/-- GF(2^64) inversion (`0 ↦ 0`). -/
@[inline] def inv64 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  let next := v0 ^^^ mulByZ5 v1
  let delta := mul32 v0 next ^^^ sq32 v1
  let d := inv32 delta
  ((mul32 d v1) <<< 32) ||| (mul32 d next)

/-! ## GF(2^8) tables and table-based rungs

Level-3 operations as byte-table lookups, tables generated from the ladder by
`Array.ofFn`; the wider `*T` rungs rebuild the ladder on the table base. -/

/-- `mul8` product table. -/
def mul8Table : ByteArray :=
  ⟨Array.ofFn (n := 65536) fun i =>
    (mul8 (UInt64.ofNat (i / 256)) (UInt64.ofNat (i % 256))).toUInt8⟩

/-- `mulByZ3` table. -/
def mulByZ3Table : ByteArray :=
  ⟨Array.ofFn (n := 256) fun i => (mulByZ3 (UInt64.ofNat i)).toUInt8⟩

/-- `sq8` table. -/
def sq8Table : ByteArray :=
  ⟨Array.ofFn (n := 256) fun i => (sq8 (UInt64.ofNat i)).toUInt8⟩

/-- `inv8` table (`0 ↦ 0`). -/
def inv8Table : ByteArray :=
  ⟨Array.ofFn (n := 256) fun i => (inv8 (UInt64.ofNat i)).toUInt8⟩

/-- `mul8` by table lookup. -/
@[inline] def mul8T (a b : UInt64) : UInt64 :=
  (mul8Table.get! ((a <<< 8) + b).toNat).toUInt64

/-- `mulByZ3` by table lookup. -/
@[inline] def mulByZ3T (v : UInt64) : UInt64 := (mulByZ3Table.get! v.toNat).toUInt64

/-- `sq8` by table lookup. -/
@[inline] def sq8T (v : UInt64) : UInt64 := (sq8Table.get! v.toNat).toUInt64

/-- `inv8` by table lookup. -/
@[inline] def inv8T (v : UInt64) : UInt64 := (inv8Table.get! v.toNat).toUInt64

/-- Table-based twin of `mulByZ4`. -/
@[inline] def mulByZ4T (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFF
  let v1 := v >>> 8
  ((v0 ^^^ mulByZ3T v1) <<< 8) ||| v1

/-- Table-based twin of `mulByZ5`. -/
@[inline] def mulByZ5T (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFF
  let v1 := v >>> 16
  ((v0 ^^^ mulByZ4T v1) <<< 16) ||| v1

/-- Table-based twin of `mulByZ6`. -/
@[inline] def mulByZ6T (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  ((v0 ^^^ mulByZ5T v1) <<< 32) ||| v1

/-- Table-based twin of `mul16`. -/
@[inline] def mul16T (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFF
  let a1 := a >>> 8
  let b0 := b &&& 0xFF
  let b1 := b >>> 8
  let p0 := mul8T a0 b0
  let p2 := mul8T a1 b1
  let p1 := mul8T (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ3T p2) <<< 8) ||| lo

/-- Table-based twin of `mul32`. -/
def mul32T (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFFFF
  let a1 := a >>> 16
  let b0 := b &&& 0xFFFF
  let b1 := b >>> 16
  let p0 := mul16T a0 b0
  let p2 := mul16T a1 b1
  let p1 := mul16T (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ4T p2) <<< 16) ||| lo

/-- Table-based twin of `mul64`. -/
def mul64T (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFFFFFFFF
  let a1 := a >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let p0 := mul32T a0 b0
  let p2 := mul32T a1 b1
  let p1 := mul32T (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ5T p2) <<< 32) ||| lo

/-- Table-based twin of `sq16`. -/
@[inline] def sq16T (v : UInt64) : UInt64 :=
  let s0 := sq8T (v &&& 0xFF)
  let s1 := sq8T (v >>> 8)
  ((mulByZ3T s1) <<< 8) ||| (s0 ^^^ s1)

/-- Table-based twin of `sq32`. -/
@[inline] def sq32T (v : UInt64) : UInt64 :=
  let s0 := sq16T (v &&& 0xFFFF)
  let s1 := sq16T (v >>> 16)
  ((mulByZ4T s1) <<< 16) ||| (s0 ^^^ s1)

/-- Table-based twin of `sq64`. -/
@[inline] def sq64T (v : UInt64) : UInt64 :=
  let s0 := sq32T (v &&& 0xFFFFFFFF)
  let s1 := sq32T (v >>> 32)
  ((mulByZ5T s1) <<< 32) ||| (s0 ^^^ s1)

/-- Table-based twin of `inv16`. -/
@[inline] def inv16T (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFF
  let v1 := v >>> 8
  let next := v0 ^^^ mulByZ3T v1
  let delta := mul8T v0 next ^^^ sq8T v1
  let d := inv8T delta
  ((mul8T d v1) <<< 8) ||| (mul8T d next)

/-- Table-based twin of `inv32`. -/
@[inline] def inv32T (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFF
  let v1 := v >>> 16
  let next := v0 ^^^ mulByZ4T v1
  let delta := mul16T v0 next ^^^ sq16T v1
  let d := inv16T delta
  ((mul16T d v1) <<< 16) ||| (mul16T d next)

/-- Table-based twin of `inv64`. -/
@[inline] def inv64T (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  let next := v0 ^^^ mulByZ5T v1
  let delta := mul32T v0 next ^^^ sq32T v1
  let d := inv32T delta
  ((mul32T d v1) <<< 32) ||| (mul32T d next)

/-! ## Level 7: GF(2^128)

The tower split falls on the limb boundary, so the halves are the limbs. -/

/-- A level-7 tower field element as two limbs, `lo` the low half. -/
structure FastBT128 where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, Inhabited

namespace FastBT128

/-- Addition is limbwise XOR. -/
@[inline] def add (a b : FastBT128) : FastBT128 := ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

/-- Multiplication: Karatsuba over the limbs with a `Z 6` generator reduction. -/
@[inline] def mul (a b : FastBT128) : FastBT128 :=
  let p0 := mul64T a.lo b.lo
  let p2 := mul64T a.hi b.hi
  let p1 := mul64T (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
  let lo := p0 ^^^ p2
  ⟨lo, p1 ^^^ lo ^^^ mulByZ6T p2⟩

/-- Multiply by the level-7 generator `Z 7`: swap halves, fold `Z 6` into the new high. -/
@[inline] def mulByZ (v : FastBT128) : FastBT128 := ⟨v.hi, v.lo ^^^ mulByZ6T v.hi⟩

/-- Squaring: the Karatsuba cross term vanishes in characteristic 2. -/
@[inline] def square (v : FastBT128) : FastBT128 :=
  let s0 := sq64T v.lo
  let s1 := sq64T v.hi
  ⟨s0 ^^^ s1, mulByZ6T s1⟩

/-- Inversion by quadratic descent (`0 ↦ 0`); same recursion as `concrete_inv`. -/
@[inline] def inv (v : FastBT128) : FastBT128 :=
  let next := v.lo ^^^ mulByZ6T v.hi
  let delta := mul64T v.lo next ^^^ sq64T v.hi
  let d := inv64T delta
  ⟨mul64T d next, mul64T d v.hi⟩

/-- Truncating constructor from `Nat`, low limb first. -/
def ofNat (n : Nat) : FastBT128 := ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64)⟩

/-- The canonical value of a two-limb element. -/
def toNat (v : FastBT128) : Nat := v.lo.toNat + v.hi.toNat * 2 ^ 64

end FastBT128

end ConcreteBinaryTower.Fast
