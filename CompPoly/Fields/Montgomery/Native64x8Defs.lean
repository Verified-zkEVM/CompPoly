/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/

/-!
# Eight-limb Montgomery arithmetic: runtime definitions (zero-import)

The runtime definitions of the eight-limb Montgomery arithmetic, split out of
`CompPoly.Fields.Montgomery.Native64x8` verbatim.  All correctness statements about them
live in that sibling module, which imports this one.

This module deliberately has **zero imports**: downstream consumers put it into
`precompileModules` native-compilation lanes, and `precompileModules` compiles the
entire import closure — so the runtime definitions must not pull in mathlib.
-/

namespace Montgomery
namespace Native64x8

/-! ## Word helpers -/

/-- Mask selecting the low 32 bits of a `UInt64`. -/
@[inline] def mask : UInt64 := 0xffffffff

/-- Low limb of add-with-carry: `(x + y + c) mod 2 ^ 32`. -/
@[inline] def adcLo (x y c : UInt64) : UInt64 := (x + y + c) &&& mask

/-- Carry-out of add-with-carry: `(x + y + c) / 2 ^ 32`. -/
@[inline] def adcCo (x y c : UInt64) : UInt64 := (x + y + c) >>> 32

/-- Low limb of subtract-with-borrow: `(x - y - b) mod 2 ^ 32`. -/
@[inline] def sbbLo (x y b : UInt64) : UInt64 := (x - y - b) &&& mask

/-- Borrow-out of subtract-with-borrow, read off the sign bit of the 64-bit difference. -/
@[inline] def sbbBo (x y b : UInt64) : UInt64 := (x - y - b) >>> 63

/-- Low limb of multiply-accumulate: `(t + x * y + c) mod 2 ^ 32`. -/
@[inline] def macLo (t x y c : UInt64) : UInt64 := (t + x * y + c) &&& mask

/-- High word of multiply-accumulate: `(t + x * y + c) / 2 ^ 32`. -/
@[inline] def macHi (t x y c : UInt64) : UInt64 := (t + x * y + c) >>> 32

/-- The Montgomery multiplier of a limb: `(s * negInv) mod 2 ^ 32`. -/
@[inline] def montM (s negInv : UInt64) : UInt64 := ((s &&& mask) * negInv) &&& mask

/-! ## Eight-limb values -/

/-- A 256-bit value as eight little-endian 32-bit limbs, each stored in a `UInt64`. -/
structure Limbs8 where
  /-- Limb of weight `2 ^ 0`. -/
  l0 : UInt64
  /-- Limb of weight `2 ^ 32`. -/
  l1 : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  l2 : UInt64
  /-- Limb of weight `2 ^ 96`. -/
  l3 : UInt64
  /-- Limb of weight `2 ^ 128`. -/
  l4 : UInt64
  /-- Limb of weight `2 ^ 160`. -/
  l5 : UInt64
  /-- Limb of weight `2 ^ 192`. -/
  l6 : UInt64
  /-- Limb of weight `2 ^ 224`. -/
  l7 : UInt64
deriving DecidableEq, Repr, Inhabited

namespace Limbs8

/-- The zero value. -/
def zero : Limbs8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The value one. -/
def one : Limbs8 := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Split a natural number into eight 32-bit limbs, discarding bits above `2 ^ 256`. -/
@[inline] def ofNat (n : Nat) : Limbs8 :=
  ⟨UInt64.ofNat (n &&& 0xffffffff), UInt64.ofNat (n >>> 32 &&& 0xffffffff),
    UInt64.ofNat (n >>> 64 &&& 0xffffffff), UInt64.ofNat (n >>> 96 &&& 0xffffffff),
    UInt64.ofNat (n >>> 128 &&& 0xffffffff), UInt64.ofNat (n >>> 160 &&& 0xffffffff),
    UInt64.ofNat (n >>> 192 &&& 0xffffffff), UInt64.ofNat (n >>> 224 &&& 0xffffffff)⟩

/-- The natural number represented by the limbs: `∑ lᵢ * 2 ^ (32 * i)`. -/
def toNat (x : Limbs8) : Nat :=
  x.l0.toNat + 2 ^ 32 * x.l1.toNat + 2 ^ 64 * x.l2.toNat + 2 ^ 96 * x.l3.toNat +
  2 ^ 128 * x.l4.toNat + 2 ^ 160 * x.l5.toNat + 2 ^ 192 * x.l6.toNat + 2 ^ 224 * x.l7.toNat

/-- Every limb holds at most 32 significant bits. -/
def Bounded (x : Limbs8) : Prop :=
  x.l0.toNat < 2 ^ 32 ∧ x.l1.toNat < 2 ^ 32 ∧ x.l2.toNat < 2 ^ 32 ∧ x.l3.toNat < 2 ^ 32 ∧
  x.l4.toNat < 2 ^ 32 ∧ x.l5.toNat < 2 ^ 32 ∧ x.l6.toNat < 2 ^ 32 ∧ x.l7.toNat < 2 ^ 32

instance (x : Limbs8) : Decidable x.Bounded := by
  unfold Bounded
  infer_instance

end Limbs8

/-! ## Limbwise addition and subtraction -/

/-- Limbwise add-with-carry, discarding the carry out of the top limb. -/
@[inline] def addLimbs (a b : Limbs8) : Limbs8 :=
  let c0 := adcCo a.l0 b.l0 0
  let c1 := adcCo a.l1 b.l1 c0
  let c2 := adcCo a.l2 b.l2 c1
  let c3 := adcCo a.l3 b.l3 c2
  let c4 := adcCo a.l4 b.l4 c3
  let c5 := adcCo a.l5 b.l5 c4
  let c6 := adcCo a.l6 b.l6 c5
  ⟨adcLo a.l0 b.l0 0, adcLo a.l1 b.l1 c0, adcLo a.l2 b.l2 c1, adcLo a.l3 b.l3 c2,
   adcLo a.l4 b.l4 c3, adcLo a.l5 b.l5 c4, adcLo a.l6 b.l6 c5, adcLo a.l7 b.l7 c6⟩

/-- Limbwise subtract-with-borrow. -/
@[inline] def subLimbs (a b : Limbs8) : Limbs8 :=
  let b0 := sbbBo a.l0 b.l0 0
  let b1 := sbbBo a.l1 b.l1 b0
  let b2 := sbbBo a.l2 b.l2 b1
  let b3 := sbbBo a.l3 b.l3 b2
  let b4 := sbbBo a.l4 b.l4 b3
  let b5 := sbbBo a.l5 b.l5 b4
  let b6 := sbbBo a.l6 b.l6 b5
  ⟨sbbLo a.l0 b.l0 0, sbbLo a.l1 b.l1 b0, sbbLo a.l2 b.l2 b1, sbbLo a.l3 b.l3 b2,
   sbbLo a.l4 b.l4 b3, sbbLo a.l5 b.l5 b4, sbbLo a.l6 b.l6 b5, sbbLo a.l7 b.l7 b6⟩

/-- Borrow out of the top limb of `subLimbs`. -/
@[inline] def subBorrow (a b : Limbs8) : UInt64 :=
  let b0 := sbbBo a.l0 b.l0 0
  let b1 := sbbBo a.l1 b.l1 b0
  let b2 := sbbBo a.l2 b.l2 b1
  let b3 := sbbBo a.l3 b.l3 b2
  let b4 := sbbBo a.l4 b.l4 b3
  let b5 := sbbBo a.l5 b.l5 b4
  let b6 := sbbBo a.l6 b.l6 b5
  sbbBo a.l7 b.l7 b6

/-! ## Conditional subtraction and field operations -/

/-- Subtract the modulus once if the value is at least the modulus.  The borrow chain
decides the branch, so no comparison is needed. -/
@[inline] def condSub (q t : Limbs8) : Limbs8 :=
  if subBorrow t q == 0 then subLimbs t q else t

/-- Modular addition. -/
@[inline] def add (q a b : Limbs8) : Limbs8 := condSub q (addLimbs a b)

/-- Modular subtraction: on a borrow, the modulus is added back. -/
@[inline] def sub (q a b : Limbs8) : Limbs8 :=
  let d := subLimbs a b
  if subBorrow a b == 0 then d else addLimbs d q

/-- Modular negation. -/
@[inline] def neg (q a : Limbs8) : Limbs8 := sub q Limbs8.zero a

/-! ## CIOS multiplication -/

/-- The CIOS accumulator: eight limbs plus one head limb. -/
structure State9 where
  /-- Limb of weight `2 ^ 0`. -/
  t0 : UInt64
  /-- Limb of weight `2 ^ 32`. -/
  t1 : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  t2 : UInt64
  /-- Limb of weight `2 ^ 96`. -/
  t3 : UInt64
  /-- Limb of weight `2 ^ 128`. -/
  t4 : UInt64
  /-- Limb of weight `2 ^ 160`. -/
  t5 : UInt64
  /-- Limb of weight `2 ^ 192`. -/
  t6 : UInt64
  /-- Limb of weight `2 ^ 224`. -/
  t7 : UInt64
  /-- Head limb of weight `2 ^ 256`. -/
  t8 : UInt64
deriving DecidableEq, Repr, Inhabited

namespace State9

/-- The zero accumulator. -/
@[inline] def zero : State9 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The eight low limbs of the accumulator. -/
@[inline] def toLimbs8 (t : State9) : Limbs8 := ⟨t.t0, t.t1, t.t2, t.t3, t.t4, t.t5, t.t6, t.t7⟩

/-- The natural number represented by the accumulator. -/
def toNat (t : State9) : Nat := t.toLimbs8.toNat + 2 ^ 256 * t.t8.toNat

/-- Every limb of the accumulator holds at most 32 significant bits. -/
def Bounded (t : State9) : Prop := t.toLimbs8.Bounded ∧ t.t8.toNat < 2 ^ 32

end State9

/-- The multiply half of a CIOS round: accumulate `a * bi` into the accumulator.  The carry
out of the top limb is kept in the head limb, so no information is lost. -/
@[inline] def mulAccum (a : Limbs8) (bi : UInt64) (t : State9) : State9 :=
  let k0 := macHi t.t0 a.l0 bi 0
  let k1 := macHi t.t1 a.l1 bi k0
  let k2 := macHi t.t2 a.l2 bi k1
  let k3 := macHi t.t3 a.l3 bi k2
  let k4 := macHi t.t4 a.l4 bi k3
  let k5 := macHi t.t5 a.l5 bi k4
  let k6 := macHi t.t6 a.l6 bi k5
  let k7 := macHi t.t7 a.l7 bi k6
  ⟨macLo t.t0 a.l0 bi 0, macLo t.t1 a.l1 bi k0, macLo t.t2 a.l2 bi k1,
    macLo t.t3 a.l3 bi k2, macLo t.t4 a.l4 bi k3, macLo t.t5 a.l5 bi k4,
    macLo t.t6 a.l6 bi k5, macLo t.t7 a.l7 bi k6, t.t8 + k7⟩

/-- The reduce half of a CIOS round: add the multiple `montM s.t0 negInv` of the modulus that
cancels the low limb, then drop that limb.  `negInv` has to be `-q⁻¹ mod 2 ^ 32`. -/
@[inline] def mulReduce (q : Limbs8) (negInv : UInt64) (s : State9) : State9 :=
  let m := montM s.t0 negInv
  let u0 := macHi s.t0 m q.l0 0
  let u1 := macHi s.t1 m q.l1 u0
  let u2 := macHi s.t2 m q.l2 u1
  let u3 := macHi s.t3 m q.l3 u2
  let u4 := macHi s.t4 m q.l4 u3
  let u5 := macHi s.t5 m q.l5 u4
  let u6 := macHi s.t6 m q.l6 u5
  let u7 := macHi s.t7 m q.l7 u6
  ⟨macLo s.t1 m q.l1 u0, macLo s.t2 m q.l2 u1, macLo s.t3 m q.l3 u2,
    macLo s.t4 m q.l4 u3, macLo s.t5 m q.l5 u4, macLo s.t6 m q.l6 u5,
    macLo s.t7 m q.l7 u6, adcLo s.t8 u7 0, adcCo s.t8 u7 0⟩

/-- One CIOS outer round: accumulate `a * bi` into the accumulator, then reduce away one
limb. -/
@[inline] def mulRound (q : Limbs8) (negInv : UInt64) (a : Limbs8) (bi : UInt64)
    (t : State9) : State9 :=
  mulReduce q negInv (mulAccum a bi t)

/-- CIOS Montgomery multiplication: eight rounds followed by one conditional
subtraction. -/
@[inline] def mul (q : Limbs8) (negInv : UInt64) (a b : Limbs8) : Limbs8 :=
  let t := mulRound q negInv a b.l0 State9.zero
  let t := mulRound q negInv a b.l1 t
  let t := mulRound q negInv a b.l2 t
  let t := mulRound q negInv a b.l3 t
  let t := mulRound q negInv a b.l4 t
  let t := mulRound q negInv a b.l5 t
  let t := mulRound q negInv a b.l6 t
  let t := mulRound q negInv a b.l7 t
  condSub q t.toLimbs8

/-- Montgomery squaring. -/
@[inline] def square (q : Limbs8) (negInv : UInt64) (a : Limbs8) : Limbs8 :=
  mul q negInv a a

end Native64x8
end Montgomery
