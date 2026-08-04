/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native64x8Defs
import CompPoly.Fields.Montgomery.Native256Gcd

/-!
# Eight-limb inversion: runtime definitions (Mathlib-free)

The Pornin binary-GCD inverse candidate over `Limbs8` and its checked wrapper, completing
the Mathlib-free defs surface of `Montgomery/Native64x8Defs`. Linear combinations run on
the eight-limb macs; the one-word divstep loops and the final fold stay at 64-bit width.
The proof-carrying path is `Montgomery.Native64x8.FastField.invGcd`.
-/

namespace Montgomery.Native64x8

/-! ## Limb conversions -/

/-- Pack eight 32-bit limbs into four 64-bit limbs (canonical inputs: high halves zero). -/
@[inline] def Limbs8.toUInt256L (x : Limbs8) : Native256.UInt256L :=
  ⟨x.l0 ||| (x.l1 <<< 32), x.l2 ||| (x.l3 <<< 32),
   x.l4 ||| (x.l5 <<< 32), x.l6 ||| (x.l7 <<< 32)⟩

/-- Split four 64-bit limbs into eight 32-bit limbs. -/
@[inline] def Limbs8.ofUInt256L (x : Native256.UInt256L) : Limbs8 :=
  ⟨x.l0 &&& 0xffffffff, x.l0 >>> 32, x.l1 &&& 0xffffffff, x.l1 >>> 32,
   x.l2 &&& 0xffffffff, x.l2 >>> 32, x.l3 &&& 0xffffffff, x.l3 >>> 32⟩

/-! ## Approximation: 64-bit windows over 32-bit limbs -/

/-- Read limb `i ∈ {0, …, 7}` of a `Limbs8` (any other index reads the top limb). -/
@[inline] def gcdLimb (v : Limbs8) : Nat → UInt64
  | 0 => v.l0
  | 1 => v.l1
  | 2 => v.l2
  | 3 => v.l3
  | 4 => v.l4
  | 5 => v.l5
  | 6 => v.l6
  | _ => v.l7

/-- Highest nonzero limb index among limbs 1-7 of `a ||| b` and its bit length; `(1, 0)`
when all are zero. -/
@[inline] def gcdNumBits (a b : Limbs8) : Nat × Nat :=
  let v7 := Native256.gcdBitLen (a.l7 ||| b.l7)
  if v7 != 0 then (7, v7) else
  let v6 := Native256.gcdBitLen (a.l6 ||| b.l6)
  if v6 != 0 then (6, v6) else
  let v5 := Native256.gcdBitLen (a.l5 ||| b.l5)
  if v5 != 0 then (5, v5) else
  let v4 := Native256.gcdBitLen (a.l4 ||| b.l4)
  if v4 != 0 then (4, v4) else
  let v3 := Native256.gcdBitLen (a.l3 ||| b.l3)
  if v3 != 0 then (3, v3) else
  let v2 := Native256.gcdBitLen (a.l2 ||| b.l2)
  if v2 != 0 then (2, v2) else
  (1, Native256.gcdBitLen (a.l1 ||| b.l1))

/-- One-word approximation: top 33 bits (at the shared bit length) above the bottom 31;
exact once both values fit one 64-bit word. -/
@[inline] def gcdApprox (val : Limbs8) (limbIdx bits : Nat) : UInt64 :=
  if limbIdx ≤ 1 then
    (val.l1 <<< 32) ||| val.l0
  else
    let hi := gcdLimb val limbIdx
    let lo := gcdLimb val (limbIdx - 1)
    let top := ((hi <<< 32) ||| lo) >>> UInt64.ofNat (bits - 1)
    (top <<< 31) ||| (val.l0 &&& 0x7FFFFFFF)

/-! ## Nine-limb linear combinations over the native macs -/

/-- 9-limb ripple-carry add (top carry discarded). -/
@[inline] def gcdAdd9 (p q : State9) : State9 :=
  let c0 := adcCo p.t0 q.t0 0
  let c1 := adcCo p.t1 q.t1 c0
  let c2 := adcCo p.t2 q.t2 c1
  let c3 := adcCo p.t3 q.t3 c2
  let c4 := adcCo p.t4 q.t4 c3
  let c5 := adcCo p.t5 q.t5 c4
  let c6 := adcCo p.t6 q.t6 c5
  let c7 := adcCo p.t7 q.t7 c6
  ⟨adcLo p.t0 q.t0 0, adcLo p.t1 q.t1 c0, adcLo p.t2 q.t2 c1, adcLo p.t3 q.t3 c2,
   adcLo p.t4 q.t4 c3, adcLo p.t5 q.t5 c4, adcLo p.t6 q.t6 c5, adcLo p.t7 q.t7 c6,
   adcLo p.t8 q.t8 c7⟩

/-- 9-limb subtract with borrow; the wrapped difference and the final borrow. -/
@[inline] def gcdSub9 (p q : State9) : State9 × UInt64 :=
  let b0 := sbbBo p.t0 q.t0 0
  let b1 := sbbBo p.t1 q.t1 b0
  let b2 := sbbBo p.t2 q.t2 b1
  let b3 := sbbBo p.t3 q.t3 b2
  let b4 := sbbBo p.t4 q.t4 b3
  let b5 := sbbBo p.t5 q.t5 b4
  let b6 := sbbBo p.t6 q.t6 b5
  let b7 := sbbBo p.t7 q.t7 b6
  (⟨sbbLo p.t0 q.t0 0, sbbLo p.t1 q.t1 b0, sbbLo p.t2 q.t2 b1, sbbLo p.t3 q.t3 b2,
    sbbLo p.t4 q.t4 b3, sbbLo p.t5 q.t5 b4, sbbLo p.t6 q.t6 b5, sbbLo p.t7 q.t7 b6,
    sbbLo p.t8 q.t8 b7⟩,
   sbbBo p.t8 q.t8 b7)

/-- `(f·a + g·b) / 2^31` via a positive − negative magnitude split; magnitude and sign.
Requires `|f| + |g| ≤ 2^31` (the mac coefficient bound). -/
@[inline] def gcdLinearCombDiv (a b : Limbs8) (f g : Int) : Limbs8 × Int :=
  let fa := mulAccum a (UInt64.ofNat f.natAbs) State9.zero
  let gb := mulAccum b (UInt64.ofNat g.natAbs) State9.zero
  let fNeg := f < 0
  let gNeg := g < 0
  let pos := gcdAdd9 (if fNeg then State9.zero else fa) (if gNeg then State9.zero else gb)
  let neg := gcdAdd9 (if fNeg then fa else State9.zero) (if gNeg then gb else State9.zero)
  let (pmn, borrow) := gcdSub9 pos neg
  let (d, sign) :=
    if borrow == 0 then (pmn, (0 : Int)) else ((gcdSub9 neg pos).1, (-1 : Int))
  let mask : UInt64 := 0xFFFFFFFF
  let o0 := ((d.t0 >>> 31) ||| (d.t1 <<< 1)) &&& mask
  let o1 := ((d.t1 >>> 31) ||| (d.t2 <<< 1)) &&& mask
  let o2 := ((d.t2 >>> 31) ||| (d.t3 <<< 1)) &&& mask
  let o3 := ((d.t3 >>> 31) ||| (d.t4 <<< 1)) &&& mask
  let o4 := ((d.t4 >>> 31) ||| (d.t5 <<< 1)) &&& mask
  let o5 := ((d.t5 >>> 31) ||| (d.t6 <<< 1)) &&& mask
  let o6 := ((d.t6 >>> 31) ||| (d.t7 <<< 1)) &&& mask
  let o7 := ((d.t7 >>> 31) ||| (d.t8 <<< 1)) &&& mask
  (⟨o0, o1, o2, o3, o4, o5, o6, o7⟩, sign)

/-- `f·a + g·b` folded through one `2^32` Montgomery reduction step; negatives absorbed
via `q − a` / `q − b`. Requires `|f| + |g| ≤ 2^31`. -/
@[inline] def gcdLinearCombMontyRed (q : Limbs8) (negInv : UInt64) (a b : Limbs8)
    (f g : Int) : Limbs8 :=
  let aS := if f < 0 then subLimbs q a else a
  let bS := if g < 0 then subLimbs q b else b
  let s := mulAccum bS (UInt64.ofNat g.natAbs)
    (mulAccum aS (UInt64.ofNat f.natAbs) State9.zero)
  condSub q (mulReduce q negInv s).toLimbs8

/-! ## Main loop and candidate -/

/-- The outer rounds: one-word approximations, 31 divsteps, then the transition matrix
applied to `(a, b)` and to the Montgomery pair `(u, v)`. -/
def gcdMainLoop (q : Limbs8) (negInv : UInt64) (rounds : Nat) (a u b v : Limbs8) :
    Limbs8 × Limbs8 × Limbs8 × Limbs8 :=
  match rounds with
  | 0 => (a, u, b, v)
  | n + 1 =>
    let (limbIdx, bits) := gcdNumBits a b
    let aT := gcdApprox a limbIdx bits
    let bT := gcdApprox b limbIdx bits
    let (_, _, f0, g0, f1, g1) := Native256.gcdInner 31 aT bT 1 0 0 1
    let (newA, signA) := gcdLinearCombDiv a b f0 g0
    let f0 := if signA < 0 then -f0 else f0
    let g0 := if signA < 0 then -g0 else g0
    let (newB, signB) := gcdLinearCombDiv a b f1 g1
    let f1 := if signB < 0 then -f1 else f1
    let g1 := if signB < 0 then -g1 else g1
    let newU := gcdLinearCombMontyRed q negInv u v f0 g0
    let newV := gcdLinearCombMontyRed q negInv u v f1 g1
    gcdMainLoop q negInv n newA newU newB newV

/-- Pornin binary-GCD candidate for the Montgomery inverse, canonical nonzero `x·R mod p`
to `x⁻¹·R mod p`; proof-free, callers verify. The final fold runs at 64-bit width (its
coefficients reach `2^gcdFinalRounds > 2^32`). -/
def gcdInvCandidate (modulus : Nat) [P : Native256.Mont256Field modulus] (q : Limbs8)
    (negInv : UInt64) (x : Limbs8) : Limbs8 :=
  let (a, u, b, v) :=
    gcdMainLoop q negInv 15 x (Limbs8.ofUInt256L P.gcdInitU) q Limbs8.zero
  let aw := (a.l1 <<< 32) ||| a.l0
  let bw := (b.l1 <<< 32) ||| b.l0
  let (_, _, _, _, f1, g1) := Native256.gcdInner P.gcdFinalRounds aw bw 1 0 0 1
  Limbs8.ofUInt256L
    (Native256.gcdLinearCombMontyRed (modulus := modulus) u.toUInt256L v.toUInt256L f1 g1)

/-! ## Checked inversion over raw limbs -/

/-- `x^n` in Montgomery form by binary powering; `rMod` is the Montgomery one. -/
def montPow (q : Limbs8) (negInv : UInt64) (rMod : Limbs8) (x : Limbs8) (n : Nat) :
    Limbs8 := Id.run do
  let mut acc := rMod
  let mut base := x
  let mut e := n
  for _ in [0:256] do
    if e == 0 then return acc
    if e % 2 == 1 then acc := mul q negInv acc base
    base := mul q negInv base base
    e := e >>> 1
  return acc

/-- The GCD candidate, accepted only if it verifies (`z · x = 1`); else Fermat `montPow`. -/
def invGcdRaw (modulus : Nat) [Native256.Mont256Field modulus] (q : Limbs8) (negInv : UInt64)
    (rMod : Limbs8) (x : Limbs8) : Limbs8 :=
  let cand := gcdInvCandidate modulus q negInv x
  if cand.Bounded ∧ subBorrow cand q = 1 ∧ mul q negInv cand x = rMod then cand
  else montPow q negInv rMod x (modulus - 2)

end Montgomery.Native64x8
