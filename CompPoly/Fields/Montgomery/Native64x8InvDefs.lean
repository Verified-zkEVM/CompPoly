/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Native64x8Defs

/-!
# Eight-limb inversion: runtime definitions (Mathlib-free)

The Pornin binary-GCD inverse candidate over `Limbs8` and its checked wrapper
(`invGcdRaw`), Mathlib-free for `precompileModules` consumers. The proof side is
`Montgomery/Native64x8Inv`.
-/

@[expose] public section

namespace Montgomery.Native64x8

/-! ## Per-field schedule -/

/-- Per-field schedule of the binary-GCD inverse candidate; every obligation defaults to
`decide`. -/
class GcdData (modulus : Nat) where
  /-- Divsteps in the final word-sized phase: `2·bits(p) - 2 - 15·31`. -/
  finalRounds : Nat
  /-- Initial `u`: the power of two that keeps the candidate in Montgomery form. -/
  initU : Limbs8
  initU_bounded : initU.Bounded := by decide
  initU_toNat : initU.toNat = 2 ^ (591 - finalRounds) % modulus := by decide
  /-- Final-phase chunks stay at mac width. -/
  finalRounds_le : finalRounds ≤ 62 := by decide

/-! ## Word-sized divstep loop -/

/-- Bit length of a word. -/
@[inline] def gcdBitLen (x : UInt64) : Nat := Id.run do
  if x == 0 then return 0
  let mut v := x
  let mut r : Nat := 1
  if v >>> (32 : UInt64) != 0 then v := v >>> (32 : UInt64); r := r + 32
  if v >>> (16 : UInt64) != 0 then v := v >>> (16 : UInt64); r := r + 16
  if v >>> (8 : UInt64) != 0 then v := v >>> (8 : UInt64); r := r + 8
  if v >>> (4 : UInt64) != 0 then v := v >>> (4 : UInt64); r := r + 4
  if v >>> (2 : UInt64) != 0 then v := v >>> (2 : UInt64); r := r + 2
  if v >>> (1 : UInt64) != 0 then r := r + 1
  return r

/-- The word-sized divstep loop, accumulating the transition matrix; `b` must be odd. -/
def gcdInner (rounds : Nat) (a b : UInt64) (f0 g0 f1 g1 : Int) :
    UInt64 × UInt64 × Int × Int × Int × Int :=
  match rounds with
  | 0 => (a, b, f0, g0, f1, g1)
  | n + 1 =>
    let (a, b, f0, g0, f1, g1) :=
      if a &&& 1 == 0 then
        (a, b, f0, g0, f1, g1)
      else
        let (a, b, f0, g0, f1, g1) :=
          if a < b then (b, a, f1, g1, f0, g0) else (a, b, f0, g0, f1, g1)
        (a - b, b, f0 - f1, g0 - g1, f1, g1)
    gcdInner n (a >>> 1) b f0 g0 (f1 * 2) (g1 * 2)

/-! ## Approximation: 64-bit windows over 32-bit limbs -/

/-- Read limb `i` (out-of-range indices read the top limb). -/
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
  let v7 := gcdBitLen (a.l7 ||| b.l7)
  if v7 != 0 then (7, v7) else
  let v6 := gcdBitLen (a.l6 ||| b.l6)
  if v6 != 0 then (6, v6) else
  let v5 := gcdBitLen (a.l5 ||| b.l5)
  if v5 != 0 then (5, v5) else
  let v4 := gcdBitLen (a.l4 ||| b.l4)
  if v4 != 0 then (4, v4) else
  let v3 := gcdBitLen (a.l3 ||| b.l3)
  if v3 != 0 then (3, v3) else
  let v2 := gcdBitLen (a.l2 ||| b.l2)
  if v2 != 0 then (2, v2) else
  (1, gcdBitLen (a.l1 ||| b.l1))

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

/-- `(f·a + g·b) / 2^31` as magnitude and sign. Requires `|f| + |g| ≤ 2^31`. -/
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

/-- `f·a + g·b` folded through one Montgomery reduction step. Requires
`|f| + |g| ≤ 2^31`. -/
@[inline] def gcdLinearCombMontyRed (q : Limbs8) (negInv : UInt64) (a b : Limbs8)
    (f g : Int) : Limbs8 :=
  let aS := if f < 0 then subLimbs q a else a
  let bS := if g < 0 then subLimbs q b else b
  let s := mulAccum bS (UInt64.ofNat g.natAbs)
    (mulAccum aS (UInt64.ofNat f.natAbs) State9.zero)
  condSub q (mulReduce q negInv s).toLimbs8

/-! ## Main loop and candidate -/

/-- The outer rounds: 31 divsteps on one-word approximations, then the transition matrix
applied to both tracks. -/
def gcdMainLoop (q : Limbs8) (negInv : UInt64) (rounds : Nat) (a u b v : Limbs8) :
    Limbs8 × Limbs8 × Limbs8 × Limbs8 :=
  match rounds with
  | 0 => (a, u, b, v)
  | n + 1 =>
    let (limbIdx, bits) := gcdNumBits a b
    let aT := gcdApprox a limbIdx bits
    let bT := gcdApprox b limbIdx bits
    let (_, _, f0, g0, f1, g1) := gcdInner 31 aT bT 1 0 0 1
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
to `x⁻¹·R mod p`; proof-free, callers verify. The final divsteps run as two mac-width
chunks. -/
def gcdInvCandidate (modulus : Nat) [P : GcdData modulus] (q : Limbs8)
    (negInv : UInt64) (x : Limbs8) : Limbs8 :=
  let (a, u, b, v) := gcdMainLoop q negInv 15 x P.initU q Limbs8.zero
  let aw := (a.l1 <<< 32) ||| a.l0
  let bw := (b.l1 <<< 32) ||| b.l0
  let c1 := (P.finalRounds + 1) / 2
  let (aw1, bw1, f0, g0, f1, g1) := gcdInner c1 aw bw 1 0 0 1
  let u1 := gcdLinearCombMontyRed q negInv u v f0 g0
  let v1 := gcdLinearCombMontyRed q negInv u v f1 g1
  let (_, _, _, _, fF, gF) := gcdInner (P.finalRounds - c1) aw1 bw1 1 0 0 1
  gcdLinearCombMontyRed q negInv u1 v1 fF gF

/-! ## Checked inversion over raw limbs -/

/-- `acc · x^n` in Montgomery form by binary powering. -/
def montPow (q : Limbs8) (negInv : UInt64) (acc x : Limbs8) (n : Nat) : Limbs8 :=
  if h : n = 0 then acc
  else
    montPow q negInv (if n % 2 == 1 then mul q negInv acc x else acc)
      (mul q negInv x x) (n / 2)
termination_by n
decreasing_by omega

/-- The GCD candidate, accepted only if it verifies (`z · x = 1`); else Fermat `montPow`. -/
def invGcdRaw (modulus : Nat) [GcdData modulus] (q : Limbs8) (negInv : UInt64)
    (rMod : Limbs8) (x : Limbs8) : Limbs8 :=
  let cand := gcdInvCandidate modulus q negInv x
  if cand.Bounded ∧ subBorrow cand q = 1 ∧ mul q negInv cand x = rMod then cand
  else montPow q negInv rMod x (modulus - 2)

end Montgomery.Native64x8
