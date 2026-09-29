/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Montgomery.Native64x4Defs
public import CompPoly.Fields.Montgomery.Native64x8InvDefs

/-!
# Four-limb inversion: runtime definitions (Mathlib-free)

The Pornin binary-GCD inverse candidate over `Limbs4` and its checked wrapper
(`invGcdRaw`), Mathlib-free for `precompileModules` consumers.  The word-sized divstep loop
and bit-length helper are shared with the eight-limb stack.  The proof side is
`Montgomery/Native64x4Inv`.
-/

@[expose] public section

namespace Montgomery.Native64x4

open Montgomery.Native64x8 (gcdInner gcdBitLen)

/-! ## Per-field schedule -/

/-- Per-field schedule of the binary-GCD inverse candidate; every obligation defaults to
`decide`. -/
class GcdData (modulus : Nat) where
  /-- Divsteps in the final word-sized phase: `2·bits(p) - 2 - 15·31`. -/
  finalRounds : Nat
  /-- Initial `u`: the power of two that keeps the candidate in Montgomery form. -/
  initU : Limbs4
  initU_toNat : initU.toNat = 2 ^ (1135 - finalRounds) % modulus := by decide
  /-- Final-phase chunks stay at mac width. -/
  finalRounds_le : finalRounds ≤ 62 := by decide

/-! ## Five-word arithmetic -/

/-- `x * k` as five words. -/
@[inline] def mulWord (x : Limbs4) (k : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (w0, c) := mac 0 x.l0 k 0
  let (w1, c) := mac 0 x.l1 k c
  let (w2, c) := mac 0 x.l2 k c
  let (w3, w4) := mac 0 x.l3 k c
  (w0, w1, w2, w3, w4)

/-- Five-word add: the sum words and the carry out. -/
@[inline] def add5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (s0, c) := adc a0 b0 0
  let (s1, c) := adc a1 b1 c
  let (s2, c) := adc a2 b2 c
  let (s3, c) := adc a3 b3 c
  let (s4, c) := adc a4 b4 c
  (s0, s1, s2, s3, s4, c)

/-- Five-word subtract: the difference words and the borrow out. -/
@[inline] def sub5 (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  let (d0, b) := sbb a0 b0 0
  let (d1, b) := sbb a1 b1 b
  let (d2, b) := sbb a2 b2 b
  let (d3, b) := sbb a3 b3 b
  let (d4, b) := sbb a4 b4 b
  (d0, d1, d2, d3, d4, b)

/-! ## Linear combinations -/

/-- `(f·a + g·b) / 2^31` as magnitude and sign.  Requires `|f| + |g| ≤ 2^31`. -/
@[inline] def gcdLinearCombDiv (a b : Limbs4) (f g : Int) : Limbs4 × Int :=
  let (fa0, fa1, fa2, fa3, fa4) := mulWord a (UInt64.ofNat f.natAbs)
  let (gb0, gb1, gb2, gb3, gb4) := mulWord b (UInt64.ofNat g.natAbs)
  let fNeg := f < 0
  let gNeg := g < 0
  let (p0, p1, p2, p3, p4) :=
    if fNeg then ((0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64))
    else (fa0, fa1, fa2, fa3, fa4)
  let (q0, q1, q2, q3, q4) :=
    if gNeg then ((0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64))
    else (gb0, gb1, gb2, gb3, gb4)
  let (n0, n1, n2, n3, n4) :=
    if fNeg then (fa0, fa1, fa2, fa3, fa4)
    else ((0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64))
  let (m0, m1, m2, m3, m4) :=
    if gNeg then (gb0, gb1, gb2, gb3, gb4)
    else ((0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64), (0 : UInt64))
  let (s0, s1, s2, s3, s4, _) := add5 p0 p1 p2 p3 p4 q0 q1 q2 q3 q4
  let (t0, t1, t2, t3, t4, _) := add5 n0 n1 n2 n3 n4 m0 m1 m2 m3 m4
  let (d0, d1, d2, d3, d4, borrow) := sub5 s0 s1 s2 s3 s4 t0 t1 t2 t3 t4
  if borrow == 0 then
    (⟨(d0 >>> 31) ||| (d1 <<< 33), (d1 >>> 31) ||| (d2 <<< 33), (d2 >>> 31) ||| (d3 <<< 33),
      (d3 >>> 31) ||| (d4 <<< 33)⟩, (0 : Int))
  else
    let (e0, e1, e2, e3, e4, _) := sub5 t0 t1 t2 t3 t4 s0 s1 s2 s3 s4
    (⟨(e0 >>> 31) ||| (e1 <<< 33), (e1 >>> 31) ||| (e2 <<< 33), (e2 >>> 31) ||| (e3 <<< 33),
      (e3 >>> 31) ||| (e4 <<< 33)⟩, (-1 : Int))

/-- `n - u` as limbs, for `u < n`. -/
@[inline] def negMod (q u : Limbs4) : Limbs4 :=
  let (d0, d1, d2, d3, _) := subLimbs q u
  ⟨d0, d1, d2, d3⟩

/-- The Montgomery linear combination on magnitudes: `(F·uS + G·vS) · 2^-64 mod q`, reduced
once through `condSubWide`.  Requires `F + G ≤ 2^31` and `uS, vS ≤ q`. -/
@[inline] def lincombTail (q : Limbs4) (negInv : UInt64) (uS vS : Limbs4) (F G : UInt64) :
    Limbs4 :=
  let (a0, a1, a2, a3, a4) := mulWord uS F
  let (b0, b1, b2, b3, b4) := mulWord vS G
  let (s0, s1, s2, s3, s4, _) := add5 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
  let m := montM s0 negInv
  let (n0, n1, n2, n3, n4) := mulWord q m
  let (_, t1, t2, t3, t4, t5) := add5 s0 s1 s2 s3 s4 n0 n1 n2 n3 n4
  condSubWide q ⟨t1, t2, t3, t4, t5⟩

/-- `(f·u + g·v) · 2^-64 mod q`, canonical.  Requires `|f| + |g| ≤ 2^31` and `u, v < q`. -/
@[inline] def gcdLinearCombMontyRed (q : Limbs4) (negInv : UInt64) (u v : Limbs4)
    (f g : Int) : Limbs4 :=
  lincombTail q negInv (if f < 0 then negMod q u else u) (if g < 0 then negMod q v else v)
    (UInt64.ofNat f.natAbs) (UInt64.ofNat g.natAbs)

/-! ## Approximation: one word at the shared bit length -/

/-- Read limb `i` (out-of-range indices read the top limb). -/
@[inline] def gcdLimb (v : Limbs4) : Nat → UInt64
  | 0 => v.l0
  | 1 => v.l1
  | 2 => v.l2
  | _ => v.l3

/-- Highest nonzero limb index among limbs 1-3 of `a ||| b` and its bit length; `(0, 0)`
when all are zero. -/
@[inline] def gcdNumBits (a b : Limbs4) : Nat × Nat :=
  let v3 := gcdBitLen (a.l3 ||| b.l3)
  if v3 != 0 then (3, v3) else
  let v2 := gcdBitLen (a.l2 ||| b.l2)
  if v2 != 0 then (2, v2) else
  let v1 := gcdBitLen (a.l1 ||| b.l1)
  if v1 != 0 then (1, v1) else (0, 0)

/-- One-word approximation: the top 33 bits at the shared bit length above the bottom 31;
exact once both values fit one word. -/
@[inline] def gcdApprox (val : Limbs4) (limbIdx bits : Nat) : UInt64 :=
  if limbIdx == 0 then val.l0
  else
    let hi := gcdLimb val limbIdx
    let lo := gcdLimb val (limbIdx - 1)
    let top :=
      if bits ≥ 33 then hi >>> (UInt64.ofNat (bits - 33))
      else ((hi <<< (UInt64.ofNat (33 - bits))) ||| (lo >>> (UInt64.ofNat (bits + 31)))) &&&
        0x1FFFFFFFF
    (top <<< 31) ||| (val.l0 &&& 0x7FFFFFFF)

/-! ## Main loop and candidate -/

/-- The outer rounds: 31 divsteps on one-word approximations, then the transition matrix
applied to both tracks. -/
def gcdMainLoop (q : Limbs4) (negInv : UInt64) (rounds : Nat) (a u b v : Limbs4) :
    Limbs4 × Limbs4 × Limbs4 × Limbs4 :=
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

/-- The final divsteps as two mac-width chunks, folding the Montgomery pair. -/
def gcdFinalChunks (q : Limbs4) (negInv : UInt64) (finalRounds : Nat)
    (a u b v : Limbs4) : Limbs4 :=
  let c1 := (finalRounds + 1) / 2
  let (aw1, bw1, f0, g0, f1, g1) := gcdInner c1 a.l0 b.l0 1 0 0 1
  let u1 := gcdLinearCombMontyRed q negInv u v f0 g0
  let v1 := gcdLinearCombMontyRed q negInv u v f1 g1
  let (_, _, _, _, fF, gF) := gcdInner (finalRounds - c1) aw1 bw1 1 0 0 1
  gcdLinearCombMontyRed q negInv u1 v1 fF gF

/-- Pornin binary-GCD candidate for the Montgomery inverse, canonical nonzero `x·R mod p`
to `x⁻¹·R mod p`; proof-free, callers verify. -/
def gcdInvCandidate (modulus : Nat) [P : GcdData modulus] (q : Limbs4)
    (negInv : UInt64) (x : Limbs4) : Limbs4 :=
  let (a, u, b, v) := gcdMainLoop q negInv 15 x P.initU q Limbs4.zero
  gcdFinalChunks q negInv P.finalRounds a u b v

/-! ## Checked inversion over raw limbs -/

/-- `acc · x^n` in Montgomery form by binary powering. -/
def montPow (q : Limbs4) (negInv : UInt64) (acc x : Limbs4) (n : Nat) : Limbs4 :=
  if h : n = 0 then acc
  else
    montPow q negInv (if n % 2 == 1 then mul q negInv acc x else acc)
      (mul q negInv x x) (n / 2)
termination_by n
decreasing_by omega

/-- The GCD candidate, accepted only if it verifies (`z · x = 1`); else Fermat `montPow`. -/
def invGcdRaw (modulus : Nat) [GcdData modulus] (q : Limbs4) (negInv : UInt64)
    (rMod : Limbs4) (x : Limbs4) : Limbs4 :=
  let cand := gcdInvCandidate modulus q negInv x
  if (subLimbs cand q).2.2.2.2 = 1 ∧ mul q negInv cand x = rMod then cand
  else montPow q negInv rMod x (modulus - 2)

end Montgomery.Native64x4
