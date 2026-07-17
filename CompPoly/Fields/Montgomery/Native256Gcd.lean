/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256

/-!
# Pornin Binary-GCD Inverse Candidate

Pornin's optimized extended binary GCD (<https://eprint.iacr.org/2020/972.pdf>, Algorithm 2)
computing Montgomery-form inverse candidates, following plonky3's `gcd_inversion`. Proof-free
by design: `gcdInvCandidate` is verified at its use site (`Montgomery.Native256.inv`) against
the proven multiplier, with a proven Fermat-window fallback, so correctness never depends on
this file's internals.
-/

namespace Montgomery
namespace Native256

variable {modulus : ℕ} [P : Mont256Field modulus]

/-- Native bit length of a word (`64 − clz`, by binary search); no `Nat.log2`/bignum. -/
@[inline] def gcdBitLen (x : UInt64) : ℕ := Id.run do
  if x == 0 then return 0
  let mut v := x
  let mut r : ℕ := 1
  if v >>> (32 : UInt64) != 0 then v := v >>> (32 : UInt64); r := r + 32
  if v >>> (16 : UInt64) != 0 then v := v >>> (16 : UInt64); r := r + 16
  if v >>> (8 : UInt64) != 0 then v := v >>> (8 : UInt64); r := r + 8
  if v >>> (4 : UInt64) != 0 then v := v >>> (4 : UInt64); r := r + 4
  if v >>> (2 : UInt64) != 0 then v := v >>> (2 : UInt64); r := r + 2
  if v >>> (1 : UInt64) != 0 then r := r + 1
  return r

/-- Highest nonzero limb index among limbs 1, 2, 3 (of `a ||| b`) and its bit length; `(1, 0)`
when all three are zero, which makes the approximation below exact for one-word values. -/
@[inline] def gcdNumBits (l1 l2 l3 : UInt64) : ℕ × ℕ :=
  let v3 := gcdBitLen l3
  if v3 != 0 then (3, v3)
  else
    let v2 := gcdBitLen l2
    if v2 != 0 then (2, v2)
    else (1, gcdBitLen l1)

/-- Read limb `i ∈ {0, 1, 2, 3}` of a `UInt256L` (any other index reads the top limb). -/
@[inline] def gcdLimb (v : UInt256L) (i : ℕ) : UInt64 :=
  match i with
  | 0 => v.l0
  | 1 => v.l1
  | 2 => v.l2
  | _ => v.l3

/-- One-word approximation of `val`: its top 33 bits (relative to the shared bit length
`64·limb + bits` of the two values being approximated) glued above its bottom 31 bits, as a
two-word funnel shift. Divstep decisions on the approximations agree with the full values for
at least 31 rounds (Pornin, §3). -/
@[inline] def gcdApprox (val : UInt256L) (limb : ℕ) (bits : ℕ) : UInt64 :=
  let hi := gcdLimb val limb
  let lo := gcdLimb val (limb - 1)
  let s := bits + 31                       -- in [31, 95]
  let topBits : UInt64 :=
    if s < 64 then (lo >>> UInt64.ofNat s) ||| (hi <<< UInt64.ofNat (64 - s))
    else hi >>> UInt64.ofNat (s - 64)
  let bottomBits := val.l0 &&& 0x7FFFFFFF
  (topBits <<< (31 : UInt64)) ||| bottomBits

/-- The word-sized divstep loop: a mini binary GCD on `a`, `b` accumulating the transition
matrix `(f0, g0, f1, g1)` (meaning `a ← (f0·a₀ + g0·b₀)/2^rounds`, `b ← (f1·a₀ + g1·b₀)`,
suitably scaled). After `n` rounds the entries satisfy `|f| + |g| ≤ 2^n`, so they stay exact
for `rounds ≤ 62`. `b` must be odd (it is: `b₀ = p`). -/
def gcdInner (rounds : ℕ) (a b : UInt64) (f0 g0 f1 g1 : Int) :
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

/-- 5-limb zero. -/
@[inline] def gcdZero5 : UInt256L × UInt64 := (⟨0, 0, 0, 0⟩, 0)

/-- `a · f` as a 5-limb unsigned value (via the proven `mulSmall`). -/
@[inline] def gcdMul5 (a : UInt256L) (f : UInt64) : UInt256L × UInt64 :=
  let (low, hi) := mulSmall a f          -- a·f = low + hi·2⁶⁴
  (⟨low, hi.l0, hi.l1, hi.l2⟩, hi.l3)

/-- 5-limb ripple-carry add (carry out of the top limb discarded). -/
@[inline] def gcdAdd5 (p q : UInt256L × UInt64) : UInt256L × UInt64 :=
  let (r0, c0) := addc p.1.l0 q.1.l0 0
  let (r1, c1) := addc p.1.l1 q.1.l1 c0
  let (r2, c2) := addc p.1.l2 q.1.l2 c1
  let (r3, c3) := addc p.1.l3 q.1.l3 c2
  let (r4, _)  := addc p.2 q.2 c3
  (⟨r0, r1, r2, r3⟩, r4)

/-- 5-limb subtract with borrow; returns the wrapped difference and the final borrow. -/
@[inline] def gcdSub5 (p q : UInt256L × UInt64) : (UInt256L × UInt64) × UInt64 :=
  let (r0, b0) := subb p.1.l0 q.1.l0 0
  let (r1, b1) := subb p.1.l1 q.1.l1 b0
  let (r2, b2) := subb p.1.l2 q.1.l2 b1
  let (r3, b3) := subb p.1.l3 q.1.l3 b2
  let (r4, b4) := subb p.2 q.2 b3
  ((⟨r0, r1, r2, r3⟩, r4), b4)

/-- `(f·a + g·b) / 2^k` with signed one-word `f`, `g`, via a positive − negative split: the
two magnitude products are accumulated separately and subtracted, recovering the sign from the
borrow, with no two's-complement wide arithmetic. Returns the magnitude (the exact quotient, which
fits four limbs since `|f| + |g| ≤ 2^k`) and the sign (`0` or `-1`). -/
@[inline] def gcdLinearCombDiv (a b : UInt256L) (f g : Int) (k : ℕ) : UInt256L × Int :=
  let faTerm := gcdMul5 a (UInt64.ofNat f.natAbs)
  let gbTerm := gcdMul5 b (UInt64.ofNat g.natAbs)
  let fNeg := f < 0
  let gNeg := g < 0
  let pos := gcdAdd5 (if fNeg then gcdZero5 else faTerm) (if gNeg then gcdZero5 else gbTerm)
  let neg := gcdAdd5 (if fNeg then faTerm else gcdZero5) (if gNeg then gbTerm else gcdZero5)
  let (pmn, borrow) := gcdSub5 pos neg
  let (diff, sign) :=
    if borrow == 0 then (pmn, (0 : Int)) else ((gcdSub5 neg pos).1, (-1 : Int))
  let shk := UInt64.ofNat k
  let shc := UInt64.ofNat (64 - k)
  let d := diff.1
  let d4 := diff.2
  let o0 := (d.l0 >>> shk) ||| (d.l1 <<< shc)
  let o1 := (d.l1 >>> shk) ||| (d.l2 <<< shc)
  let o2 := (d.l2 >>> shk) ||| (d.l3 <<< shc)
  let o3 := (d.l3 >>> shk) ||| (d4 <<< shc)
  (⟨o0, o1, o2, o3⟩, sign)

/-- `a·f + b·g` with unsigned one-word `f`, `g`, as a 5-limb value. -/
@[inline] def gcdLinearCombUnsigned (a b : UInt256L) (f g : UInt64) : UInt256L × UInt64 :=
  let (p0, ph) := mulSmall a f
  let (q0, qh) := mulSmall b g
  let (r0, c0) := addc p0 q0 0
  let (r1, c1) := addc ph.l0 qh.l0 c0
  let (r2, c2) := addc ph.l1 qh.l1 c1
  let (r3, c3) := addc ph.l2 qh.l2 c2
  let (r4, _)  := addc ph.l3 qh.l3 c3
  (⟨r0, r1, r2, r3⟩, r4)

/-- `f·a + g·b` for canonical residues `a`, `b` and signed one-word `f`, `g`, folded through
one Montgomery reduction step (`· 2⁻⁶⁴ mod p`). A negative coefficient is absorbed by
substituting `p − a` (resp. `p − b`), keeping the combination unsigned. -/
@[specialize] def gcdLinearCombMontyRed (a b : UInt256L) (f g : Int) : UInt256L :=
  let absF := UInt64.ofNat f.natAbs
  let absG := UInt64.ofNat g.natAbs
  let aSigned := if f < 0 then P.modulus256 - a else a
  let bSigned := if g < 0 then P.modulus256 - b else b
  let (plo, phi) := gcdLinearCombUnsigned aSigned bSigned absF absG
  interleavedMontgomeryReduction (modulus := modulus) plo.l0 ⟨plo.l1, plo.l2, plo.l3, phi⟩

/-- The outer rounds: approximate `a`, `b` by one word each, run 31 word-sized divsteps, then
apply the accumulated transition matrix to the full `(a, b)` (shifting out the `2^31`) and to
the Montgomery pair `(u, v)` (reducing by `2^64`), flipping matrix rows negated by the
`a`/`b` sign fix-up. -/
@[specialize] def gcdMainLoop (rounds : ℕ) (a u b v : UInt256L) :
    UInt256L × UInt256L × UInt256L × UInt256L :=
  match rounds with
  | 0 => (a, u, b, v)
  | n + 1 =>
    let (limb, bits) := gcdNumBits (a.l1 ||| b.l1) (a.l2 ||| b.l2) (a.l3 ||| b.l3)
    let aTilde := gcdApprox a limb bits
    let bTilde := gcdApprox b limb bits
    let (_, _, f0, g0, f1, g1) := gcdInner 31 aTilde bTilde 1 0 0 1
    let (newA, signA) := gcdLinearCombDiv a b f0 g0 31
    let f0 := if signA < 0 then -f0 else f0
    let g0 := if signA < 0 then -g0 else g0
    let (newB, signB) := gcdLinearCombDiv a b f1 g1 31
    let f1 := if signB < 0 then -f1 else f1
    let g1 := if signB < 0 then -g1 else g1
    let newU := gcdLinearCombMontyRed (modulus := modulus) u v f0 g0
    let newV := gcdLinearCombMontyRed (modulus := modulus) u v f1 g1
    gcdMainLoop n newA newU newB newV

/-- Pornin binary-GCD candidate for the Montgomery inverse: for canonical nonzero `input`
(the Montgomery residue `x·R mod p`) this computes `x⁻¹·R mod p`. Proof-free: callers must
verify the result (`Montgomery.Native256.inv` multiplies it back against the input and falls
back to the proven Fermat window, so a candidate miss can never affect correctness). -/
@[specialize] def gcdInvCandidate (input : UInt256L) : UInt256L :=
  let (a, u, b, v) := gcdMainLoop (modulus := modulus) 15 input P.gcdInitU P.modulus256 ⟨0, 0, 0, 0⟩
  let (_, _, _, _, f1, g1) := gcdInner P.gcdFinalRounds a.l0 b.l0 1 0 0 1
  gcdLinearCombMontyRed (modulus := modulus) u v f1 g1

end Native256
end Montgomery
