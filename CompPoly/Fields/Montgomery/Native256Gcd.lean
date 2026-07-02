/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256

/-!
# Native 256-bit Montgomery field — Pornin binary-GCD inverse candidate

The optimized extended binary GCD of Thomas Pornin, *Optimized Binary GCD for Modular
Inversion* (<https://eprint.iacr.org/2020/972.pdf>, Algorithm 2), computing modular inverses in
Montgomery form roughly 4–5× faster than the fixed-window Fermat exponentiation for 256-bit
prime fields. The implementation follows plonky3's `gcd_inversion` for the BN254 scalar field
(`bn254/src/helpers.rs`), generalized over `Mont256Field` with a per-field divstep schedule.

The algorithm threads `(a, u, b, v)` from `(x, u₀, p, 0)` maintaining `a·u₀ ≡ u·x` and
`b·u₀ ≡ v·x (mod p)`, where every outer round runs 31 divsteps of a *word-sized* binary GCD on
one-word approximations of `a` and `b` (top 33 bits + bottom 31 bits), then applies the
accumulated 2×2 transition matrix to the full four-limb values. After 15 outer rounds `a` and
`b` fit in one word and `gcdFinalRounds` exact divsteps finish the job: `b = gcd(x, p) = 1`, so
`v ≡ u₀·x⁻¹`, and `u₀ = gcdInitU` is chosen so that `v` is exactly the Montgomery residue of
the inverse (see `Mont256Field.gcdInitU`).

Everything here is **proof-free by design**: `gcdInvCandidate` is a total native-word program
whose result is *verified at the use site* — `Montgomery.Native256.inv` checks
`candidate · x = 1` with the proven Montgomery multiplier and falls back to the proven Fermat
window on failure, so field correctness never depends on this file's internals (only the fast
path's hit rate does). See `CompPoly.Fields.Montgomery.Native256Field`.
-/

namespace Montgomery
namespace Native256

variable {F : Type} [P : Mont256Field F]

/-- Native bit length of a word (`64 − clz`, by binary search); no `Nat.log2`/bignum. -/
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

/-- Highest nonzero limb index among limbs 1, 2, 3 (of `a ||| b`) and its bit length; `(1, 0)`
when all three are zero, which makes the approximation below exact for one-word values. -/
@[inline] def gcdNumBits (l1 l2 l3 : UInt64) : Nat × Nat :=
  let v3 := gcdBitLen l3
  if v3 != 0 then (3, v3)
  else
    let v2 := gcdBitLen l2
    if v2 != 0 then (2, v2)
    else (1, gcdBitLen l1)

/-- Read limb `i ∈ {0, 1, 2, 3}` of a `UInt256L` (any other index reads the top limb). -/
@[inline] def gcdLimb (v : UInt256L) (i : Nat) : UInt64 :=
  match i with
  | 0 => v.l0
  | 1 => v.l1
  | 2 => v.l2
  | _ => v.l3

/-- One-word approximation of `val`: its top 33 bits (relative to the shared bit length
`64·limb + bits` of the two values being approximated) glued above its bottom 31 bits, as a
two-word funnel shift. Divstep decisions on the approximations agree with the full values for
at least 31 rounds (Pornin, §3). -/
@[inline] def gcdApprox (val : UInt256L) (limb : Nat) (bits : Nat) : UInt64 :=
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
borrow — no two's-complement wide arithmetic. Returns the magnitude (the exact quotient, which
fits four limbs since `|f| + |g| ≤ 2^k`) and the sign (`0` or `-1`). -/
@[inline] def gcdLinearCombDiv (a b : UInt256L) (f g : Int) (k : Nat) : UInt256L × Int :=
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
  let aSigned := if f < 0 then P.modulus - a else a
  let bSigned := if g < 0 then P.modulus - b else b
  let (plo, phi) := gcdLinearCombUnsigned aSigned bSigned absF absG
  interleavedMontgomeryReduction (F := F) plo.l0 ⟨plo.l1, plo.l2, plo.l3, phi⟩

/-- The outer rounds: approximate `a`, `b` by one word each, run 31 word-sized divsteps, then
apply the accumulated transition matrix to the full `(a, b)` (shifting out the `2^31`) and to
the Montgomery pair `(u, v)` (reducing by `2^64`), flipping matrix rows negated by the
`a`/`b` sign fix-up. -/
@[specialize] def gcdMainLoop (rounds : Nat) (a u b v : UInt256L) :
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
    let newU := gcdLinearCombMontyRed (F := F) u v f0 g0
    let newV := gcdLinearCombMontyRed (F := F) u v f1 g1
    gcdMainLoop n newA newU newB newV

/-- Pornin binary-GCD candidate for the Montgomery inverse: for canonical nonzero `input`
(the Montgomery residue `x·R mod p`) this computes `x⁻¹·R mod p`. Proof-free: callers must
verify the result (`Montgomery.Native256.inv` multiplies it back against the input and falls
back to the proven Fermat window, so a candidate miss can never affect correctness). -/
@[specialize] def gcdInvCandidate (input : UInt256L) : UInt256L :=
  let (a, u, b, v) := gcdMainLoop (F := F) 15 input P.gcdInitU P.modulus ⟨0, 0, 0, 0⟩
  let (_, _, _, _, f1, g1) := gcdInner P.gcdFinalRounds a.l0 b.l0 1 0 0 1
  gcdLinearCombMontyRed (F := F) u v f1 g1

end Native256
end Montgomery
