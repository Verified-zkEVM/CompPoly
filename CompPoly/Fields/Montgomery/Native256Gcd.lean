/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256

/-!
# Pornin binary GCD: 64-bit word pieces

The word-level pieces of Pornin's optimized extended binary GCD
(<https://eprint.iacr.org/2020/972.pdf>, Algorithm 2), following plonky3's
`gcd_inversion`: the divstep loop and the 64-bit linear-combination fold. The eight-limb
outer loop lives in `Montgomery/Native64x8InvDefs.lean`. Proof-free: results are verified
at the use site (`Montgomery.Native64x8.FastField.invGcd`).
-/

namespace Montgomery
namespace Native256

variable {modulus : Nat} [P : Mont256Field modulus]

/-- Bit length of a word by binary search (no `Nat` bignum in the hot path). -/
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

/-- The word-sized divstep loop, accumulating the transition matrix `(f0, g0, f1, g1)`;
the entries satisfy `|f| + |g| ≤ 2^rounds`, exact for `rounds ≤ 62`. `b` must be odd. -/
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

/-- `f·a + g·b` folded through one `2^64` Montgomery reduction step; negative coefficients
are absorbed via `p − a` / `p − b`. -/
@[specialize] def gcdLinearCombMontyRed (a b : UInt256L) (f g : Int) : UInt256L :=
  let absF := UInt64.ofNat f.natAbs
  let absG := UInt64.ofNat g.natAbs
  let aSigned := if f < 0 then P.modulus256 - a else a
  let bSigned := if g < 0 then P.modulus256 - b else b
  let (plo, phi) := gcdLinearCombUnsigned aSigned bSigned absF absG
  interleavedMontgomeryReduction (modulus := modulus) plo.l0 ⟨plo.l1, plo.l2, plo.l3, phi⟩

end Native256
end Montgomery
