/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256.UInt256L

/-!
# 64-bit-limb Montgomery reduction (GCD engine)

The `Mont256Field` data class and the CIOS reduction step over four `UInt64` limbs
(`R = 2 ^ 256`). Proof-free runtime definitions, verified at the call site.
-/

namespace Montgomery
namespace Native256

/-- Per-field data for the binary-GCD inverse candidate; every obligation defaults to
`decide`. -/
class Mont256Field (modulus : Nat) where
  /-- `modulus` as a 256-bit word. -/
  modulus256 : UInt256L
  /-- `-modulus⁻¹ mod 2^64`. -/
  montgomeryNegInv : UInt64
  /-- Divsteps in the final word-sized round: `2·bits(p) - 2 - 15·31`. -/
  gcdFinalRounds : Nat
  /-- Initial `u`: the power of two that keeps the candidate in Montgomery form. -/
  gcdInitU : UInt256L
  modulus256_toNat : modulus256.toNat = modulus := by decide
  montgomeryNegInv_mul_modulus_mod_two_pow_64 :
    montgomeryNegInv.toNat * modulus % 2 ^ 64 = 2 ^ 64 - 1 := by decide
  gcdInitU_toNat : gcdInitU.toNat = 2 ^ (591 - gcdFinalRounds) % modulus := by decide
  /-- Final-round transition entries stay word-sized. -/
  gcdFinalRounds_le : gcdFinalRounds ≤ 62 := by decide

variable {modulus : Nat} [P : Mont256Field modulus]

/-- Reduce a value below `2·modulus` to canonical range. -/
@[inline]
def conditionalSubtract (x : UInt256L) : UInt256L :=
  if x < P.modulus256 then x else x - P.modulus256

/-- Reduce a value `lo + carry·2²⁵⁶` below `2·modulus` to canonical range. -/
@[inline]
def reduceWideRaw (lo : UInt256L) (carry : UInt64) : UInt256L :=
  if carry = 0 then conditionalSubtract (modulus := modulus) lo else lo - P.modulus256

/-- One CIOS step: `(acc0 + acc·2⁶⁴)·2⁻⁶⁴ mod p` for a 5-limb accumulator `< p·2⁶⁴`. -/
@[inline]
def interleavedMontgomeryReduction (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := P.montgomeryNegInv * acc0
  let prod := mulSmall P.modulus256 t
  let cin := (addc acc0 prod.1 0).2
  let sc := UInt256L.addCarryOut acc prod.2 cin
  reduceWideRaw (modulus := modulus) sc.1 sc.2

end Native256
end Montgomery
