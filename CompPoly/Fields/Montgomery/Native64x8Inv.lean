/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native64x8Field
import CompPoly.Fields.Montgomery.Native64x8InvDefs

/-!
# Fast inversion for eight-limb Montgomery fields

The Pornin binary-GCD inverse for the eight-limb carrier: the 64-bit-word candidate of
`Montgomery.Native256Gcd`, verified by one proven eight-limb multiplication, with the
proven Fermat inverse as fallback. The raw-limb twin lives in
`Montgomery/Native64x8InvDefs`.
-/

namespace Montgomery.Native64x8

/-- Splitting always produces 32-bit-bounded limbs. -/
theorem Limbs8.ofUInt256L_bounded (x : Native256.UInt256L) : (ofUInt256L x).Bounded := by
  have hand : ∀ y : UInt64, (y &&& 0xffffffff).toNat < 2 ^ 32 := fun y => by
    rw [UInt64.toNat_and, show ((0xffffffff : UInt64).toNat) = 2 ^ 32 - 1 from by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hshr : ∀ y : UInt64, (y >>> 32).toNat < 2 ^ 32 := fun y => by
    rw [UInt64.toNat_shiftRight, show ((32 : UInt64).toNat % 64) = 32 from by decide,
      Nat.shiftRight_eq_div_pow]
    have := y.toNat_lt
    omega
  exact ⟨hand _, hshr _, hand _, hshr _, hand _, hshr _, hand _, hshr _⟩

/-! ## Order from the borrow chain -/

/-- The final borrow decides the numeric order: `subBorrow a b = 1` iff `a < b`. -/
theorem subBorrow_eq_one_iff {a b : Limbs8} (ha : a.Bounded) (hb : b.Bounded) :
    subBorrow a b = 1 ↔ a.toNat < b.toNat := by
  obtain ⟨hbo, hchain⟩ := subLimbs_spec a b ha hb
  have hd := Limbs8.toNat_lt (subLimbs_bounded a b)
  rw [← UInt64.toNat_inj, show (1 : UInt64).toNat = 1 from rfl]
  omega

/-! ## Checked-candidate inversion -/

namespace FastField

variable {modulus : ℕ} [P : Mont64x8Field modulus]

/-- Accept a raw candidate `z` for `x⁻¹` if it verifies (bounded, canonical, `z · x = 1`
under the proven multiplier), else fall back to `x⁻¹`. -/
@[inline] def invWithCandidate (x : FastField modulus) (z : Limbs8) : FastField modulus :=
  if h : z.Bounded ∧ subBorrow z P.modulusLimbs = 1 ∧
      Native64x8.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus then
    ⟨z, h.1, by
      have hlt := (subBorrow_eq_one_iff h.1 P.modulusLimbs_bounded).mp h.2.1
      rwa [Mont64x8Field.q_toNat] at hlt⟩
  else x⁻¹

/-- A verified candidate is the field inverse. -/
theorem invWithCandidate_eq_inv (x : FastField modulus) (z : Limbs8) :
    invWithCandidate x z = x⁻¹ := by
  unfold invWithCandidate
  split
  case isTrue h =>
    refine eq_inv_of_mul_eq_one_left (Subtype.ext ?_)
    show Native64x8.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus
    exact h.2.2
  case isFalse _ => rfl

/-- Inversion via the shared binary-GCD candidate, verified by one eight-limb
multiplication; the fallback (`x = 0` or a candidate miss) is the proven Fermat inverse. -/
@[inline] def invGcd [Native256.Mont256Field modulus] (x : FastField modulus) :
    FastField modulus :=
  invWithCandidate x
    (Limbs8.ofUInt256L (Native256.gcdInvCandidate (modulus := modulus) x.val.toUInt256L))

/-- `invGcd` agrees with the Fermat inverse of the `Field` instance. -/
theorem invGcd_eq_inv [Native256.Mont256Field modulus] (x : FastField modulus) :
    invGcd x = x⁻¹ :=
  invWithCandidate_eq_inv x _

end FastField

end Montgomery.Native64x8
