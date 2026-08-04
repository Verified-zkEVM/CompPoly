/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native64x8Field
import CompPoly.Fields.Montgomery.Native64x8InvDefs
import Mathlib.Tactic.Ring

/-!
# Fast inversion for eight-limb Montgomery fields

The Pornin binary-GCD inverse for the eight-limb carrier: the raw candidate of
`Montgomery/Native64x8InvDefs`, accepted after one proven eight-limb multiplication, with
the proven Fermat inverse as fallback.  Also proves the divstep coefficient bound and that
the raw twin `invGcdRaw` agrees with `invGcd`.
-/

namespace Montgomery.Native256

/-! ## Divstep coefficient bounds -/

theorem gcdInner_zero (a b : UInt64) (f0 g0 f1 g1 : Int) :
    gcdInner 0 a b f0 g0 f1 g1 = (a, b, f0, g0, f1, g1) := rfl

/-- Unfolding of one divstep. -/
theorem gcdInner_succ (rounds : Nat) (a b : UInt64) (f0 g0 f1 g1 : Int) :
    gcdInner (rounds + 1) a b f0 g0 f1 g1 =
      if a &&& 1 == 0 then
        gcdInner rounds (a >>> 1) b f0 g0 (f1 * 2) (g1 * 2)
      else if a < b then
        gcdInner rounds ((b - a) >>> 1) a (f1 - f0) (g1 - g0) (f0 * 2) (g0 * 2)
      else
        gcdInner rounds ((a - b) >>> 1) b (f0 - f1) (g0 - g1) (f1 * 2) (g1 * 2) := by
  simp only [gcdInner]
  by_cases h1 : a &&& 1 == 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : a < b
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]

/-- Transition entries at most double per divstep. -/
theorem gcdInner_natAbs_le {rounds : Nat} {a b a' b' : UInt64}
    {f0 g0 f1 g1 f0' g0' f1' g1' : Int} {n : Nat}
    (h0 : f0.natAbs + g0.natAbs ≤ n) (h1 : f1.natAbs + g1.natAbs ≤ n)
    (heq : gcdInner rounds a b f0 g0 f1 g1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ rounds * n ∧
      f1'.natAbs + g1'.natAbs ≤ 2 ^ rounds * n := by
  induction rounds generalizing a b f0 g0 f1 g1 n with
  | zero =>
    rw [gcdInner_zero] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, -, rfl, rfl, rfl, rfl⟩ := heq
    rw [Nat.pow_zero, Nat.one_mul]
    exact ⟨h0, h1⟩
  | succ k ih =>
    have step : ∀ {A B : UInt64} {F0 G0 F1 G1 : Int},
        F0.natAbs + G0.natAbs ≤ 2 * n → F1.natAbs + G1.natAbs ≤ 2 * n →
        gcdInner k A B F0 G0 F1 G1 = (a', b', f0', g0', f1', g1') →
        f0'.natAbs + g0'.natAbs ≤ 2 ^ (k + 1) * n ∧
          f1'.natAbs + g1'.natAbs ≤ 2 ^ (k + 1) * n := by
      intro A B F0 G0 F1 G1 hF hG hEq
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact ih hF hG hEq
    rw [gcdInner_succ] at heq
    split at heq
    · exact step (by omega) (by omega) heq
    · split at heq
      · exact step (by omega) (by omega) heq
      · exact step (by omega) (by omega) heq

/-- Main-loop coefficients satisfy the linear-combination bound. -/
theorem gcdInner_31_natAbs_le {a b a' b' : UInt64} {f0' g0' f1' g1' : Int}
    (heq : gcdInner 31 a b 1 0 0 1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ 31 ∧ f1'.natAbs + g1'.natAbs ≤ 2 ^ 31 := by
  simpa using gcdInner_natAbs_le (n := 1) (by decide) (by decide) heq

/-- Final-fold coefficients stay word-sized. -/
theorem gcdInner_finalRounds_natAbs_le {modulus : Nat} [P : Mont256Field modulus]
    {a b a' b' : UInt64} {f0' g0' f1' g1' : Int}
    (heq : gcdInner P.gcdFinalRounds a b 1 0 0 1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ 62 ∧ f1'.natAbs + g1'.natAbs ≤ 2 ^ 62 := by
  have h := gcdInner_natAbs_le (n := 1) (by decide) (by decide) heq
  have hle : 2 ^ P.gcdFinalRounds ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by omega) P.gcdFinalRounds_le
  omega

end Montgomery.Native256

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

/-- Inversion via the binary-GCD candidate, verified by one eight-limb multiplication;
the fallback (`x = 0` or a candidate miss) is the proven Fermat inverse. -/
@[inline] def invGcd [Native256.Mont256Field modulus] (x : FastField modulus) :
    FastField modulus :=
  invWithCandidate x
    (Native64x8.gcdInvCandidate modulus P.modulusLimbs P.montgomeryNegInv x.val)

/-- `invGcd` agrees with the Fermat inverse of the `Field` instance. -/
theorem invGcd_eq_inv [Native256.Mont256Field modulus] (x : FastField modulus) :
    invGcd x = x⁻¹ :=
  invWithCandidate_eq_inv x _

end FastField

/-! ## Agreement of the raw twin -/

section RawTwin

variable {modulus : ℕ} [P : Mont64x8Field modulus]

private theorem toField_hpow (x : FastField modulus) (n : ℕ) :
    (x ^ n).toField = x.toField ^ n :=
  FastField.toField_pow x n

/-- `montPow` computes `acc · xⁿ`. -/
theorem montPow_eq_mul_pow (acc x : FastField modulus) (n : ℕ) :
    montPow P.modulusLimbs P.montgomeryNegInv acc.val x.val n = (acc * x ^ n).val := by
  induction n using Nat.strong_induction_on generalizing acc x with
  | _ n ih =>
    rw [montPow.eq_def]
    split
    next h =>
      subst h
      refine congrArg Subtype.val (FastField.toField_injective ?_)
      rw [FastField.toField_mul, toField_hpow, pow_zero, mul_one]
    next h =>
      have hlt : n / 2 < n := by omega
      by_cases hodd : n % 2 == 1
      · rw [if_pos hodd,
          show Native64x8.mul P.modulusLimbs P.montgomeryNegInv acc.val x.val
            = (acc * x).val from rfl,
          show Native64x8.mul P.modulusLimbs P.montgomeryNegInv x.val x.val
            = (x * x).val from rfl,
          ih _ hlt]
        simp only [beq_iff_eq] at hodd
        refine congrArg Subtype.val (FastField.toField_injective ?_)
        simp only [FastField.toField_mul, toField_hpow]
        conv_rhs => rw [show n = 2 * (n / 2) + 1 by omega]
        ring
      · rw [if_neg hodd,
          show Native64x8.mul P.modulusLimbs P.montgomeryNegInv x.val x.val
            = (x * x).val from rfl,
          ih _ hlt]
        simp only [beq_iff_eq] at hodd
        refine congrArg Subtype.val (FastField.toField_injective ?_)
        simp only [FastField.toField_mul, toField_hpow]
        conv_rhs => rw [show n = 2 * (n / 2) by omega]
        ring

/-- The `montPow` fallback computes the field inverse. -/
theorem montPow_eq_inv (x : FastField modulus) :
    montPow P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val (modulus - 2)
      = (x⁻¹).val := by
  rw [show P.rModModulus = (1 : FastField modulus).val from rfl, montPow_eq_mul_pow]
  have h1 : (1 : FastField modulus) * x ^ (modulus - 2) = x ^ (modulus - 2) :=
    FastField.toField_injective
      (by rw [FastField.toField_mul, FastField.toField_one, one_mul])
  exact congrArg Subtype.val (h1.trans rfl)

/-- The raw twin agrees with `invGcd`. -/
theorem invGcdRaw_eq_invGcd [Native256.Mont256Field modulus] (x : FastField modulus) :
    invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val
      = (FastField.invGcd x).val := by
  simp only [invGcdRaw, FastField.invGcd, FastField.invWithCandidate]
  split
  next h => rfl
  next h => exact montPow_eq_inv x

end RawTwin

end Montgomery.Native64x8
