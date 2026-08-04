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

Correctness of the checked inversion of `Montgomery/Native64x8InvDefs`: `invGcdRaw`
computes the field inverse and `FastField.invGcd` is its proof-carrying wrapper.  Also
proves the divstep coefficient bound.
-/

namespace Montgomery.Native64x8

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

/-- Chunks of at most 31 divsteps satisfy the linear-combination bound. -/
theorem gcdInner_natAbs_le_31 {rounds : Nat} (h31 : rounds ≤ 31) {a b a' b' : UInt64}
    {f0' g0' f1' g1' : Int}
    (heq : gcdInner rounds a b 1 0 0 1 = (a', b', f0', g0', f1', g1')) :
    f0'.natAbs + g0'.natAbs ≤ 2 ^ 31 ∧ f1'.natAbs + g1'.natAbs ≤ 2 ^ 31 := by
  have h := gcdInner_natAbs_le (n := 1) (by decide) (by decide) heq
  have hle : 2 ^ rounds ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) h31
  omega

/-! ## Order from the borrow chain -/

/-- The final borrow decides the numeric order. -/
theorem subBorrow_eq_one_iff {a b : Limbs8} (ha : a.Bounded) (hb : b.Bounded) :
    subBorrow a b = 1 ↔ a.toNat < b.toNat := by
  obtain ⟨hbo, hchain⟩ := subLimbs_spec a b ha hb
  have hd := Limbs8.toNat_lt (subLimbs_bounded a b)
  rw [← UInt64.toNat_inj, show (1 : UInt64).toNat = 1 from rfl]
  omega

/-! ## The Fermat fallback and the checked raw inversion -/

section

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

/-- Accept a raw candidate `z` for `x⁻¹` if it verifies, else fall back to `x⁻¹`. -/
private def invWithCandidate (x : FastField modulus) (z : Limbs8) : FastField modulus :=
  if h : z.Bounded ∧ subBorrow z P.modulusLimbs = 1 ∧
      Native64x8.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus then
    ⟨z, h.1, by
      have hlt := (subBorrow_eq_one_iff h.1 P.modulusLimbs_bounded).mp h.2.1
      rwa [Mont64x8Field.q_toNat] at hlt⟩
  else x⁻¹

private theorem invWithCandidate_eq_inv (x : FastField modulus) (z : Limbs8) :
    invWithCandidate x z = x⁻¹ := by
  unfold invWithCandidate
  split
  case isTrue h =>
    refine eq_inv_of_mul_eq_one_left (Subtype.ext ?_)
    show Native64x8.mul P.modulusLimbs P.montgomeryNegInv z x.val = P.rModModulus
    exact h.2.2
  case isFalse _ => rfl

/-- `invGcdRaw` computes the field inverse. -/
theorem invGcdRaw_eq_inv [GcdData modulus] (x : FastField modulus) :
    invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val
      = (x⁻¹).val := by
  have hval : invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val
      = (invWithCandidate x
          (gcdInvCandidate modulus P.modulusLimbs P.montgomeryNegInv x.val)).val := by
    simp only [invGcdRaw, invWithCandidate]
    split
    next h => rfl
    next h => exact montPow_eq_inv x
  rw [hval, invWithCandidate_eq_inv]

end

/-! ## The proof-carrying wrapper -/

namespace FastField

variable {modulus : ℕ} [P : Mont64x8Field modulus]

/-- The proof-carrying wrapper of the checked inversion `invGcdRaw`. -/
@[inline] def invGcd [GcdData modulus] (x : FastField modulus) : FastField modulus :=
  ⟨invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val, by
    rw [invGcdRaw_eq_inv x]
    exact (x⁻¹).property⟩

/-- `invGcd` agrees with the `Field` inverse. -/
theorem invGcd_eq_inv [GcdData modulus] (x : FastField modulus) :
    invGcd x = x⁻¹ := by
  have hval : (invGcd x).val
      = invGcdRaw modulus P.modulusLimbs P.montgomeryNegInv P.rModModulus x.val := by
    simp only [invGcd]
  exact Subtype.ext (hval.trans (invGcdRaw_eq_inv x))

end FastField

end Montgomery.Native64x8
