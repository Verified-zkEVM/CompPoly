/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring

/-!
# Montgomery Reduction

Radix-generic specification and correctness lemmas for single-word Montgomery reduction.
Word-specific implementations refine these results in sibling modules.
-/

namespace Montgomery

/-- Natural-number Montgomery reduction used to specify the native-word reducer. -/
def reduceNat (R p negInv x : ℕ) : ℕ :=
  let m := (x % R * negInv) % R
  let u := (x + m * p) / R
  if u < p then u else u - p

/-- The quotient before the final conditional subtraction in Montgomery reduction. -/
def reduceNatQuotient (R p negInv x : ℕ) : ℕ :=
  let m := (x % R * negInv) % R
  (x + m * p) / R

/-- The pre-subtraction quotient is below twice the modulus. -/
theorem reduceNatQuotient_lt_two_mul (R p negInv x : ℕ)
    (hR : 0 < R) (hp : 0 < p) (hx : x < p * R) :
    reduceNatQuotient R p negInv x < 2 * p := by
  let m := x % R * negInv % R
  have hm_lt : m < R := Nat.mod_lt _ hR
  change (x + m * p) / R < 2 * p
  rw [Nat.div_lt_iff_lt_mul]
  · have hprod_lt : m * p < R * p := Nat.mul_lt_mul_of_pos_right hm_lt hp
    have hprod_lt' : m * p < p * R := by
      simpa only [Nat.mul_comm] using hprod_lt
    calc
      x + m * p < p * R + p * R := Nat.add_lt_add hx hprod_lt'
      _ = 2 * p * R := by ring
  · exact hR

/-- Montgomery reduction returns a canonical representative. -/
theorem reduceNat_lt (R p negInv x : ℕ)
    (hR : 0 < R) (hp : 0 < p) (hx : x < p * R) :
    reduceNat R p negInv x < p := by
  change (if reduceNatQuotient R p negInv x < p then
    reduceNatQuotient R p negInv x else reduceNatQuotient R p negInv x - p) < p
  have hu := reduceNatQuotient_lt_two_mul R p negInv x hR hp hx
  by_cases h : reduceNatQuotient R p negInv x < p
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    omega

/-- The Montgomery divisibility identity: if `(negInv * p) % R = R - 1` (i.e.
`negInv = -p⁻¹ mod R`), then `R ∣ x + ((x mod R)·negInv mod R)·p` for every `x`. -/
theorem dvd_add (R p negInv : ℕ) (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (x : ℕ) :
    R ∣ x + ((x % R * negInv) % R) * p := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.add_mod, Nat.mod_mul_mod (x % R * negInv) p R, Nat.mul_assoc]
  rw [← Nat.mul_mod_mod, hnegInv, Nat.add_mod_mod, add_comm, ← Nat.mul_add_one]
  rw [show R - 1 + 1 = R by omega, Nat.mul_mod_left]

/-- The pre-subtraction quotient represents multiplication by `R⁻¹` in `ZMod p`. -/
theorem reduceNatQuotient_cast (R p negInv : ℕ) [Fact (Nat.Prime p)] (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (hRne : (R : ZMod p) ≠ 0) (x : ℕ) :
    (reduceNatQuotient R p negInv x : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
  let m := x % R * negInv % R
  let u := (x + m * p) / R
  change (u : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹
  have hdiv : R ∣ x + m * p := by
    simpa [m] using dvd_add R p negInv hR hnegInv x
  have hu_mul : u * R = x + m * p := Nat.div_mul_cancel hdiv
  have hcast_mul : (u : ZMod p) * (R : ZMod p) = (x : ZMod p) := by
    rw [← Nat.cast_mul, hu_mul, Nat.cast_add, Nat.cast_mul]
    simp
  rw [← hcast_mul]
  exact (mul_inv_cancel_right₀ hRne (u : ZMod p)).symm

/-- Montgomery reduction represents multiplication by `R⁻¹` in `ZMod p`. -/
theorem reduceNat_cast (R p negInv : ℕ) [Fact (Nat.Prime p)] (hR : 0 < R)
    (hnegInv : negInv * p % R = R - 1) (hRne : (R : ZMod p) ≠ 0) (x : ℕ) :
    (reduceNat R p negInv x : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
  let m := x % R * negInv % R
  let u := (x + m * p) / R
  have hu_cast : (u : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
    simpa only [reduceNatQuotient, m, u] using
      reduceNatQuotient_cast R p negInv hR hnegInv hRne x
  change ((if u < p then u else u - p : ℕ) : ZMod p) =
    (x : ZMod p) * (R : ZMod p)⁻¹
  by_cases hu : u < p
  · rw [if_pos hu]
    exact hu_cast
  · have hfield : ((u - p : ℕ) : ZMod p) = (u : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    rw [if_neg hu]
    rw [hfield]
    exact hu_cast

/-- Two naturals below `p` are equal once their `ZMod p` casts agree. -/
theorem natCast_inj_of_lt {p a b : ℕ} (h : (a : ZMod p) = (b : ZMod p))
    (ha : a < p) (hb : b < p) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

end Montgomery
