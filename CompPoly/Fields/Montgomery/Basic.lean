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
# Montgomery Reduction — radix-generic core

Field-agnostic number theory behind native-word Montgomery reduction, shared by every
fast prime field. Everything here is parameterized by an abstract radix `R : Nat` (the
Montgomery modulus, e.g. `2^32` for 32-bit-word fields) and the prime `p`; the proofs use
only that `gcd(R, p) = 1` — supplied as the congruence `negInv * p ≡ R - 1 [MOD R]` — and
that `0 < R`, so nothing here is tied to a particular word size.

The concrete word-level bridges (e.g. the `UInt32 × UInt64`, `R = 2^32` reduction) live in
sibling modules such as `CompPoly.Fields.Montgomery.Native32`, which instantiate `R` and
call into this core. These lemmas are all `Prop`/spec level and erased at codegen, so
sharing them carries no runtime cost.
-/

namespace Montgomery

/-- The Montgomery divisibility identity: if `negInv * p ≡ R - 1 [MOD R]` (i.e.
`negInv = -p⁻¹ mod R`), then `R ∣ x + ((x mod R)·negInv mod R)·p` for every `x`. This is
what makes Montgomery reduction integer-valued. -/
theorem sum_dvd (R p negInv : Nat) (hR : 0 < R)
    (hp : negInv * p ≡ R - 1 [MOD R]) (x : Nat) :
    R ∣ x + ((x % R * negInv) % R) * p := by
  rw [← Nat.modEq_zero_iff_dvd]
  have hx : x ≡ x % R [MOD R] := (Nat.mod_modEq x R).symm
  have hm :
      ((x % R * negInv) % R) * p ≡ (x % R) * (R - 1) [MOD R] := by
    have hmi :
        (x % R * negInv) % R ≡ x % R * negInv [MOD R] := Nat.mod_modEq _ _
    calc
      ((x % R * negInv) % R) * p
          ≡ (x % R * negInv) * p [MOD R] := hmi.mul_right _
      _ = x % R * (negInv * p) := by ring
      _ ≡ x % R * (R - 1) [MOD R] := hp.mul_left _
  calc
    x + ((x % R * negInv) % R) * p
        ≡ x % R + x % R * (R - 1) [MOD R] := hx.add hm
    _ = x % R * R := by
      rw [add_comm, ← Nat.mul_succ]
      have hsucc : (R - 1).succ = R := by omega
      rw [hsucc]
    _ ≡ 0 [MOD R] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact ⟨x % R, by rw [mul_comm]⟩

/-- Nat-level Montgomery reduction: specifies and is used to prove the native-word reducer. -/
def reduceNat (R p negInv x : Nat) : Nat :=
  let m := (x % R * negInv) % R
  let u := (x + m * p) / R
  if u < p then u else u - p

/-- Montgomery reduction descends to "multiply by `R⁻¹`" in `ZMod p`. -/
theorem reduceNat_cast (R p negInv : Nat) [Fact (Nat.Prime p)] (hR : 0 < R)
    (hp : negInv * p ≡ R - 1 [MOD R]) (hRne : (R : ZMod p) ≠ 0) (x : Nat) :
    (reduceNat R p negInv x : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
  let m := x % R * negInv % R
  let u := (x + m * p) / R
  have hdiv : R ∣ x + m * p := by
    simpa [m] using sum_dvd R p negInv hR hp x
  have hu_mul : u * R = x + m * p := Nat.div_mul_cancel hdiv
  have hcast_mul : (u : ZMod p) * (R : ZMod p) = (x : ZMod p) := by
    rw [← Nat.cast_mul, hu_mul, Nat.cast_add, Nat.cast_mul]
    simp
  by_cases hu : u < p
  · have hmain : (u : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
      rw [← hcast_mul]
      refine (mul_inv_cancel_right₀ ?_ (u : ZMod p)).symm
      exact hRne
    dsimp only [reduceNat]
    rw [if_pos hu]
    exact hmain
  · have hfield : ((u - p : Nat) : ZMod p) = (u : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    have hmain : ((u - p : Nat) : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
      rw [hfield, ← hcast_mul]
      refine (mul_inv_cancel_right₀ ?_ (u : ZMod p)).symm
      exact hRne
    dsimp only [reduceNat]
    rw [if_neg hu]
    exact hmain

/-- The pre-conditional-subtract Montgomery quotient already casts to "multiply by `R⁻¹`"
in `ZMod p`. -/
theorem quotient_cast (R p negInv : Nat) [Fact (Nat.Prime p)] (hR : 0 < R)
    (hp : negInv * p ≡ R - 1 [MOD R]) (hRne : (R : ZMod p) ≠ 0) (x : Nat) :
    (let m := x % R * negInv % R
     let u := (x + m * p) / R
     (u : ZMod p)) = (x : ZMod p) * (R : ZMod p)⁻¹ := by
  let m := x % R * negInv % R
  let u := (x + m * p) / R
  have hmr := reduceNat_cast R p negInv hR hp hRne x
  unfold reduceNat at hmr
  change (u : ZMod p) = (x : ZMod p) * (R : ZMod p)⁻¹
  by_cases hu : u < p
  · simpa only [m, u, hu, if_true] using hmr
  · have hfield : ((u - p : Nat) : ZMod p) = (u : ZMod p) := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hu)]
      simp
    rw [← hfield]
    simpa only [m, u, hu, if_false] using hmr

/-- Two naturals below `p` are equal once their `ZMod p` casts agree. -/
theorem natCast_inj {p a b : Nat} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact Nat.ModEq.eq_of_lt_of_lt h ha hb

end Montgomery
