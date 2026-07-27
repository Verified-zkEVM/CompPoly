/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Impl
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Direct Binary-Extension Irreducibility And Primitive-Order Helpers

Reusable proof helpers for the concrete `GF(2^48)` and `GF(2^72)` certificate
files. The concrete modules still need generated modular-power and gcd
certificates; this file supplies the small field-theoretic shell those
certificates plug into.
-/

namespace BinaryField

namespace Extension

open Polynomial

namespace Concrete

variable (params : ExecutableParams)

/-- Natural-number encoding of executable multiplication modulo the defining polynomial. -/
def mulNat (x y : Nat) : Nat :=
  reduceNat params (clMulNat x y params.degree)

/-- Natural-number encoding of executable squaring modulo the defining polynomial. -/
def squareNat (x : Nat) : Nat :=
  mulNat params x x

/-- Raw bit-pattern construction preserves bounded natural encodings. -/
theorem toNat_ofNat_of_lt {n : Nat} (hn : n < 2 ^ params.degree) :
    toNat params (ofNat params n) = n := by
  simp [toNat, toBitVec, ofNat, ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- A bounded raw bit-pattern different from `1` is not executable one. -/
theorem ofNat_ne_one_of_lt {n : Nat} (hDegree_pos : 0 < params.degree)
    (hn : n < 2 ^ params.degree) (hne : n ≠ 1) :
    ofNat params n ≠ one params := by
  intro h
  have hnat := congrArg (toNat params) h
  rw [toNat_ofNat_of_lt params hn] at hnat
  have hone : toNat params (one params) = 1 := by
    unfold one
    exact toNat_ofNat_of_lt params (n := 1) (Nat.one_lt_two_pow hDegree_pos.ne')
  rw [hone] at hnat
  exact hne hnat

/-- Nat-level modular multiplication returns a bounded residue. -/
theorem mulNat_lt_two_pow (x y : Nat) :
    mulNat params x y < 2 ^ params.degree := by
  unfold mulNat reduceNat
  exact Nat.mod_lt _ (pow_pos (by norm_num : 0 < 2) params.degree)

/-- Executable multiplication agrees with Nat-level modular multiplication on bounded inputs. -/
theorem mul_ofNat_of_lt {x y : Nat} (hx : x < 2 ^ params.degree)
    (hy : y < 2 ^ params.degree) :
    mul params (ofNat params x) (ofNat params y) = ofNat params (mulNat params x y) := by
  unfold mul mulNat reduce
  rw [toNat_ofNat_of_lt params hx, toNat_ofNat_of_lt params hy]

/-- Executable squaring agrees with Nat-level modular squaring on bounded inputs. -/
theorem square_ofNat_of_lt {x : Nat} (hx : x < 2 ^ params.degree) :
    square params (ofNat params x) = ofNat params (squareNat params x) := by
  unfold square squareNat
  exact mul_ofNat_of_lt params hx hx

/--
Consume a structurally checked power chain.

Each subsequent `(exponent, residue)` entry must use the previous exponent as
`exponent / 2` and the previous residue as the halving-recursion result for
`Concrete.pow`.
-/
def consumePowNatChain (a : Nat) :
    Nat → Nat → List (Nat × Nat) → Option (Nat × Nat)
  | prevExponent, prevResidue, [] => some (prevExponent, prevResidue)
  | prevExponent, prevResidue, (exponent, residue) :: rest =>
      if exponent == 0 then
        none
      else if prevExponent == exponent / 2 then
        let halfSq := squareNat params prevResidue
        let expected :=
          if exponent % 2 = 0 then halfSq else mulNat params halfSq a
        if residue == expected then
          consumePowNatChain a exponent expected rest
        else
          none
      else
        none

/-- Check a structurally encoded Nat-level power chain. -/
def checkPowNatChain (a target : Nat) (cert : List (Nat × Nat)) (expected : Nat) : Bool :=
  match cert with
  | [] => false
  | (startExponent, startResidue) :: rest =>
      if startExponent == 0 then
        if startResidue == 1 then
          match consumePowNatChain params a 0 1 rest with
          | some (lastExponent, lastResidue) =>
              if lastExponent == target then
                if lastResidue == expected then true else false
              else
                false
          | none => false
        else
          false
      else
        false

/-- A consumed structural power chain evaluates to the existing `Concrete.pow`. -/
theorem consumePowNatChain_correct {a : Nat} (ha : a < 2 ^ params.degree) :
    ∀ cert prevExponent prevResidue lastExponent lastResidue,
      pow params (ofNat params a) prevExponent = ofNat params prevResidue →
        prevResidue < 2 ^ params.degree →
        consumePowNatChain params a prevExponent prevResidue cert =
          some (lastExponent, lastResidue) →
        pow params (ofNat params a) lastExponent = ofNat params lastResidue ∧
          lastResidue < 2 ^ params.degree := by
  intro cert
  induction cert with
  | nil =>
      intro prevExponent prevResidue lastExponent lastResidue hprev hprevBound hchain
      simp [consumePowNatChain] at hchain
      rcases hchain with ⟨rfl, rfl⟩
      exact ⟨hprev, hprevBound⟩
  | cons step rest ih =>
      intro prevExponent prevResidue lastExponent lastResidue hprev hprevBound hchain
      rcases step with ⟨exponent, residue⟩
      simp only [consumePowNatChain] at hchain
      by_cases hzero : exponent == 0
      · simp [hzero] at hchain
      · simp [hzero] at hchain
        let halfSq := squareNat params prevResidue
        let expected :=
          if exponent % 2 = 0 then halfSq else mulNat params halfSq a
        have hhalfEq : prevExponent = exponent / 2 := hchain.1
        have hchainRest :
            consumePowNatChain params a exponent expected rest =
              some (lastExponent, lastResidue) := by
          simpa [expected, halfSq] using hchain.2.2
        cases exponent with
        | zero =>
            simp at hzero
        | succ exponent' =>
            have hpowCurrent :
                pow params (ofNat params a) (exponent' + 1) =
                  ofNat params expected := by
              rw [pow]
              rw [← hhalfEq, hprev]
              by_cases heven : (exponent' + 1) % 2 = 0
              · simp [expected, halfSq, heven,
                  square_ofNat_of_lt params hprevBound]
              · have hhalfSqBound :
                    squareNat params prevResidue < 2 ^ params.degree :=
                  mulNat_lt_two_pow params prevResidue prevResidue
                rw [square_ofNat_of_lt params hprevBound]
                simp only [heven, ↓reduceIte]
                rw [mul_ofNat_of_lt params hhalfSqBound ha]
                simp [expected, halfSq, squareNat, heven]
            have hboundCurrent :
                expected < 2 ^ params.degree := by
              by_cases heven : (exponent' + 1) % 2 = 0
              · simp [expected, halfSq, heven]
                exact mulNat_lt_two_pow params prevResidue prevResidue
              · simp [expected, halfSq, heven]
                exact mulNat_lt_two_pow params (squareNat params prevResidue) a
            exact ih (exponent' + 1) expected lastExponent lastResidue
              hpowCurrent hboundCurrent hchainRest

/-- A checked structural power chain proves the requested power residue. -/
theorem pow_eq_of_checkPowNatChain {a target : Nat} {cert : List (Nat × Nat)}
    {expected : Nat} (hDegree_pos : 0 < params.degree) (ha : a < 2 ^ params.degree)
    (hcert : checkPowNatChain params a target cert expected = true) :
    pow params (ofNat params a) target = ofNat params expected ∧
      expected < 2 ^ params.degree := by
  unfold checkPowNatChain at hcert
  cases cert with
  | nil =>
      simp at hcert
  | cons start rest =>
      rcases start with ⟨startExponent, startResidue⟩
      by_cases hstartExp : startExponent == 0
      · simp [hstartExp] at hcert
        cases hconsume : consumePowNatChain params a 0 1 rest with
        | none =>
            simp [hconsume] at hcert
        | some last =>
            rcases last with ⟨lastExponent, lastResidue⟩
            simp [hconsume] at hcert
            have hlastExp : lastExponent = target := hcert.2.1
            have hlastResidue : lastResidue = expected := hcert.2.2
            have hchain :=
              consumePowNatChain_correct params ha rest
                0 1 lastExponent lastResidue
                (by simp [pow, one])
                (Nat.one_lt_two_pow hDegree_pos.ne')
                hconsume
            rw [← hlastExp, ← hlastResidue]
            exact hchain
      · simp [hstartExp] at hcert

end Concrete

noncomputable section

/-- A reducible degree-`n` polynomial has an irreducible factor of degree at most `n / 2`. -/
lemma exists_irreducible_factor_le_half_of_reducible {R : Type*} [Field R]
    (P : Polynomial R) {n : Nat} (h_pos : 0 < n) (h_deg : P.natDegree = n)
    (h_red : ¬ Irreducible P) :
    ∃ q, Irreducible q ∧ q ∣ P ∧ 2 * q.natDegree ≤ n := by
  have h_not_unit : ¬ IsUnit P := by
    by_contra h_unit
    rw [Polynomial.isUnit_iff_degree_eq_zero] at h_unit
    have h_ne_zero : P ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.natDegree_zero] at h_deg
      omega
    have h_natDeg_zero : P.natDegree = 0 :=
      (Polynomial.degree_eq_iff_natDegree_eq h_ne_zero).mp h_unit
    omega
  have h_exists_split : ∃ a b, P = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    rw [irreducible_iff, not_and_or, not_forall] at h_red
    simp only [h_not_unit, not_false_eq_true] at h_red
    push Not at h_red
    simp only [IsEmpty.exists_iff, false_or] at h_red
    rcases h_red with ⟨a, b, h_eq, h_non_units⟩
    exact ⟨a, b, h_eq, h_non_units⟩
  rcases h_exists_split with ⟨a, b, h_eq, ha_nonunit, hb_nonunit⟩
  have h_a_ne_zero : a ≠ 0 := by
    intro ha_zero
    rw [h_eq, ha_zero, zero_mul, Polynomial.natDegree_zero] at h_deg
    omega
  have h_b_ne_zero : b ≠ 0 := by
    intro hb_zero
    rw [h_eq, hb_zero, mul_zero, Polynomial.natDegree_zero] at h_deg
    omega
  have h_deg_sum : a.natDegree + b.natDegree = n := by
    rw [← h_deg, h_eq]
    exact (Polynomial.natDegree_mul (hp := h_a_ne_zero) (hq := h_b_ne_zero)).symm
  by_cases h_le : a.natDegree ≤ b.natDegree
  · have h_a_half : 2 * a.natDegree ≤ n := by omega
    obtain ⟨q, hq_irr, hq_dvd_a⟩ :=
      WfDvdMonoid.exists_irreducible_factor ha_nonunit h_a_ne_zero
    refine ⟨q, hq_irr, dvd_trans hq_dvd_a (Dvd.intro b h_eq.symm), ?_⟩
    have hq_le_a : q.natDegree ≤ a.natDegree :=
      Polynomial.natDegree_le_of_dvd hq_dvd_a h_a_ne_zero
    omega
  · have h_b_half : 2 * b.natDegree ≤ n := by omega
    obtain ⟨q, hq_irr, hq_dvd_b⟩ :=
      WfDvdMonoid.exists_irreducible_factor hb_nonunit h_b_ne_zero
    refine ⟨q, hq_irr, dvd_trans hq_dvd_b (Dvd.intro_left a h_eq.symm), ?_⟩
    have hq_le_b : q.natDegree ≤ b.natDegree :=
      Polynomial.natDegree_le_of_dvd hq_dvd_b h_b_ne_zero
    omega

private lemma dvd_32_of_dvd_32_le_half {d : Nat} (hdvd : d ∣ 32) (hle : 2 * d ≤ 32) :
    d ∣ 16 := by
  rcases hdvd with ⟨k, hk⟩
  have hdle : d ≤ 16 := by omega
  interval_cases d
  all_goals omega

private lemma dvd_48_of_dvd_48_le_half {d : Nat} (hdvd : d ∣ 48) (hle : 2 * d ≤ 48) :
    d ∣ 24 ∨ d ∣ 16 := by
  rcases hdvd with ⟨k, hk⟩
  have hdle : d ≤ 24 := by omega
  interval_cases d
  all_goals omega

private lemma dvd_64_of_dvd_64_le_half {d : Nat} (hdvd : d ∣ 64) (hle : 2 * d ≤ 64) :
    d ∣ 32 := by
  rcases hdvd with ⟨k, hk⟩
  have hdle : d ≤ 32 := by omega
  interval_cases d
  all_goals omega

private lemma dvd_72_of_dvd_72_le_half {d : Nat} (hdvd : d ∣ 72) (hle : 2 * d ≤ 72) :
    d ∣ 36 ∨ d ∣ 24 := by
  rcases hdvd with ⟨k, hk⟩
  have hdle : d ≤ 36 := by omega
  interval_cases d
  all_goals omega

/--
Rabin irreducibility test specialized to degree `32` over `GF(2)`.

The concrete certificate files provide the divisibility check
`P ∣ X^(2^32) - X` and the gcd check for the only prime factor `2` of
`32`.
-/
lemma irreducible_of_rabin_32_passed_over_GF2 (P : Polynomial (ZMod 2))
    (h_deg : P.natDegree = 32)
    (h_trace : P ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 32) + X))
    (h_gcd16 :
      EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 16) + X) P = 1) :
    Irreducible P := by
  have h_ringCharZmod2 : ringChar (ZMod 2) = 2 := by
    exact ZMod.ringChar_zmod_n 2
  letI : Fact (Nat.Prime (ringChar (ZMod 2))) := by
    exact Fact.mk (by
      rw [h_ringCharZmod2]
      exact Nat.prime_two)
  by_contra h_red
  rcases exists_irreducible_factor_le_half_of_reducible
      P (by norm_num : 0 < 32) h_deg h_red with
    ⟨q, hq_irr, hq_dvd_P, hq_half⟩
  have hq_dvd_trace : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 32) + X) :=
    dvd_trans hq_dvd_P h_trace
  have h_sub_eq := CharTwo.sub_eq_add ((X : Polynomial (ZMod 2)) ^ 2 ^ 32) X
  simp only [← h_sub_eq] at hq_dvd_trace
  have h_deg_dvd_32 : q.natDegree ∣ 32 := by
    apply Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
      (R := ZMod 2) (n := 32) (q := q) (hq_irr := hq_irr).mp
    rw [ZMod.card]
    exact hq_dvd_trace
  have h_dvd16 := dvd_32_of_dvd_32_le_half h_deg_dvd_32 hq_half
  have hq_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 16) - X) := by
    have hres :=
      Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
        (R := ZMod 2) (n := 16) (q := q) (hq_irr := hq_irr).mpr h_dvd16
    rw [ZMod.card] at hres
    exact hres
  rw [CharTwo.sub_eq_add] at hq_dvd_check
  have hq_dvd_gcd :
      q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 16) + X) P :=
    EuclideanDomain.dvd_gcd (by convert hq_dvd_check) hq_dvd_P
  rw [h_gcd16] at hq_dvd_gcd
  exact (irreducible_iff.mp hq_irr).1 (isUnit_of_dvd_one hq_dvd_gcd)

/--
Rabin irreducibility test specialized to degree `48` over `GF(2)`.

The concrete certificate files provide the divisibility check
`P ∣ X^(2^48) - X` and the two gcd checks for prime factors `2` and `3` of
`48`.
-/
lemma irreducible_of_rabin_48_passed_over_GF2 (P : Polynomial (ZMod 2))
    (h_deg : P.natDegree = 48)
    (h_trace : P ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 48) + X))
    (h_gcd24 :
      EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 24) + X) P = 1)
    (h_gcd16 :
      EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 16) + X) P = 1) :
    Irreducible P := by
  have h_ringCharZmod2 : ringChar (ZMod 2) = 2 := by
    exact ZMod.ringChar_zmod_n 2
  letI : Fact (Nat.Prime (ringChar (ZMod 2))) := by
    exact Fact.mk (by
      rw [h_ringCharZmod2]
      exact Nat.prime_two)
  by_contra h_red
  rcases exists_irreducible_factor_le_half_of_reducible
      P (by norm_num : 0 < 48) h_deg h_red with
    ⟨q, hq_irr, hq_dvd_P, hq_half⟩
  have hq_dvd_trace : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 48) + X) :=
    dvd_trans hq_dvd_P h_trace
  have h_sub_eq := CharTwo.sub_eq_add ((X : Polynomial (ZMod 2)) ^ 2 ^ 48) X
  simp only [← h_sub_eq] at hq_dvd_trace
  have h_deg_dvd_48 : q.natDegree ∣ 48 := by
    apply Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
      (R := ZMod 2) (n := 48) (q := q) (hq_irr := hq_irr).mp
    rw [ZMod.card]
    exact hq_dvd_trace
  rcases dvd_48_of_dvd_48_le_half h_deg_dvd_48 hq_half with h_dvd24 | h_dvd16
  · have hq_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 24) - X) := by
      have hres :=
        Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
          (R := ZMod 2) (n := 24) (q := q) (hq_irr := hq_irr).mpr h_dvd24
      rw [ZMod.card] at hres
      exact hres
    rw [CharTwo.sub_eq_add] at hq_dvd_check
    have hq_dvd_gcd :
        q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 24) + X) P :=
      EuclideanDomain.dvd_gcd (by convert hq_dvd_check) hq_dvd_P
    rw [h_gcd24] at hq_dvd_gcd
    exact (irreducible_iff.mp hq_irr).1 (isUnit_of_dvd_one hq_dvd_gcd)
  · have hq_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 16) - X) := by
      have hres :=
        Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
          (R := ZMod 2) (n := 16) (q := q) (hq_irr := hq_irr).mpr h_dvd16
      rw [ZMod.card] at hres
      exact hres
    rw [CharTwo.sub_eq_add] at hq_dvd_check
    have hq_dvd_gcd :
        q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 16) + X) P :=
      EuclideanDomain.dvd_gcd (by convert hq_dvd_check) hq_dvd_P
    rw [h_gcd16] at hq_dvd_gcd
    exact (irreducible_iff.mp hq_irr).1 (isUnit_of_dvd_one hq_dvd_gcd)

/--
Rabin irreducibility test specialized to degree `64` over `GF(2)`.

The concrete certificate files provide the divisibility check
`P ∣ X^(2^64) - X` and the gcd check for the only prime factor `2` of
`64`.
-/
lemma irreducible_of_rabin_64_passed_over_GF2 (P : Polynomial (ZMod 2))
    (h_deg : P.natDegree = 64)
    (h_trace : P ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 64) + X))
    (h_gcd32 :
      EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 32) + X) P = 1) :
    Irreducible P := by
  have h_ringCharZmod2 : ringChar (ZMod 2) = 2 := by
    exact ZMod.ringChar_zmod_n 2
  letI : Fact (Nat.Prime (ringChar (ZMod 2))) := by
    exact Fact.mk (by
      rw [h_ringCharZmod2]
      exact Nat.prime_two)
  by_contra h_red
  rcases exists_irreducible_factor_le_half_of_reducible
      P (by norm_num : 0 < 64) h_deg h_red with
    ⟨q, hq_irr, hq_dvd_P, hq_half⟩
  have hq_dvd_trace : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 64) + X) :=
    dvd_trans hq_dvd_P h_trace
  have h_sub_eq := CharTwo.sub_eq_add ((X : Polynomial (ZMod 2)) ^ 2 ^ 64) X
  simp only [← h_sub_eq] at hq_dvd_trace
  have h_deg_dvd_64 : q.natDegree ∣ 64 := by
    apply Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
      (R := ZMod 2) (n := 64) (q := q) (hq_irr := hq_irr).mp
    rw [ZMod.card]
    exact hq_dvd_trace
  have h_dvd32 := dvd_64_of_dvd_64_le_half h_deg_dvd_64 hq_half
  have hq_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 32) - X) := by
    have hres :=
      Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
        (R := ZMod 2) (n := 32) (q := q) (hq_irr := hq_irr).mpr h_dvd32
    rw [ZMod.card] at hres
    exact hres
  rw [CharTwo.sub_eq_add] at hq_dvd_check
  have hq_dvd_gcd :
      q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 32) + X) P :=
    EuclideanDomain.dvd_gcd (by convert hq_dvd_check) hq_dvd_P
  rw [h_gcd32] at hq_dvd_gcd
  exact (irreducible_iff.mp hq_irr).1 (isUnit_of_dvd_one hq_dvd_gcd)

/--
Rabin irreducibility test specialized to degree `72` over `GF(2)`.

The concrete certificate files provide the divisibility check
`P ∣ X^(2^72) - X` and the two gcd checks for prime factors `2` and `3` of
`72`.
-/
lemma irreducible_of_rabin_72_passed_over_GF2 (P : Polynomial (ZMod 2))
    (h_deg : P.natDegree = 72)
    (h_trace : P ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 72) + X))
    (h_gcd36 :
      EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 36) + X) P = 1)
    (h_gcd24 :
      EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 24) + X) P = 1) :
    Irreducible P := by
  have h_ringCharZmod2 : ringChar (ZMod 2) = 2 := by
    exact ZMod.ringChar_zmod_n 2
  letI : Fact (Nat.Prime (ringChar (ZMod 2))) := by
    exact Fact.mk (by
      rw [h_ringCharZmod2]
      exact Nat.prime_two)
  by_contra h_red
  rcases exists_irreducible_factor_le_half_of_reducible
      P (by norm_num : 0 < 72) h_deg h_red with
    ⟨q, hq_irr, hq_dvd_P, hq_half⟩
  have hq_dvd_trace : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 72) + X) :=
    dvd_trans hq_dvd_P h_trace
  have h_sub_eq := CharTwo.sub_eq_add ((X : Polynomial (ZMod 2)) ^ 2 ^ 72) X
  simp only [← h_sub_eq] at hq_dvd_trace
  have h_deg_dvd_72 : q.natDegree ∣ 72 := by
    apply Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
      (R := ZMod 2) (n := 72) (q := q) (hq_irr := hq_irr).mp
    rw [ZMod.card]
    exact hq_dvd_trace
  rcases dvd_72_of_dvd_72_le_half h_deg_dvd_72 hq_half with h_dvd36 | h_dvd24
  · have hq_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 36) - X) := by
      have hres :=
        Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
          (R := ZMod 2) (n := 36) (q := q) (hq_irr := hq_irr).mpr h_dvd36
      rw [ZMod.card] at hres
      exact hres
    rw [CharTwo.sub_eq_add] at hq_dvd_check
    have hq_dvd_gcd :
        q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 36) + X) P :=
      EuclideanDomain.dvd_gcd (by convert hq_dvd_check) hq_dvd_P
    rw [h_gcd36] at hq_dvd_gcd
    exact (irreducible_iff.mp hq_irr).1 (isUnit_of_dvd_one hq_dvd_gcd)
  · have hq_dvd_check : q ∣ ((X : Polynomial (ZMod 2)) ^ (2 ^ 24) - X) := by
      have hres :=
        Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd
          (R := ZMod 2) (n := 24) (q := q) (hq_irr := hq_irr).mpr h_dvd24
      rw [ZMod.card] at hres
      exact hres
    rw [CharTwo.sub_eq_add] at hq_dvd_check
    have hq_dvd_gcd :
        q ∣ EuclideanDomain.gcd ((X : Polynomial (ZMod 2)) ^ (2 ^ 24) + X) P :=
      EuclideanDomain.dvd_gcd (by convert hq_dvd_check) hq_dvd_P
    rw [h_gcd24] at hq_dvd_gcd
    exact (irreducible_iff.mp hq_irr).1 (isUnit_of_dvd_one hq_dvd_gcd)

end

end Extension

end BinaryField
