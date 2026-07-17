/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256.UInt256L
import CompPoly.Fields.Montgomery.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Native 256-bit Montgomery Fields

The `Mont256Field` data class, the bounded `FastField` carrier, and the proven CIOS
Montgomery reduction and multiplication with radix `2 ^ 256` (four 64-bit limbs).
-/

set_option maxRecDepth 4000

namespace Montgomery
namespace Native256

/-- Per-field data for a fast 256-bit Montgomery field. The word constants and the GCD
divstep schedule are the only runtime data; every proof obligation defaults to `decide`. -/
class Mont256Field (modulus : ℕ) where
  /-- `modulus` is prime. -/
  prime : modulus.Prime
  /-- `modulus` as a 256-bit word. -/
  modulus256 : UInt256L
  /-- `-modulus⁻¹ mod 2^64`, the per-limb multiplier for interleaved Montgomery reduction. -/
  montgomeryNegInv : UInt64
  /-- `2^256 mod modulus`, the Montgomery representation of one. -/
  rModModulus : UInt256L
  /-- `(2^256)^2 mod modulus`, used to enter Montgomery form. -/
  r2ModModulus : UInt256L
  /-- Divsteps in the final word-sized round of the Pornin binary-GCD inversion:
  `2·bits(p) - 2 - 15·31`, so the total divstep count is the worst-case bound `2·bits(p) - 2`
  (each divstep shrinks `len(a) + len(b) ≤ 2·bits(p)` by at least one). Must stay `≤ 62` so the
  final transition-matrix entries fit in a signed word. -/
  gcdFinalRounds : ℕ
  /-- Initial `u` for the Pornin binary-GCD inversion: `2^(1071 - gcdFinalRounds) mod modulus`.
  The exponent is `512 - T + 16·64` for `T = 15·31 + gcdFinalRounds` total divsteps: `2^512`
  turns the Montgomery input `x·R` into the Montgomery output `x⁻¹·R`, `2^(-T)` cancels the
  per-divstep doubling of the transition factors, and `2^(16·64)` cancels the sixteen
  one-word Montgomery reductions applied to `u`/`v`. -/
  gcdInitU : UInt256L
  modulus256_toNat : modulus256.toNat = modulus := by decide
  two_lt_modulus : 2 < modulus := by decide
  rModModulus_toNat : rModModulus.toNat = 2 ^ 256 % modulus := by decide
  r2ModModulus_toNat : r2ModModulus.toNat = (2 ^ 256) ^ 2 % modulus := by decide
  montgomeryNegInv_mul_modulus_mod_two_pow_64 :
    montgomeryNegInv.toNat * modulus % 2 ^ 64 = 2 ^ 64 - 1 := by decide
  /-- The binary-GCD initial `u` is the documented power of two. Guards the constant against
  typos; inversion correctness never relies on it (the GCD result is verified at runtime and
  falls back to the proven Fermat path). -/
  gcdInitU_toNat : gcdInitU.toNat = 2 ^ (1071 - gcdFinalRounds) % modulus := by decide
  /-- The 64 base-16 nibbles of the inversion exponent `p - 2` (most significant first)
  Horner-reconstruct to `p - 2`. Drives the fixed-window inversion. -/
  p2HexDigits_reconstruct :
    ((List.range 64).map (fun i => ((modulus - 2) >>> ((63 - i) * 4)) &&& 0xF)).tail.foldl
        (fun n d => n * 16 + d)
        (((List.range 64).map (fun i => ((modulus - 2) >>> ((63 - i) * 4)) &&& 0xF)).headD 0)
      = modulus - 2 := by decide

attribute [simp] Mont256Field.modulus256_toNat Mont256Field.rModModulus_toNat
  Mont256Field.r2ModModulus_toNat

attribute [-simp] Nat.reducePow

/-- The fast carrier for a prime modulus: a 256-bit word below `modulus`, interpreted as a
Montgomery residue. At runtime this erases to `UInt256L`. -/
def FastField (modulus : ℕ) [Mont256Field modulus] : Type :=
  { x : UInt256L // x.toNat < modulus }

variable {modulus : ℕ} [P : Mont256Field modulus]

instance : DecidableEq (FastField modulus) :=
  inferInstanceAs (DecidableEq { x : UInt256L // x.toNat < modulus })

namespace Mont256Field

instance : Fact (Nat.Prime modulus) := ⟨P.prime⟩

@[simp]
theorem modulus_pos : 0 < modulus := Nat.zero_lt_of_lt P.two_lt_modulus

/-- The prime is below `2 ^ 256`: it is the numeric value of the four-limb word. (We do not
assume `2·p < 2 ^ 256`, so this stack also serves top-bit-set moduli.) -/
@[simp]
theorem modulus_lt_two_pow_256 : modulus < 2 ^ 256 := by
  rw [← P.modulus256_toNat]
  exact P.modulus256.toNat_lt

theorem two_ne_zero : (2 : ZMod modulus) ≠ 0 := by
  intro h
  have hdvd : modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 modulus).mp h
  exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)

theorem two_pow_64_ne_zero : ((2 ^ 64 : ℕ) : ZMod modulus) ≠ 0 := by
  simp [two_ne_zero]

theorem two_pow_256_ne_zero : ((2 ^ 256 : ℕ) : ZMod modulus) ≠ 0 := by
  simp [two_ne_zero]

theorem rModModulus_lt_modulus : P.rModModulus.toNat < modulus := by
  rw [P.rModModulus_toNat]
  exact Nat.mod_lt _ P.modulus_pos

@[simp]
theorem rModModulus_cast :
    (P.rModModulus.toNat : ZMod modulus) = ((2 ^ 256 : ℕ) : ZMod modulus) := by
  rw [P.rModModulus_toNat, ZMod.natCast_mod]

@[simp]
theorem r2ModModulus_cast :
    (P.r2ModModulus.toNat : ZMod modulus) = ((2 ^ 256 : ℕ) : ZMod modulus) ^ 2 := by
  rw [P.r2ModModulus_toNat, ZMod.natCast_mod, Nat.cast_pow]

end Mont256Field

/-- Reduce a word known to be `< 2·modulus` to canonical range by one conditional subtract. -/
@[inline]
def conditionalSubtract (x : UInt256L) : UInt256L :=
  if x < P.modulus256 then x else x - P.modulus256

/-- The conditional subtract lands in `[0, modulus)` when the input is `< 2·modulus`. -/
theorem conditionalSubtract_lt (x : UInt256L)
    (h : x.toNat < 2 * modulus) :
    (conditionalSubtract (modulus := modulus) x).toNat < modulus := by
  unfold conditionalSubtract
  by_cases hx : x < P.modulus256
  · rw [if_pos hx]
    rw [UInt256L.lt_iff_toNat_lt, P.modulus256_toNat] at hx
    exact hx
  · rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt] at hx
    have hle : P.modulus256.toNat ≤ x.toNat := by omega
    rw [UInt256L.toNat_sub_of_le hle, P.modulus256_toNat]
    rw [P.modulus256_toNat] at hx
    omega

/-- The conditional subtract preserves the value modulo the prime. -/
theorem conditionalSubtract_cast (x : UInt256L) :
    ((conditionalSubtract (modulus := modulus) x).toNat : ZMod modulus)
      = (x.toNat : ZMod modulus) := by
  unfold conditionalSubtract
  by_cases hx : x < P.modulus256
  · rw [if_pos hx]
  · rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt, P.modulus256_toNat] at hx
    have hle : P.modulus256.toNat ≤ x.toNat := by rw [P.modulus256_toNat]; omega
    rw [UInt256L.toNat_sub_of_le hle, P.modulus256_toNat,
        Nat.cast_sub (by rw [P.modulus256_toNat] at hle; exact hle)]
    simp only [ZMod.natCast_self, sub_zero]

/-- Reduce a value `lo + carry·2²⁵⁶` (with `carry ∈ {0,1}`) known to be `< 2·modulus` to
canonical range. With no carry this is the plain conditional subtract. A set carry means the
value is `≥ 2²⁵⁶ > p`, so one subtraction, which wraps back below `2²⁵⁶`, lands in range;
this is the branch that lets top-bit-set moduli (`2·p ≥ 2²⁵⁶`) reuse the same reducer. -/
@[inline]
def reduceWideRaw (lo : UInt256L) (carry : UInt64) : UInt256L :=
  if carry = 0 then conditionalSubtract (modulus := modulus) lo else lo - P.modulus256

/-- `reduceWideRaw` lands in `[0, modulus)` for a wide input `< 2·modulus`. -/
theorem reduceWideRaw_lt (lo : UInt256L) (carry : UInt64) (hc : carry.toNat ≤ 1)
    (h : lo.toNat + carry.toNat * 2 ^ 256 < 2 * modulus) :
    (reduceWideRaw (modulus := modulus) lo carry).toNat < modulus := by
  unfold reduceWideRaw
  have hp := P.modulus_lt_two_pow_256
  have hmod := P.modulus256_toNat
  by_cases hcarry : carry = 0
  · rw [if_pos hcarry]
    have hc0 : carry.toNat = 0 := by rw [hcarry]; rfl
    exact conditionalSubtract_lt lo
      (by rw [hc0] at h; simp only [Nat.zero_mul, Nat.add_zero] at h; exact h)
  · rw [if_neg hcarry]
    have hne : carry.toNat ≠ 0 := fun h0 => hcarry (UInt64.toNat_inj.mp (by rw [h0]; rfl))
    have hc1 : carry.toNat = 1 := by omega
    rw [hc1] at h
    have hlo_lt : lo.toNat < P.modulus256.toNat := by omega
    rw [UInt256L.toNat_sub_of_lt hlo_lt]
    omega

/-- `reduceWideRaw` preserves the value modulo the prime. -/
theorem reduceWideRaw_cast (lo : UInt256L) (carry : UInt64) (hc : carry.toNat ≤ 1)
    (h : lo.toNat + carry.toNat * 2 ^ 256 < 2 * modulus) :
    ((reduceWideRaw (modulus := modulus) lo carry).toNat : ZMod modulus)
      = ((lo.toNat + carry.toNat * 2 ^ 256 : ℕ) : ZMod modulus) := by
  unfold reduceWideRaw
  have hp := P.modulus_lt_two_pow_256
  have hmod := P.modulus256_toNat
  have hmz : (P.modulus256.toNat : ZMod modulus) = 0 := by
    rw [P.modulus256_toNat]; exact ZMod.natCast_self _
  by_cases hcarry : carry = 0
  · rw [if_pos hcarry]
    have hc0 : carry.toNat = 0 := by rw [hcarry]; rfl
    rw [conditionalSubtract_cast, hc0, Nat.zero_mul, Nat.add_zero]
  · rw [if_neg hcarry]
    have hne : carry.toNat ≠ 0 := fun h0 => hcarry (UInt64.toNat_inj.mp (by rw [h0]; rfl))
    have hc1 : carry.toNat = 1 := by omega
    rw [hc1] at h
    have hlo_lt : lo.toNat < P.modulus256.toNat := by omega
    have hge : P.modulus256.toNat ≤ 2 ^ 256 + lo.toNat := by omega
    have hnat : 2 ^ 256 + lo.toNat = lo.toNat + carry.toNat * 2 ^ 256 := by omega
    rw [UInt256L.toNat_sub_of_lt hlo_lt, Nat.cast_sub hge, hmz, sub_zero, hnat]

/-- `reduceWideRaw` packaged as a `FastField` (input `lo + carry·2²⁵⁶ < 2·modulus`). -/
@[inline]
def reduceWide (lo : UInt256L) (carry : UInt64) (hc : carry.toNat ≤ 1)
    (h : lo.toNat + carry.toNat * 2 ^ 256 < 2 * modulus) : FastField modulus :=
  ⟨reduceWideRaw (modulus := modulus) lo carry, reduceWideRaw_lt lo carry hc h⟩

/-- One additive CIOS step: given the low limb `acc0` and high four limbs `acc` of a 5-limb
accumulator, returns `(acc0 + acc·2⁶⁴)·2⁻⁶⁴ mod p`. Assumes the accumulator is `< p·2⁶⁴`.
The 5→4 limb fold may reach `2²⁵⁶` (when `2·p ≥ 2²⁵⁶`), so the carry-out is captured and fed to
`reduceWideRaw` rather than dropped. -/
@[inline]
def interleavedMontgomeryReduction (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := P.montgomeryNegInv * acc0
  let prod := mulSmall P.modulus256 t
  let cin := (addc acc0 prod.1 0).2
  let sc := UInt256L.addCarryOut acc prod.2 cin
  reduceWideRaw (modulus := modulus) sc.1 sc.2

/-- One CIOS step is correct: given the 5-limb accumulator `(acc0, acc)` bounded by `p·2⁶⁴`,
`interleavedMontgomeryReduction` returns a canonical residue equal to
`(acc0 + acc·2⁶⁴)·(2⁶⁴)⁻¹ mod p`. -/
theorem interleavedMontgomeryReduction_spec (acc0 : UInt64) (acc : UInt256L)
    (hV : acc0.toNat + acc.toNat * 2 ^ 64 < modulus * 2 ^ 64) :
    (interleavedMontgomeryReduction (modulus := modulus) acc0 acc).toNat < modulus ∧
    ((interleavedMontgomeryReduction (modulus := modulus) acc0 acc).toNat : ZMod modulus)
      = ((acc0.toNat + acc.toNat * 2 ^ 64 : ℕ) : ZMod modulus)
        * ((2 ^ 64 : ℕ) : ZMod modulus)⁻¹ := by
  have hcong := P.montgomeryNegInv_mul_modulus_mod_two_pow_64
  have hRne := P.two_pow_64_ne_zero
  have hppos : 0 < modulus := P.modulus_pos
  unfold interleavedMontgomeryReduction
  set t := P.montgomeryNegInv * acc0 with htdef
  set prod := mulSmall P.modulus256 t with hproddef
  set cin := (addc acc0 prod.1 0).2 with hcindef
  set sc := UInt256L.addCarryOut acc prod.2 cin with hsdef
  have ht_lt : t.toNat < 2 ^ 64 := t.toNat_lt
  have ha0 : acc0.toNat < 2 ^ 64 := acc0.toNat_lt
  have hp1 : prod.1.toNat < 2 ^ 64 := prod.1.toNat_lt
  have hprodval : prod.1.toNat + prod.2.toNat * 2 ^ 64 = modulus * t.toNat := by
    rw [hproddef, mulSmall_toNat, P.modulus256_toNat]
  obtain ⟨haddc, hcin1, hD⟩ := addc_spec acc0 prod.1 0 (by decide)
  rw [← hcindef] at haddc hcin1
  rw [show (0 : UInt64).toNat = 0 from rfl] at haddc
  have hVmod : (acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 = acc0.toNat := by omega
  have htm : (acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 * P.montgomeryNegInv.toNat % 2 ^ 64
      = t.toNat := by
    rw [hVmod, htdef, UInt64.toNat_mul, Nat.mul_comm]
  have hdvd : 2 ^ 64 ∣ (acc0.toNat + acc.toNat * 2 ^ 64)
      + (prod.1.toNat + prod.2.toNat * 2 ^ 64) := by
    have h := Montgomery.dvd_add (2 ^ 64) (modulus) P.montgomeryNegInv.toNat
      (by decide) hcong (acc0.toNat + acc.toNat * 2 ^ 64)
    rw [htm] at h
    rwa [show t.toNat * modulus = modulus * t.toNat from by ring,
      ← hprodval] at h
  have hD0 : (addc acc0 prod.1 0).1.toNat = 0 := by omega
  have hu : acc.toNat + prod.2.toNat + cin.toNat
      = ((acc0.toNat + acc.toNat * 2 ^ 64) + (prod.1.toNat + prod.2.toNat * 2 ^ 64)) / 2 ^ 64 := by
    omega
  have hpb : prod.1.toNat + prod.2.toNat * 2 ^ 64 < modulus * 2 ^ 64 := by
    rw [hprodval]; nlinarith [ht_lt, hppos]
  have hSlt : acc.toNat + prod.2.toNat + cin.toNat < 2 * modulus := by
    rw [hu]; omega
  obtain ⟨hsc, hscbound⟩ := UInt256L.toNat_addCarryOut acc prod.2 cin hcin1
  rw [← hsdef] at hsc hscbound
  have hbnd : sc.1.toNat + sc.2.toNat * 2 ^ 256 < 2 * modulus := by
    rw [hsc]; exact hSlt
  refine ⟨?_, ?_⟩
  · exact reduceWideRaw_lt sc.1 sc.2 hscbound hbnd
  · rw [reduceWideRaw_cast sc.1 sc.2 hscbound hbnd, hsc, hu]
    rw [show (acc0.toNat + acc.toNat * 2 ^ 64) + (prod.1.toNat + prod.2.toNat * 2 ^ 64)
          = (acc0.toNat + acc.toNat * 2 ^ 64)
            + ((acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 * P.montgomeryNegInv.toNat % 2 ^ 64)
              * modulus from by rw [htm, hprodval]; ring]
    exact Montgomery.reduceNatQuotient_cast (2 ^ 64) (modulus)
      P.montgomeryNegInv.toNat (by decide) hcong hRne (acc0.toNat + acc.toNat * 2 ^ 64)

/-- Montgomery multiplication: `montgomeryMul a b = a · b · R⁻¹ mod p` (CIOS, 4 rounds).
Requires `lhs < modulus` (the fully-scanned operand); `rhs` is unrestricted. -/
@[specialize]
def montgomeryMul (lhs rhs : UInt256L) : UInt256L :=
  let (a0, a) := mulSmall lhs rhs.l0
  let r0 := interleavedMontgomeryReduction (modulus := modulus) a0 a
  let (b0, b) := mulSmallAndAcc lhs rhs.l1 r0
  let r1 := interleavedMontgomeryReduction (modulus := modulus) b0 b
  let (c0, c) := mulSmallAndAcc lhs rhs.l2 r1
  let r2 := interleavedMontgomeryReduction (modulus := modulus) c0 c
  let (d0, d) := mulSmallAndAcc lhs rhs.l3 r2
  interleavedMontgomeryReduction (modulus := modulus) d0 d

/-- Round 0 of CIOS: `mulSmall` then one reduction step. -/
theorem montgomeryInit_spec (lhs : UInt256L) (d : UInt64)
    (hlhs : lhs.toNat < modulus) :
    (interleavedMontgomeryReduction (modulus := modulus)
        (mulSmall lhs d).1 (mulSmall lhs d).2).toNat < modulus ∧
    ((interleavedMontgomeryReduction (modulus := modulus)
        (mulSmall lhs d).1 (mulSmall lhs d).2).toNat : ZMod modulus)
      = (lhs.toNat : ZMod modulus) * (d.toNat : ZMod modulus)
        * ((2 ^ 64 : ℕ) : ZMod modulus)⁻¹ := by
  have hv : (mulSmall lhs d).1.toNat + (mulSmall lhs d).2.toNat * 2 ^ 64 = lhs.toNat * d.toNat :=
    mulSmall_toNat lhs d
  have hrng : (mulSmall lhs d).1.toNat + (mulSmall lhs d).2.toNat * 2 ^ 64
      < modulus * 2 ^ 64 := by
    rw [hv]; nlinarith [hlhs, d.toNat_lt]
  obtain ⟨hb, hc⟩ := interleavedMontgomeryReduction_spec (modulus := modulus)
    (mulSmall lhs d).1 (mulSmall lhs d).2 hrng
  refine ⟨hb, ?_⟩
  rw [hc, hv]; push_cast; ring

/-- Rounds 1–3 of CIOS: `mulSmallAndAcc` then one reduction step. -/
theorem montgomeryStep_spec (lhs : UInt256L) (d : UInt64) (acc : UInt256L)
    (hlhs : lhs.toNat < modulus) (hacc : acc.toNat < modulus) :
    (interleavedMontgomeryReduction (modulus := modulus) (mulSmallAndAcc lhs d acc).1
        (mulSmallAndAcc lhs d acc).2).toNat < modulus ∧
    ((interleavedMontgomeryReduction (modulus := modulus) (mulSmallAndAcc lhs d acc).1
        (mulSmallAndAcc lhs d acc).2).toNat : ZMod modulus)
      = ((lhs.toNat : ZMod modulus) * (d.toNat : ZMod modulus)
          + (acc.toNat : ZMod modulus))
        * ((2 ^ 64 : ℕ) : ZMod modulus)⁻¹ := by
  have hv : (mulSmallAndAcc lhs d acc).1.toNat + (mulSmallAndAcc lhs d acc).2.toNat * 2 ^ 64
      = lhs.toNat * d.toNat + acc.toNat := mulSmallAndAcc_toNat lhs d acc
  have hrng : (mulSmallAndAcc lhs d acc).1.toNat + (mulSmallAndAcc lhs d acc).2.toNat * 2 ^ 64
      < modulus * 2 ^ 64 := by
    rw [hv]; nlinarith [hlhs, hacc, d.toNat_lt]
  obtain ⟨hb, hc⟩ := interleavedMontgomeryReduction_spec (modulus := modulus)
    (mulSmallAndAcc lhs d acc).1 (mulSmallAndAcc lhs d acc).2 hrng
  refine ⟨hb, ?_⟩
  rw [hc, hv]; push_cast; ring

/-- The field-level reassembly of the four reduction rounds into `L · rhs · (R⁴)⁻¹`. -/
private theorem montgomeryMul_assemble
    (R L b0 b1 b2 b3 c0 c1 c2 res : ZMod modulus)
    (hRne : R ≠ 0)
    (h0 : c0 = L * b0 * R⁻¹) (h1 : c1 = (L * b1 + c0) * R⁻¹)
    (h2 : c2 = (L * b2 + c1) * R⁻¹) (h3 : res = (L * b3 + c2) * R⁻¹) :
    res = L * (b0 + b1 * R + b2 * R ^ 2 + b3 * R ^ 3) * (R ^ 4)⁻¹ := by
  have e0 : c0 * R = L * b0 := by rw [h0, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have e1 : c1 * R = L * b1 + c0 := by rw [h1, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have e2 : c2 * R = L * b2 + c1 := by rw [h2, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have e3 : res * R = L * b3 + c2 := by rw [h3, mul_assoc, inv_mul_cancel₀ hRne, mul_one]
  have hkey : res * R ^ 4 = L * (b0 + b1 * R + b2 * R ^ 2 + b3 * R ^ 3) := by
    linear_combination e0 + R * e1 + R ^ 2 * e2 + R ^ 3 * e3
  rw [← hkey, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 4 hRne), mul_one]

/-- Montgomery multiplication is correct: for `lhs < modulus` and arbitrary `rhs`, the result
is a canonical residue equal to `lhs · rhs · (2²⁵⁶)⁻¹ mod p`. -/
theorem montgomeryMul_spec (lhs rhs : UInt256L) (hlhs : lhs.toNat < modulus) :
    (montgomeryMul (modulus := modulus) lhs rhs).toNat < modulus ∧
    ((montgomeryMul (modulus := modulus) lhs rhs).toNat : ZMod modulus)
      = (lhs.toNat : ZMod modulus)
        * (rhs.toNat : ZMod modulus)
        * ((2 ^ 256 : ℕ) : ZMod modulus)⁻¹ := by
  unfold montgomeryMul
  set r0 := interleavedMontgomeryReduction (modulus := modulus)
    (mulSmall lhs rhs.l0).1 (mulSmall lhs rhs.l0).2 with hr0
  set r1 := interleavedMontgomeryReduction (modulus := modulus) (mulSmallAndAcc lhs rhs.l1 r0).1
    (mulSmallAndAcc lhs rhs.l1 r0).2 with hr1
  set r2 := interleavedMontgomeryReduction (modulus := modulus) (mulSmallAndAcc lhs rhs.l2 r1).1
    (mulSmallAndAcc lhs rhs.l2 r1).2 with hr2
  obtain ⟨hb0, hc0⟩ := montgomeryInit_spec (modulus := modulus) lhs rhs.l0 hlhs
  rw [← hr0] at hb0 hc0
  obtain ⟨hb1, hc1⟩ := montgomeryStep_spec (modulus := modulus) lhs rhs.l1 r0 hlhs hb0
  rw [← hr1] at hb1 hc1
  obtain ⟨hb2, hc2⟩ := montgomeryStep_spec (modulus := modulus) lhs rhs.l2 r1 hlhs hb1
  rw [← hr2] at hb2 hc2
  obtain ⟨hb3, hc3⟩ := montgomeryStep_spec (modulus := modulus) lhs rhs.l3 r2 hlhs hb2
  set rr := interleavedMontgomeryReduction (modulus := modulus) (mulSmallAndAcc lhs rhs.l3 r2).1
    (mulSmallAndAcc lhs rhs.l3 r2).2 with hrr
  refine ⟨hb3, ?_⟩
  set R := ((2 ^ 64 : ℕ) : ZMod modulus) with hRdef
  have hrhs : (rhs.toNat : ZMod modulus)
      = (rhs.l0.toNat : ZMod modulus)
        + (rhs.l1.toNat : ZMod modulus) * R
        + (rhs.l2.toNat : ZMod modulus) * R ^ 2
        + (rhs.l3.toNat : ZMod modulus) * R ^ 3 := by
    simp only [UInt256L.toNat, Nat.shiftLeft_eq]; push_cast [hRdef]; ring
  have h256 : ((2 ^ 256 : ℕ) : ZMod modulus) = R ^ 4 := by
    rw [hRdef]; push_cast; ring
  rw [h256, hrhs]
  exact montgomeryMul_assemble R (lhs.toNat : ZMod modulus)
    (rhs.l0.toNat : ZMod modulus)
    (rhs.l1.toNat : ZMod modulus)
    (rhs.l2.toNat : ZMod modulus)
    (rhs.l3.toNat : ZMod modulus) (r0.toNat : ZMod modulus)
    (r1.toNat : ZMod modulus) (r2.toNat : ZMod modulus)
    (rr.toNat : ZMod modulus) (P.two_pow_64_ne_zero) hc0 hc1 hc2 hc3

end Native256
end Montgomery
