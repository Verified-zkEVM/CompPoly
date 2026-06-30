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
# Native 256-bit Montgomery field — reduction and multiplication

The radix-`R = 2^256` word bridge shared by every fast 256-bit prime field, the analogue of
`CompPoly.Fields.Montgomery.Native32` for four-`UInt64`-limb fields.

* `Mont256Field F` bundles the prime (`fieldSize`), its native-word forms, the Montgomery
  constants (`modulus`, `rModModulus`, `r2ModModulus`, `montgomeryNegInv`), and the small
  `decide`-checkable numeric/`ZMod` facts the proofs consume. Everything except the four word
  constants is spec-level and erased at codegen.
* `FastField F` is the fast carrier `{ x : UInt256L // x.toNat < fieldSize }`, tagged by `F`
  so the generic `Field`/… instances resolve for each concrete field. It erases to `UInt256L`.
* The executable `def`s are `@[inline]`/`@[specialize]`, so once a concrete instance is fixed
  the instance projections fold to literals — no `Mont256Field` dictionary survives to runtime.

The CIOS reducer divides by `2^64` per limb (`interleavedMontgomeryReduction`); four rounds
realise `a · b · (2^256)⁻¹ mod p` (`montgomeryMul`). The radix-generic number theory lives in
`CompPoly.Fields.Montgomery.Basic`; concrete fields supply a `Mont256Field` instance.
-/

set_option maxRecDepth 4000

namespace Montgomery
namespace Native256

/-- Per-field data and spec-level facts realizing a 256-bit prime field as a fast Montgomery
field with `R = 2^256` (four 64-bit limbs). Only the four word constants survive to runtime. -/
class Mont256Field (F : Type) where
  /-- The field size / prime `p`. -/
  fieldSize : Nat
  /-- `fieldSize` is prime — needed to reduce into `ZMod fieldSize` as a field. -/
  prime : Fact (Nat.Prime fieldSize)
  /-- `fieldSize` as a 256-bit word. -/
  modulus : UInt256L
  /-- `-fieldSize⁻¹ mod 2^64`, the per-limb multiplier for interleaved Montgomery reduction. -/
  montgomeryNegInv : UInt64
  /-- `2^256 mod fieldSize`, the Montgomery representation of one. -/
  rModModulus : UInt256L
  /-- `(2^256)^2 mod fieldSize`, used to enter Montgomery form. -/
  r2ModModulus : UInt256L
  modulus_toNat : modulus.toNat = fieldSize
  two_mul_fieldSize_lt_two256 : 2 * fieldSize < 2 ^ 256
  rModModulus_lt_fieldSize : rModModulus.toNat < fieldSize
  rModModulus_cast : (rModModulus.toNat : ZMod fieldSize) = ((2 ^ 256 : Nat) : ZMod fieldSize)
  r2ModModulus_cast :
    (r2ModModulus.toNat : ZMod fieldSize) = ((2 ^ 256 : Nat) : ZMod fieldSize) ^ 2
  /-- The Montgomery inverse congruence `negInv * p ≡ 2^64 - 1 [MOD 2^64]`. -/
  negInv_congr : montgomeryNegInv.toNat * fieldSize ≡ 2 ^ 64 - 1 [MOD 2 ^ 64]
  /-- Characteristic `≠ 2`, used to build the `NonBinaryField` instance. -/
  two_ne_zero_in_field : ((2 : Nat) : ZMod fieldSize) ≠ 0
  /-- The 64 base-16 nibbles of the inversion exponent `p - 2` (most significant first)
  Horner-reconstruct to `p - 2`. Drives the fixed-window inversion; `decide`-checked per field. -/
  p2HexDigits_reconstruct :
    ((List.range 64).map (fun i => ((fieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).tail.foldl
        (fun n d => n * 16 + d)
        (((List.range 64).map (fun i => ((fieldSize - 2) >>> ((63 - i) * 4)) &&& 0xF)).headD 0)
      = fieldSize - 2

attribute [instance] Mont256Field.prime

/-- The fast carrier: a 256-bit word below the field size. Erases to `UInt256L`. -/
def FastField (F : Type) [Mont256Field F] : Type :=
  { x : UInt256L // x.toNat < Mont256Field.fieldSize F }

instance (F : Type) [Mont256Field F] : DecidableEq (FastField F) :=
  inferInstanceAs (DecidableEq { x : UInt256L // x.toNat < Mont256Field.fieldSize F })

variable {F : Type} [P : Mont256Field F]

/-- `2^64` is a unit in `ZMod p`: an odd prime cannot divide a power of two. -/
theorem r64_ne_zero : ((2 ^ 64 : Nat) : ZMod (Mont256Field.fieldSize F)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact Mont256Field.two_ne_zero_in_field (F := F)
    ((ZMod.natCast_eq_zero_iff _ _).mpr (P.prime.out.dvd_of_dvd_pow hdvd))

/-- Reduce a word known to be `< 2·modulus` to canonical range by one conditional subtract. -/
@[inline]
def reduceUInt256Lt2ModulusRaw (x : UInt256L) : UInt256L :=
  if x < P.modulus then x else x - P.modulus

/-- The conditional subtract lands in `[0, fieldSize)` when the input is `< 2·fieldSize`. -/
theorem reduceUInt256Lt2ModulusRaw_lt (x : UInt256L)
    (h : x.toNat < 2 * Mont256Field.fieldSize F) :
    (reduceUInt256Lt2ModulusRaw (F := F) x).toNat < Mont256Field.fieldSize F := by
  unfold reduceUInt256Lt2ModulusRaw
  by_cases hx : x < P.modulus
  · rw [if_pos hx]
    rw [UInt256L.lt_iff_toNat_lt, P.modulus_toNat] at hx
    exact hx
  · rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt] at hx
    have hle : P.modulus.toNat ≤ x.toNat := by omega
    rw [UInt256L.toNat_sub_of_le hle, P.modulus_toNat]
    rw [P.modulus_toNat] at hx
    omega

/-- The conditional subtract preserves the value modulo the prime. -/
theorem reduceUInt256Lt2ModulusRaw_cast (x : UInt256L) :
    ((reduceUInt256Lt2ModulusRaw (F := F) x).toNat : ZMod (Mont256Field.fieldSize F))
      = (x.toNat : ZMod (Mont256Field.fieldSize F)) := by
  unfold reduceUInt256Lt2ModulusRaw
  by_cases hx : x < P.modulus
  · rw [if_pos hx]
  · rw [if_neg hx]
    rw [UInt256L.lt_iff_toNat_lt, P.modulus_toNat] at hx
    have hle : P.modulus.toNat ≤ x.toNat := by rw [P.modulus_toNat]; omega
    rw [UInt256L.toNat_sub_of_le hle, P.modulus_toNat,
        Nat.cast_sub (by rw [P.modulus_toNat] at hle; exact hle)]
    simp only [ZMod.natCast_self, sub_zero]

/-- `reduceUInt256Lt2ModulusRaw` packaged as a `FastField` (input `< 2·fieldSize`). -/
@[inline]
def reduceUInt256Lt2Modulus (x : UInt256L) (h : x.toNat < 2 * Mont256Field.fieldSize F) :
    FastField F :=
  ⟨reduceUInt256Lt2ModulusRaw (F := F) x, reduceUInt256Lt2ModulusRaw_lt x h⟩

/-- One additive CIOS step: given the low limb `acc0` and high four limbs `acc` of a 5-limb
accumulator, returns `(acc0 + acc·2⁶⁴)·2⁻⁶⁴ mod p`. Assumes the accumulator is `< p·2⁶⁴`. -/
@[inline]
def interleavedMontgomeryReduction (acc0 : UInt64) (acc : UInt256L) : UInt256L :=
  let t := P.montgomeryNegInv * acc0
  let prod := mulSmall P.modulus t
  let cin := (addc acc0 prod.1 0).2
  let s := UInt256L.addCarry acc prod.2 cin
  reduceUInt256Lt2ModulusRaw (F := F) s

/-- One CIOS step is correct: given the 5-limb accumulator `(acc0, acc)` bounded by `p·2⁶⁴`,
`interleavedMontgomeryReduction` returns a canonical residue equal to
`(acc0 + acc·2⁶⁴)·(2⁶⁴)⁻¹ mod p`. -/
theorem interleavedMontgomeryReduction_spec (acc0 : UInt64) (acc : UInt256L)
    (hV : acc0.toNat + acc.toNat * 2 ^ 64 < Mont256Field.fieldSize F * 2 ^ 64) :
    (interleavedMontgomeryReduction (F := F) acc0 acc).toNat < Mont256Field.fieldSize F ∧
    ((interleavedMontgomeryReduction (F := F) acc0 acc).toNat : ZMod (Mont256Field.fieldSize F))
      = ((acc0.toNat + acc.toNat * 2 ^ 64 : Nat) : ZMod (Mont256Field.fieldSize F))
        * ((2 ^ 64 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ := by
  have hcong := P.negInv_congr
  have hRne := r64_ne_zero (F := F)
  have h2p := P.two_mul_fieldSize_lt_two256
  have hppos : 0 < Mont256Field.fieldSize F := P.prime.out.pos
  unfold interleavedMontgomeryReduction
  set t := P.montgomeryNegInv * acc0 with htdef
  set prod := mulSmall P.modulus t with hproddef
  set cin := (addc acc0 prod.1 0).2 with hcindef
  set s := UInt256L.addCarry acc prod.2 cin with hsdef
  have ht_lt : t.toNat < 2 ^ 64 := t.toNat_lt
  have ha0 : acc0.toNat < 2 ^ 64 := acc0.toNat_lt
  have hp1 : prod.1.toNat < 2 ^ 64 := prod.1.toNat_lt
  have hprodval : prod.1.toNat + prod.2.toNat * 2 ^ 64 = Mont256Field.fieldSize F * t.toNat := by
    rw [hproddef, mulSmall_toNat, P.modulus_toNat]
  obtain ⟨haddc, hcin1, hD⟩ := addc_spec acc0 prod.1 0 (by decide)
  rw [← hcindef] at haddc hcin1
  rw [show (0 : UInt64).toNat = 0 from rfl] at haddc
  have hVmod : (acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 = acc0.toNat := by omega
  have htm : (acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 * P.montgomeryNegInv.toNat % 2 ^ 64
      = t.toNat := by
    rw [hVmod, htdef, UInt64.toNat_mul, Nat.mul_comm]
  have hdvd : 2 ^ 64 ∣ (acc0.toNat + acc.toNat * 2 ^ 64)
      + (prod.1.toNat + prod.2.toNat * 2 ^ 64) := by
    have h := Montgomery.sum_dvd (2 ^ 64) (Mont256Field.fieldSize F) P.montgomeryNegInv.toNat
      (by decide) hcong (acc0.toNat + acc.toNat * 2 ^ 64)
    rw [htm] at h
    rwa [show t.toNat * Mont256Field.fieldSize F = Mont256Field.fieldSize F * t.toNat from by ring,
      ← hprodval] at h
  have hD0 : (addc acc0 prod.1 0).1.toNat = 0 := by omega
  have hu : acc.toNat + prod.2.toNat + cin.toNat
      = ((acc0.toNat + acc.toNat * 2 ^ 64) + (prod.1.toNat + prod.2.toNat * 2 ^ 64)) / 2 ^ 64 := by
    omega
  have hpb : prod.1.toNat + prod.2.toNat * 2 ^ 64 < Mont256Field.fieldSize F * 2 ^ 64 := by
    rw [hprodval]; nlinarith [ht_lt, hppos]
  have hSlt : acc.toNat + prod.2.toNat + cin.toNat < 2 * Mont256Field.fieldSize F := by
    rw [hu]; omega
  have hsval : s.toNat = acc.toNat + prod.2.toNat + cin.toNat := by
    rw [hsdef, UInt256L.toNat_addCarry acc prod.2 cin hcin1, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_⟩
  · exact reduceUInt256Lt2ModulusRaw_lt s (by rw [hsval]; exact hSlt)
  · rw [reduceUInt256Lt2ModulusRaw_cast, hsval, hu]
    rw [show (acc0.toNat + acc.toNat * 2 ^ 64) + (prod.1.toNat + prod.2.toNat * 2 ^ 64)
          = (acc0.toNat + acc.toNat * 2 ^ 64)
            + ((acc0.toNat + acc.toNat * 2 ^ 64) % 2 ^ 64 * P.montgomeryNegInv.toNat % 2 ^ 64)
              * Mont256Field.fieldSize F from by rw [htm, hprodval]; ring]
    exact Montgomery.quotient_cast (2 ^ 64) (Mont256Field.fieldSize F) P.montgomeryNegInv.toNat
      (by decide) hcong hRne (acc0.toNat + acc.toNat * 2 ^ 64)

/-- Montgomery multiplication: `montgomeryMul a b = a · b · R⁻¹ mod p` (CIOS, 4 rounds).
Requires `lhs < modulus` (the fully-scanned operand); `rhs` is unrestricted. -/
@[specialize]
def montgomeryMul (lhs rhs : UInt256L) : UInt256L :=
  let (a0, a) := mulSmall lhs rhs.l0
  let r0 := interleavedMontgomeryReduction (F := F) a0 a
  let (b0, b) := mulSmallAndAcc lhs rhs.l1 r0
  let r1 := interleavedMontgomeryReduction (F := F) b0 b
  let (c0, c) := mulSmallAndAcc lhs rhs.l2 r1
  let r2 := interleavedMontgomeryReduction (F := F) c0 c
  let (d0, d) := mulSmallAndAcc lhs rhs.l3 r2
  interleavedMontgomeryReduction (F := F) d0 d

/-- Round 0 of CIOS: `mulSmall` then one reduction step. -/
theorem montgomeryInit_spec (lhs : UInt256L) (d : UInt64)
    (hlhs : lhs.toNat < Mont256Field.fieldSize F) :
    (interleavedMontgomeryReduction (F := F) (mulSmall lhs d).1 (mulSmall lhs d).2).toNat
        < Mont256Field.fieldSize F ∧
    ((interleavedMontgomeryReduction (F := F) (mulSmall lhs d).1 (mulSmall lhs d).2).toNat :
        ZMod (Mont256Field.fieldSize F))
      = (lhs.toNat : ZMod (Mont256Field.fieldSize F)) * (d.toNat : ZMod (Mont256Field.fieldSize F))
        * ((2 ^ 64 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ := by
  have hv : (mulSmall lhs d).1.toNat + (mulSmall lhs d).2.toNat * 2 ^ 64 = lhs.toNat * d.toNat :=
    mulSmall_toNat lhs d
  have hrng : (mulSmall lhs d).1.toNat + (mulSmall lhs d).2.toNat * 2 ^ 64
      < Mont256Field.fieldSize F * 2 ^ 64 := by
    rw [hv]; nlinarith [hlhs, d.toNat_lt]
  obtain ⟨hb, hc⟩ :=
    interleavedMontgomeryReduction_spec (F := F) (mulSmall lhs d).1 (mulSmall lhs d).2 hrng
  refine ⟨hb, ?_⟩
  rw [hc, hv]; push_cast; ring

/-- Rounds 1–3 of CIOS: `mulSmallAndAcc` then one reduction step. -/
theorem montgomeryStep_spec (lhs : UInt256L) (d : UInt64) (acc : UInt256L)
    (hlhs : lhs.toNat < Mont256Field.fieldSize F) (hacc : acc.toNat < Mont256Field.fieldSize F) :
    (interleavedMontgomeryReduction (F := F) (mulSmallAndAcc lhs d acc).1
        (mulSmallAndAcc lhs d acc).2).toNat < Mont256Field.fieldSize F ∧
    ((interleavedMontgomeryReduction (F := F) (mulSmallAndAcc lhs d acc).1
        (mulSmallAndAcc lhs d acc).2).toNat : ZMod (Mont256Field.fieldSize F))
      = ((lhs.toNat : ZMod (Mont256Field.fieldSize F)) * (d.toNat : ZMod (Mont256Field.fieldSize F))
          + (acc.toNat : ZMod (Mont256Field.fieldSize F)))
        * ((2 ^ 64 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ := by
  have hv : (mulSmallAndAcc lhs d acc).1.toNat + (mulSmallAndAcc lhs d acc).2.toNat * 2 ^ 64
      = lhs.toNat * d.toNat + acc.toNat := mulSmallAndAcc_toNat lhs d acc
  have hrng : (mulSmallAndAcc lhs d acc).1.toNat + (mulSmallAndAcc lhs d acc).2.toNat * 2 ^ 64
      < Mont256Field.fieldSize F * 2 ^ 64 := by
    rw [hv]; nlinarith [hlhs, hacc, d.toNat_lt]
  obtain ⟨hb, hc⟩ := interleavedMontgomeryReduction_spec (F := F) (mulSmallAndAcc lhs d acc).1
    (mulSmallAndAcc lhs d acc).2 hrng
  refine ⟨hb, ?_⟩
  rw [hc, hv]; push_cast; ring

/-- The field-level reassembly of the four reduction rounds into `L · rhs · (R⁴)⁻¹`. -/
private theorem montgomeryMul_assemble
    (R L b0 b1 b2 b3 c0 c1 c2 res : ZMod (Mont256Field.fieldSize F))
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
theorem montgomeryMul_spec (lhs rhs : UInt256L) (hlhs : lhs.toNat < Mont256Field.fieldSize F) :
    (montgomeryMul (F := F) lhs rhs).toNat < Mont256Field.fieldSize F ∧
    ((montgomeryMul (F := F) lhs rhs).toNat : ZMod (Mont256Field.fieldSize F))
      = (lhs.toNat : ZMod (Mont256Field.fieldSize F))
        * (rhs.toNat : ZMod (Mont256Field.fieldSize F))
        * ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ := by
  unfold montgomeryMul
  set r0 := interleavedMontgomeryReduction (F := F) (mulSmall lhs rhs.l0).1 (mulSmall lhs rhs.l0).2
    with hr0
  set r1 := interleavedMontgomeryReduction (F := F) (mulSmallAndAcc lhs rhs.l1 r0).1
    (mulSmallAndAcc lhs rhs.l1 r0).2 with hr1
  set r2 := interleavedMontgomeryReduction (F := F) (mulSmallAndAcc lhs rhs.l2 r1).1
    (mulSmallAndAcc lhs rhs.l2 r1).2 with hr2
  obtain ⟨hb0, hc0⟩ := montgomeryInit_spec (F := F) lhs rhs.l0 hlhs
  rw [← hr0] at hb0 hc0
  obtain ⟨hb1, hc1⟩ := montgomeryStep_spec (F := F) lhs rhs.l1 r0 hlhs hb0
  rw [← hr1] at hb1 hc1
  obtain ⟨hb2, hc2⟩ := montgomeryStep_spec (F := F) lhs rhs.l2 r1 hlhs hb1
  rw [← hr2] at hb2 hc2
  obtain ⟨hb3, hc3⟩ := montgomeryStep_spec (F := F) lhs rhs.l3 r2 hlhs hb2
  set rr := interleavedMontgomeryReduction (F := F) (mulSmallAndAcc lhs rhs.l3 r2).1
    (mulSmallAndAcc lhs rhs.l3 r2).2 with hrr
  refine ⟨hb3, ?_⟩
  set R := ((2 ^ 64 : Nat) : ZMod (Mont256Field.fieldSize F)) with hRdef
  have hrhs : (rhs.toNat : ZMod (Mont256Field.fieldSize F))
      = (rhs.l0.toNat : ZMod (Mont256Field.fieldSize F))
        + (rhs.l1.toNat : ZMod (Mont256Field.fieldSize F)) * R
        + (rhs.l2.toNat : ZMod (Mont256Field.fieldSize F)) * R ^ 2
        + (rhs.l3.toNat : ZMod (Mont256Field.fieldSize F)) * R ^ 3 := by
    simp only [UInt256L.toNat, Nat.shiftLeft_eq]; push_cast [hRdef]; ring
  have h256 : ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F)) = R ^ 4 := by
    rw [hRdef]; push_cast; ring
  rw [h256, hrhs]
  exact montgomeryMul_assemble R (lhs.toNat : ZMod (Mont256Field.fieldSize F))
    (rhs.l0.toNat : ZMod (Mont256Field.fieldSize F))
    (rhs.l1.toNat : ZMod (Mont256Field.fieldSize F))
    (rhs.l2.toNat : ZMod (Mont256Field.fieldSize F))
    (rhs.l3.toNat : ZMod (Mont256Field.fieldSize F)) (r0.toNat : ZMod (Mont256Field.fieldSize F))
    (r1.toNat : ZMod (Mont256Field.fieldSize F)) (r2.toNat : ZMod (Mont256Field.fieldSize F))
    (rr.toNat : ZMod (Mont256Field.fieldSize F)) (r64_ne_zero (F := F)) hc0 hc1 hc2 hc3

end Native256
end Montgomery
