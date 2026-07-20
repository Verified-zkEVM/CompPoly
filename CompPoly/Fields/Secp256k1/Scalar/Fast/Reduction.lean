/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Secp256k1.Scalar.Fast.Internal

/-!
  # Reduction routines for fast secp256k1 scalar field arithmetic

  This module contains raw modular reduction helpers and theorem scaffolding
  for the later ring-equivalence proof.
-/

namespace Secp256k1.Scalar.Fast
namespace Reduction

/-- Split `2^257` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_257 : (2 : Nat) ^ 257 = 2 ^ 256 * 2 := by
  rw [show 257 = 256 + 1 by omega, pow_add]
  norm_num

/-- Split `2^259` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_259 : (2 : Nat) ^ 259 = 2 ^ 256 * 2 ^ 3 := by
  rw [show 259 = 256 + 3 by omega, pow_add]

/-- Split `2^320` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_320 : (2 : Nat) ^ 320 = 2 ^ 256 * 2 ^ 64 := by
  rw [show 320 = 256 + 64 by omega, pow_add]

/-- Split `2^384` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_384 : (2 : Nat) ^ 384 = 2 ^ 256 * 2 ^ 128 := by
  rw [show 384 = 256 + 128 by omega, pow_add]

/-- Split `2^385` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_385 : (2 : Nat) ^ 385 = 2 ^ 256 * 2 ^ 129 := by
  rw [show 385 = 256 + 129 by omega, pow_add]

/-- Split `2^448` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_448 : (2 : Nat) ^ 448 = 2 ^ 256 * 2 ^ 192 := by
  rw [show 448 = 256 + 192 by omega, pow_add]

/-- Split `2^512` at the largest exponent evaluated by default. -/
@[simp] private theorem two_pow_512 : (2 : Nat) ^ 512 = 2 ^ 256 * 2 ^ 256 := by
  rw [show 512 = 256 + 256 by omega, pow_add]

/-- Exact linear upper bound for multiplication by the low complement limb. -/
private theorem mulNC0_bound (x : UInt64) :
    x.toNat * N_C_0.toNat < 2 ^ 64 * N_C_0.toNat := by
  have hx := x.toNat_lt_size
  norm_num [UInt64.size, N_C_0, UInt64.toNat_ofNat] at hx ⊢
  omega

/-- Exact linear upper bound for multiplication by the high complement limb. -/
private theorem mulNC1_bound (x : UInt64) :
    x.toNat * N_C_1.toNat < 2 ^ 64 * N_C_1.toNat := by
  have hx := x.toNat_lt_size
  norm_num [UInt64.size, N_C_1, UInt64.toNat_ofNat] at hx ⊢
  omega

/-- Add `2^256 - n` if `overflow` is true, i.e. subtract `n` modulo `2^256`.
    This mirrors `secp256k1_scalar_reduce`. -/
@[inline] def reduceRaw (d0 d1 d2 d3 : UInt64) (overflow : Bool) : Limbs4 :=
  if overflow then
    let (r0, c) := addCarry d0 N_C_0 0
    let (r1, c) := addCarry d1 N_C_1 c
    let (r2, c) := addCarry d2 N_C_2 c
    let (r3, _) := addCarry d3 0 c
    (r0, r1, r2, r3)
  else
    (d0, d1, d2, d3)

/-- Canonicalize an arbitrary four-limb scalar by conditionally subtracting the order. -/
@[inline] def canonicalizeRaw (d0 d1 d2 d3 : UInt64) : Limbs4 :=
  reduceRaw d0 d1 d2 d3 (checkOverflowRaw d0 d1 d2 d3)

/-- Exact value equation for the unconditional `reduceRaw` branch. -/
private theorem reduceRaw_true_value (d0 d1 d2 d3 : UInt64) :
    let r := reduceRaw d0 d1 d2 d3 true
    ∃ c : Nat, c ≤ 1 ∧
      (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat + 2 ^ 256 * c =
        (Repr.ofLimbs d0 d1 d2 d3).toNat +
          (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) := by
  let q := addRaw d0 d1 d2 d3 N_C_0 N_C_1 N_C_2 0
  refine ⟨q.2.2.2.2.toNat,
    addRaw_carry_le_one d0 d1 d2 d3 N_C_0 N_C_1 N_C_2 0, ?_⟩
  have h := addRaw_value d0 d1 d2 d3 N_C_0 N_C_1 N_C_2 0
  rw [Repr.complement_toNat] at h
  simpa [reduceRaw, q] using h

/-- Reducing a value at least the scalar order subtracts the order once. -/
theorem reduceRaw_true_of_ge (d0 d1 d2 d3 : UInt64)
    (hge : Secp256k1.Scalar.Basic.CARD ≤ (Repr.ofLimbs d0 d1 d2 d3).toNat) :
    let r := reduceRaw d0 d1 d2 d3 true
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat =
      (Repr.ofLimbs d0 d1 d2 d3).toNat - Secp256k1.Scalar.Basic.CARD := by
  obtain ⟨c, hc, hvalue⟩ := reduceRaw_true_value d0 d1 d2 d3
  let r := reduceRaw d0 d1 d2 d3 true
  have hout := Repr.toNat_lt_two256 (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2)
  norm_num [Secp256k1.Scalar.Basic.CARD] at hvalue hout hge
  have hvaluez :
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat : Int) +
          115792089237316195423570985008687907853269984665640564039457584007913129639936 * c =
        (Repr.ofLimbs d0 d1 d2 d3).toNat +
          432420386565659656852420866394968145599 := by exact_mod_cast hvalue
  have houtz : ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat : Int) <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    exact_mod_cast hout
  have hgez : (115792089237316195423570985008687907852837564279074904382605163141518161494337 : Int) ≤
      (Repr.ofLimbs d0 d1 d2 d3).toNat := by exact_mod_cast hge
  have hcz : (c : Int) ≤ 1 := by exact_mod_cast hc
  have heqz :
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat : Int) +
          115792089237316195423570985008687907852837564279074904382605163141518161494337 =
        (Repr.ofLimbs d0 d1 d2 d3).toNat := by
    omega
  have heq :
      (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat +
          Secp256k1.Scalar.Basic.CARD =
        (Repr.ofLimbs d0 d1 d2 d3).toNat := by
    norm_num [Secp256k1.Scalar.Basic.CARD]
    exact_mod_cast heqz
  dsimp only
  exact Nat.eq_sub_of_add_eq heq

/-- Reducing a value below the scalar order adds `2^256 - n` without wrapping. -/
theorem reduceRaw_true_of_lt (d0 d1 d2 d3 : UInt64)
    (hlt : (Repr.ofLimbs d0 d1 d2 d3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := reduceRaw d0 d1 d2 d3 true
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat =
      (Repr.ofLimbs d0 d1 d2 d3).toNat +
        (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) := by
  obtain ⟨c, hc, hvalue⟩ := reduceRaw_true_value d0 d1 d2 d3
  let r := reduceRaw d0 d1 d2 d3 true
  have hout := Repr.toNat_lt_two256 (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2)
  norm_num [Secp256k1.Scalar.Basic.CARD] at hvalue hout hlt ⊢
  omega

/-- Canonicalizing arbitrary four-limb input produces a value below the scalar order. -/
theorem canonicalizeRaw_lt (d0 d1 d2 d3 : UInt64) :
    let r := canonicalizeRaw d0 d1 d2 d3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD := by
  let x := Repr.ofLimbs d0 d1 d2 d3
  have hcheck := checkOverflowRaw_eq_decide d0 d1 d2 d3
  change checkOverflowRaw d0 d1 d2 d3 =
    decide (x.toNat >= Secp256k1.Scalar.Basic.CARD) at hcheck
  by_cases hge : Secp256k1.Scalar.Basic.CARD <= x.toNat
  · have hflag : checkOverflowRaw d0 d1 d2 d3 = true := by
      rw [hcheck]
      simp [hge]
    simp only [canonicalizeRaw, hflag]
    rw [reduceRaw_true_of_ge d0 d1 d2 d3 hge]
    have hx := Repr.toNat_lt_two256 x
    dsimp only [x] at hx hge ⊢
    norm_num [Secp256k1.Scalar.Basic.CARD] at hx hge ⊢
    omega
  · have hlt : x.toNat < Secp256k1.Scalar.Basic.CARD := Nat.lt_of_not_ge hge
    have hflag : checkOverflowRaw d0 d1 d2 d3 = false := by
      rw [hcheck]
      simp [hlt]
    simpa [canonicalizeRaw, hflag, reduceRaw, x] using hlt

/-- Canonicalization preserves the input's value in the scalar field. -/
theorem canonicalizeRaw_cast (d0 d1 d2 d3 : UInt64) :
    let r := canonicalizeRaw d0 d1 d2 d3
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
      Secp256k1.Scalar.Basic.Field) =
      ((Repr.ofLimbs d0 d1 d2 d3).toNat : Secp256k1.Scalar.Basic.Field) := by
  let x := Repr.ofLimbs d0 d1 d2 d3
  have hcheck := checkOverflowRaw_eq_decide d0 d1 d2 d3
  change checkOverflowRaw d0 d1 d2 d3 =
    decide (x.toNat >= Secp256k1.Scalar.Basic.CARD) at hcheck
  by_cases hge : Secp256k1.Scalar.Basic.CARD <= x.toNat
  · have hflag : checkOverflowRaw d0 d1 d2 d3 = true := by
      rw [hcheck]
      simp [hge]
    simp only [canonicalizeRaw, hflag]
    rw [reduceRaw_true_of_ge d0 d1 d2 d3 hge]
    rw [Nat.cast_sub hge]
    have hcard :
        (Secp256k1.Scalar.Basic.CARD : Secp256k1.Scalar.Basic.Field) = 0 :=
      CharP.cast_eq_zero _ _
    rw [hcard, sub_zero]
  · have hlt : x.toNat < Secp256k1.Scalar.Basic.CARD := Nat.lt_of_not_ge hge
    have hflag : checkOverflowRaw d0 d1 d2 d3 = false := by
      rw [hcheck]
      simp [hlt]
    simp [canonicalizeRaw, hflag, reduceRaw]

/-- Addition modulo the scalar order. -/
@[inline] def addModRaw (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Limbs4 :=
  let (s0, s1, s2, s3, carry) := addRaw a0 a1 a2 a3 b0 b1 b2 b3
  reduceRaw s0 s1 s2 s3 (carry != 0 || checkOverflowRaw s0 s1 s2 s3)

/-- Correct a wrapped four-limb subtraction by adding the scalar order on borrow. -/
@[inline] def finishSubRaw (s0 s1 s2 s3 borrow : UInt64) : Limbs4 :=
  if borrow == 0 then
    (s0, s1, s2, s3)
  else
    let (r0, r1, r2, r3, _) := addRaw s0 s1 s2 s3 N_0 N_1 N_2 N_3
    (r0, r1, r2, r3)

/-- A subtraction without a final borrow needs no modular correction. -/
@[simp] theorem finishSubRaw_zero (s0 s1 s2 s3 : UInt64) :
    finishSubRaw s0 s1 s2 s3 0 = (s0, s1, s2, s3) := by
  simp only [finishSubRaw, beq_self_eq_true, if_true]

/-- A subtraction with a nonzero final borrow is corrected by adding the modulus. -/
theorem finishSubRaw_of_ne_zero (s0 s1 s2 s3 borrow : UInt64)
    (hborrow : borrow ≠ 0) :
    finishSubRaw s0 s1 s2 s3 borrow =
      let r := addRaw s0 s1 s2 s3 N_0 N_1 N_2 N_3
      (r.1, r.2.1, r.2.2.1, r.2.2.2.1) := by
  simp only [finishSubRaw, beq_iff_eq, hborrow, if_false]

/-- Subtraction modulo the scalar order. -/
@[inline] def subModRaw (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Limbs4 :=
  let (s0, s1, s2, s3, borrow) := subRaw a0 a1 a2 a3 b0 b1 b2 b3
  finishSubRaw s0 s1 s2 s3 borrow

/-- Expose modular subtraction as raw subtraction followed by borrow correction. -/
theorem subModRaw_eq_finish (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    subModRaw a0 a1 a2 a3 b0 b1 b2 b3 =
      let s := subRaw a0 a1 a2 a3 b0 b1 b2 b3
      finishSubRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 := rfl

/-- Negation modulo the scalar order. -/
@[inline] def negRaw (a0 a1 a2 a3 : UInt64) : Limbs4 :=
  let nonzero : UInt64 := if isZeroRaw a0 a1 a2 a3 then 0 else 0xffffffffffffffff
  let (d0, c) := addCarry (~~~a0) (N_0 + 1) 0
  let (d1, c) := addCarry (~~~a1) N_1 c
  let (d2, c) := addCarry (~~~a2) N_2 c
  let (d3, _) := addCarry (~~~a3) N_3 c
  (d0 &&& nonzero, d1 &&& nonzero, d2 &&& nonzero, d3 &&& nonzero)

/-- Add one product and emit one column using the fast two-word macros. -/
@[inline] private def mulColumnFast
    (c0 c1 c2 a b : UInt64) : Limbs4 :=
  let s := mulAddFast c0 c1 c2 a b
  extractFast s.1 s.2.1 s.2.2

/-- Add two products and emit one multiplication column. -/
@[inline] private def mulColumn2
    (c0 c1 c2 a0 b0 a1 b1 : UInt64) : Limbs4 :=
  let s0 := mulAdd c0 c1 c2 a0 b0
  let s1 := mulAdd s0.1 s0.2.1 s0.2.2 a1 b1
  extract s1.1 s1.2.1 s1.2.2

/-- Add three products and emit one multiplication column. -/
@[inline] private def mulColumn3
    (c0 c1 c2 a0 b0 a1 b1 a2 b2 : UInt64) : Limbs4 :=
  let s0 := mulAdd c0 c1 c2 a0 b0
  let s1 := mulAdd s0.1 s0.2.1 s0.2.2 a1 b1
  let s2 := mulAdd s1.1 s1.2.1 s1.2.2 a2 b2
  extract s2.1 s2.2.1 s2.2.2

/-- Add four products and emit one multiplication column. -/
@[inline] private def mulColumn4
    (c0 c1 c2 a0 b0 a1 b1 a2 b2 a3 b3 : UInt64) : Limbs4 :=
  let s0 := mulAdd c0 c1 c2 a0 b0
  let s1 := mulAdd s0.1 s0.2.1 s0.2.2 a1 b1
  let s2 := mulAdd s1.1 s1.2.1 s1.2.2 a2 b2
  let s3 := mulAdd s2.1 s2.2.1 s2.2.2 a3 b3
  extract s3.1 s3.2.1 s3.2.2

/-- C `secp256k1_scalar_mul_512`, non-asm path. -/
@[inline] def mul512Raw (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Limbs8 :=
  let e0 := mulColumnFast 0 0 0 a0 b0
  let e1 := mulColumn2 e0.2.1 e0.2.2.1 e0.2.2.2 a0 b1 a1 b0
  let e2 := mulColumn3 e1.2.1 e1.2.2.1 e1.2.2.2 a0 b2 a1 b1 a2 b0
  let e3 := mulColumn4 e2.2.1 e2.2.2.1 e2.2.2.2 a0 b3 a1 b2 a2 b1 a3 b0
  let e4 := mulColumn3 e3.2.1 e3.2.2.1 e3.2.2.2 a1 b3 a2 b2 a3 b1
  let e5 := mulColumn2 e4.2.1 e4.2.2.1 e4.2.2.2 a2 b3 a3 b2
  let e6 := mulColumnFast e5.2.1 e5.2.2.1 e5.2.2.2 a3 b3
  (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e6.2.1)

/-- Expose the seven column results without unfolding their accumulator kernels. -/
private theorem mul512Raw_columns (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    mul512Raw a0 a1 a2 a3 b0 b1 b2 b3 =
      let e0 := mulColumnFast 0 0 0 a0 b0
      let e1 := mulColumn2 e0.2.1 e0.2.2.1 e0.2.2.2 a0 b1 a1 b0
      let e2 := mulColumn3 e1.2.1 e1.2.2.1 e1.2.2.2 a0 b2 a1 b1 a2 b0
      let e3 := mulColumn4 e2.2.1 e2.2.2.1 e2.2.2.2 a0 b3 a1 b2 a2 b1 a3 b0
      let e4 := mulColumn3 e3.2.1 e3.2.2.1 e3.2.2.2 a1 b3 a2 b2 a3 b1
      let e5 := mulColumn2 e4.2.1 e4.2.2.1 e4.2.2.2 a2 b3 a3 b2
      let e6 := mulColumnFast e5.2.1 e5.2.2.1 e5.2.2.2 a3 b3
      (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e6.2.1) := rfl

/-- Natural-number value of eight little-endian 64-bit limbs. -/
private def limbs8ToNat (x : Limbs8) : Nat :=
  x.1.toNat + 2 ^ 64 * x.2.1.toNat + 2 ^ 128 * x.2.2.1.toNat +
    2 ^ 192 * x.2.2.2.1.toNat + 2 ^ 256 * x.2.2.2.2.1.toNat +
    2 ^ 320 * x.2.2.2.2.2.1.toNat + 2 ^ 384 * x.2.2.2.2.2.2.1.toNat +
    2 ^ 448 * x.2.2.2.2.2.2.2.toNat

/-- Collapse two sequential accumulator additions into one value equation. -/
private theorem addChain2 {base s1 s2 x y : Nat}
    (h1 : s1 = base + x) (h2 : s2 = s1 + y) :
    s2 = base + (x + y) := by
  omega

/-- Collapse three sequential accumulator additions into one value equation. -/
private theorem addChain3 {base s1 s2 s3 x y z : Nat}
    (h1 : s1 = base + x) (h2 : s2 = s1 + y) (h3 : s3 = s2 + z) :
    s3 = base + (x + y + z) := by
  omega

/-- Collapse four sequential accumulator additions into one value equation. -/
private theorem addChain4 {base s1 s2 s3 s4 w x y z : Nat}
    (h1 : s1 = base + w) (h2 : s2 = s1 + x)
    (h3 : s3 = s2 + y) (h4 : s4 = s3 + z) :
    s4 = base + (w + x + y + z) := by
  omega

/-- Append one emitted radix-`2^64` column to an accumulated value equation. -/
private theorem appendRadixColumn
    {pref oldTail digit newAcc newTail rhs added shift : Nat}
    (hprefix : pref + shift * oldTail = rhs)
    (hacc : newAcc = oldTail + added)
    (hextract : digit + 2 ^ 64 * newTail = newAcc) :
    pref + shift * digit + (shift * 2 ^ 64) * newTail =
      rhs + shift * added := by
  calc
    pref + shift * digit + (shift * 2 ^ 64) * newTail =
        pref + shift * (digit + 2 ^ 64 * newTail) := by ring
    _ = pref + shift * newAcc := by rw [hextract]
    _ = pref + shift * (oldTail + added) := by rw [hacc]
    _ = (pref + shift * oldTail) + shift * added := by ring
    _ = rhs + shift * added := by rw [hprefix]

/-- Append a column whose emitted-word equation already includes its additions. -/
private theorem appendCompletedColumn
    {pref oldTail digit newTail rhs added shift : Nat}
    (hprefix : pref + shift * oldTail = rhs)
    (hcolumn : digit + 2 ^ 64 * newTail = oldTail + added) :
    pref + shift * digit + (shift * 2 ^ 64) * newTail =
      rhs + shift * added := by
  exact appendRadixColumn hprefix rfl hcolumn

/-- A fast multiplication column preserves its exact accumulator value. -/
private theorem mulColumnFast_value (c0 c1 c2 a b : UInt64)
    (hc2 : c2 = 0)
    (hbound : accToNat c0 c1 c2 + a.toNat * b.toNat < 2 ^ 128) :
    let r := mulColumnFast c0 c1 c2 a b
    r.1.toNat + 2 ^ 64 * accToNat r.2.1 r.2.2.1 r.2.2.2 =
      accToNat c0 c1 c2 + a.toNat * b.toNat := by
  let s := mulAddFast c0 c1 c2 a b
  have hs : accToNat s.1 s.2.1 s.2.2 =
      accToNat c0 c1 c2 + a.toNat * b.toNat := by
    simpa [s] using mulAddFast_value c0 c1 c2 a b hc2 hbound
  have hs2 : s.2.2 = 0 := by
    simp [s, mulAddFast, hc2]
  have he := extractFast_value s.1 s.2.1 s.2.2 hs2
  change (extractFast s.1 s.2.1 s.2.2).1.toNat +
      2 ^ 64 * accToNat (extractFast s.1 s.2.1 s.2.2).2.1
        (extractFast s.1 s.2.1 s.2.2).2.2.1
        (extractFast s.1 s.2.1 s.2.2).2.2.2 = _
  exact he.trans hs

/-- A fast column leaves only one carry word. -/
private theorem mulColumnFast_tail (c0 c1 c2 a b : UInt64) :
    let r := mulColumnFast c0 c1 c2 a b
    r.2.2.1 = 0 ∧ r.2.2.2 = 0 := by
  simp [mulColumnFast, extractFast]

/-- A two-product multiplication column preserves its exact accumulator value. -/
private theorem mulColumn2_value (c0 c1 c2 a0 b0 a1 b1 : UInt64)
    (hacc : accToNat c0 c1 c2 < 2 ^ 128) :
    let r := mulColumn2 c0 c1 c2 a0 b0 a1 b1
    r.1.toNat + 2 ^ 64 * accToNat r.2.1 r.2.2.1 r.2.2.2 =
      accToNat c0 c1 c2 + (a0.toNat * b0.toNat + a1.toNat * b1.toNat) := by
  let s0 := mulAdd c0 c1 c2 a0 b0
  let s1 := mulAdd s0.1 s0.2.1 s0.2.2 a1 b1
  have hp0 := wordProduct_lt_two128 a0 b0
  have hp1 := wordProduct_lt_two128 a1 b1
  have hs0 : accToNat s0.1 s0.2.1 s0.2.2 =
      accToNat c0 c1 c2 + a0.toNat * b0.toNat := by
    simpa [s0] using mulAdd_value c0 c1 c2 a0 b0 (by omega)
  have hs1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat s0.1 s0.2.1 s0.2.2 + a1.toNat * b1.toNat := by
    simpa [s1] using mulAdd_value s0.1 s0.2.1 s0.2.2 a1 b1 (by rw [hs0]; omega)
  have he := extract_value s1.1 s1.2.1 s1.2.2
  change (extract s1.1 s1.2.1 s1.2.2).1.toNat +
      2 ^ 64 * accToNat (extract s1.1 s1.2.1 s1.2.2).2.1
        (extract s1.1 s1.2.1 s1.2.2).2.2.1
        (extract s1.1 s1.2.1 s1.2.2).2.2.2 = _
  exact he.trans (addChain2 hs0 hs1)

/-- A two-product column shifts into a two-word carry. -/
private theorem mulColumn2_tail (c0 c1 c2 a0 b0 a1 b1 : UInt64) :
    let r := mulColumn2 c0 c1 c2 a0 b0 a1 b1
    r.2.2.2 = 0 := by
  rfl

/-- A three-product multiplication column preserves its exact accumulator value. -/
private theorem mulColumn3_value (c0 c1 c2 a0 b0 a1 b1 a2 b2 : UInt64)
    (hacc : accToNat c0 c1 c2 < 2 ^ 128) :
    let r := mulColumn3 c0 c1 c2 a0 b0 a1 b1 a2 b2
    r.1.toNat + 2 ^ 64 * accToNat r.2.1 r.2.2.1 r.2.2.2 =
      accToNat c0 c1 c2 +
        (a0.toNat * b0.toNat + a1.toNat * b1.toNat + a2.toNat * b2.toNat) := by
  let s0 := mulAdd c0 c1 c2 a0 b0
  let s1 := mulAdd s0.1 s0.2.1 s0.2.2 a1 b1
  let s2 := mulAdd s1.1 s1.2.1 s1.2.2 a2 b2
  have hp0 := wordProduct_lt_two128 a0 b0
  have hp1 := wordProduct_lt_two128 a1 b1
  have hp2 := wordProduct_lt_two128 a2 b2
  have hs0 : accToNat s0.1 s0.2.1 s0.2.2 =
      accToNat c0 c1 c2 + a0.toNat * b0.toNat := by
    simpa [s0] using mulAdd_value c0 c1 c2 a0 b0 (by omega)
  have hs1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat s0.1 s0.2.1 s0.2.2 + a1.toNat * b1.toNat := by
    simpa [s1] using mulAdd_value s0.1 s0.2.1 s0.2.2 a1 b1 (by rw [hs0]; omega)
  have hs2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat s1.1 s1.2.1 s1.2.2 + a2.toNat * b2.toNat := by
    simpa [s2] using mulAdd_value s1.1 s1.2.1 s1.2.2 a2 b2
      (by rw [hs1, hs0]; omega)
  have he := extract_value s2.1 s2.2.1 s2.2.2
  change (extract s2.1 s2.2.1 s2.2.2).1.toNat +
      2 ^ 64 * accToNat (extract s2.1 s2.2.1 s2.2.2).2.1
        (extract s2.1 s2.2.1 s2.2.2).2.2.1
        (extract s2.1 s2.2.1 s2.2.2).2.2.2 = _
  exact he.trans (addChain3 hs0 hs1 hs2)

/-- A three-product column shifts into a two-word carry. -/
private theorem mulColumn3_tail (c0 c1 c2 a0 b0 a1 b1 a2 b2 : UInt64) :
    let r := mulColumn3 c0 c1 c2 a0 b0 a1 b1 a2 b2
    r.2.2.2 = 0 := by
  rfl

/-- A four-product multiplication column preserves its exact accumulator value. -/
private theorem mulColumn4_value (c0 c1 c2 a0 b0 a1 b1 a2 b2 a3 b3 : UInt64)
    (hacc : accToNat c0 c1 c2 < 2 ^ 128) :
    let r := mulColumn4 c0 c1 c2 a0 b0 a1 b1 a2 b2 a3 b3
    r.1.toNat + 2 ^ 64 * accToNat r.2.1 r.2.2.1 r.2.2.2 =
      accToNat c0 c1 c2 + (a0.toNat * b0.toNat + a1.toNat * b1.toNat +
        a2.toNat * b2.toNat + a3.toNat * b3.toNat) := by
  let s0 := mulAdd c0 c1 c2 a0 b0
  let s1 := mulAdd s0.1 s0.2.1 s0.2.2 a1 b1
  let s2 := mulAdd s1.1 s1.2.1 s1.2.2 a2 b2
  let s3 := mulAdd s2.1 s2.2.1 s2.2.2 a3 b3
  have hp0 := wordProduct_lt_two128 a0 b0
  have hp1 := wordProduct_lt_two128 a1 b1
  have hp2 := wordProduct_lt_two128 a2 b2
  have hp3 := wordProduct_lt_two128 a3 b3
  have hs0 : accToNat s0.1 s0.2.1 s0.2.2 =
      accToNat c0 c1 c2 + a0.toNat * b0.toNat := by
    simpa [s0] using mulAdd_value c0 c1 c2 a0 b0 (by omega)
  have hs1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat s0.1 s0.2.1 s0.2.2 + a1.toNat * b1.toNat := by
    simpa [s1] using mulAdd_value s0.1 s0.2.1 s0.2.2 a1 b1 (by rw [hs0]; omega)
  have hs2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat s1.1 s1.2.1 s1.2.2 + a2.toNat * b2.toNat := by
    simpa [s2] using mulAdd_value s1.1 s1.2.1 s1.2.2 a2 b2
      (by rw [hs1, hs0]; omega)
  have hs3 : accToNat s3.1 s3.2.1 s3.2.2 =
      accToNat s2.1 s2.2.1 s2.2.2 + a3.toNat * b3.toNat := by
    simpa [s3] using mulAdd_value s2.1 s2.2.1 s2.2.2 a3 b3
      (by rw [hs2, hs1, hs0]; omega)
  have he := extract_value s3.1 s3.2.1 s3.2.2
  change (extract s3.1 s3.2.1 s3.2.2).1.toNat +
      2 ^ 64 * accToNat (extract s3.1 s3.2.1 s3.2.2).2.1
        (extract s3.1 s3.2.1 s3.2.2).2.2.1
        (extract s3.1 s3.2.1 s3.2.2).2.2.2 = _
  exact he.trans (addChain4 hs0 hs1 hs2 hs3)

/-- A four-product column shifts into a two-word carry. -/
private theorem mulColumn4_tail (c0 c1 c2 a0 b0 a1 b1 a2 b2 a3 b3 : UInt64) :
    let r := mulColumn4 c0 c1 c2 a0 b0 a1 b1 a2 b2 a3 b3
    r.2.2.2 = 0 := by
  rfl

/-- The libsecp256k1 multiplication schedule emits the exact 512-bit product. -/
theorem mul512Raw_value (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    limbs8ToNat (mul512Raw a0 a1 a2 a3 b0 b1 b2 b3) =
      (Repr.ofLimbs a0 a1 a2 a3).toNat *
        (Repr.ofLimbs b0 b1 b2 b3).toNat := by
  let p00 := a0.toNat * b0.toNat
  let p01 := a0.toNat * b1.toNat
  let p10 := a1.toNat * b0.toNat
  let p02 := a0.toNat * b2.toNat
  let p11 := a1.toNat * b1.toNat
  let p20 := a2.toNat * b0.toNat
  let p03 := a0.toNat * b3.toNat
  let p12 := a1.toNat * b2.toNat
  let p21 := a2.toNat * b1.toNat
  let p30 := a3.toNat * b0.toNat
  let p13 := a1.toNat * b3.toNat
  let p22 := a2.toNat * b2.toNat
  let p31 := a3.toNat * b1.toNat
  let p23 := a2.toNat * b3.toNat
  let p32 := a3.toNat * b2.toNat
  let p33 := a3.toNat * b3.toNat
  generalize h_e0 : mulColumnFast 0 0 0 a0 b0 = e0
  have he0 : e0.1.toNat + 2 ^ 64 * accToNat e0.2.1 e0.2.2.1 e0.2.2.2 = p00 := by
    have h := mulColumnFast_value 0 0 0 a0 b0 rfl
      (by simpa [accToNat] using wordProduct_lt_two128 a0 b0)
    rw [h_e0] at h
    simpa only [p00, accToNat, UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero,
      Nat.zero_add] using h
  have he0bound : accToNat e0.2.1 e0.2.2.1 e0.2.2.2 < 2 ^ 64 := by
    have hz := mulColumnFast_tail 0 0 0 a0 b0
    rw [h_e0] at hz
    simpa only [hz.1, hz.2] using accToNat_lt_two64 e0.2.1
  generalize h_e1 : mulColumn2 e0.2.1 e0.2.2.1 e0.2.2.2 a0 b1 a1 b0 = e1
  have he1 : e1.1.toNat + 2 ^ 64 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
      accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + (p01 + p10) := by
    have h := mulColumn2_value e0.2.1 e0.2.2.1 e0.2.2.2 a0 b1 a1 b0
      (lt_trans he0bound (by norm_num))
    rw [h_e1] at h
    simpa only [p01, p10] using h
  have he1bound : accToNat e1.2.1 e1.2.2.1 e1.2.2.2 < 2 ^ 128 := by
    have hz := mulColumn2_tail e0.2.1 e0.2.2.1 e0.2.2.2 a0 b1 a1 b0
    rw [h_e1] at hz
    simpa only [hz] using accToNat_lt_two128 e1.2.1 e1.2.2.1
  generalize h_e2 : mulColumn3 e1.2.1 e1.2.2.1 e1.2.2.2 a0 b2 a1 b1 a2 b0 = e2
  have he2 : e2.1.toNat + 2 ^ 64 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
      accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + (p02 + p11 + p20) := by
    have h := mulColumn3_value e1.2.1 e1.2.2.1 e1.2.2.2
      a0 b2 a1 b1 a2 b0 he1bound
    rw [h_e2] at h
    simpa only [p02, p11, p20] using h
  have he2bound : accToNat e2.2.1 e2.2.2.1 e2.2.2.2 < 2 ^ 128 := by
    have hz := mulColumn3_tail e1.2.1 e1.2.2.1 e1.2.2.2 a0 b2 a1 b1 a2 b0
    rw [h_e2] at hz
    simpa only [hz] using accToNat_lt_two128 e2.2.1 e2.2.2.1
  generalize h_e3 :
    mulColumn4 e2.2.1 e2.2.2.1 e2.2.2.2 a0 b3 a1 b2 a2 b1 a3 b0 = e3
  have he3 : e3.1.toNat + 2 ^ 64 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + (p03 + p12 + p21 + p30) := by
    have h := mulColumn4_value e2.2.1 e2.2.2.1 e2.2.2.2
      a0 b3 a1 b2 a2 b1 a3 b0 he2bound
    rw [h_e3] at h
    simpa only [p03, p12, p21, p30] using h
  have he3bound : accToNat e3.2.1 e3.2.2.1 e3.2.2.2 < 2 ^ 128 := by
    have hz := mulColumn4_tail e2.2.1 e2.2.2.1 e2.2.2.2
      a0 b3 a1 b2 a2 b1 a3 b0
    rw [h_e3] at hz
    simpa only [hz] using accToNat_lt_two128 e3.2.1 e3.2.2.1
  generalize h_e4 : mulColumn3 e3.2.1 e3.2.2.1 e3.2.2.2 a1 b3 a2 b2 a3 b1 = e4
  have he4 : e4.1.toNat + 2 ^ 64 * accToNat e4.2.1 e4.2.2.1 e4.2.2.2 =
      accToNat e3.2.1 e3.2.2.1 e3.2.2.2 + (p13 + p22 + p31) := by
    have h := mulColumn3_value e3.2.1 e3.2.2.1 e3.2.2.2
      a1 b3 a2 b2 a3 b1 he3bound
    rw [h_e4] at h
    simpa only [p13, p22, p31] using h
  have he4bound : accToNat e4.2.1 e4.2.2.1 e4.2.2.2 < 2 ^ 128 := by
    have hz := mulColumn3_tail e3.2.1 e3.2.2.1 e3.2.2.2 a1 b3 a2 b2 a3 b1
    rw [h_e4] at hz
    simpa only [hz] using accToNat_lt_two128 e4.2.1 e4.2.2.1
  generalize h_e5 : mulColumn2 e4.2.1 e4.2.2.1 e4.2.2.2 a2 b3 a3 b2 = e5
  have he5 : e5.1.toNat + 2 ^ 64 * accToNat e5.2.1 e5.2.2.1 e5.2.2.2 =
      accToNat e4.2.1 e4.2.2.1 e4.2.2.2 + (p23 + p32) := by
    have h := mulColumn2_value e4.2.1 e4.2.2.1 e4.2.2.2 a2 b3 a3 b2 he4bound
    rw [h_e5] at h
    simpa only [p23, p32] using h
  have hpartial1 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat +
          2 ^ 128 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
        p00 + 2 ^ 64 * (p01 + p10) := by
    have h := appendCompletedColumn (shift := 2 ^ 64) he0 he1
    norm_num at h ⊢
    exact h
  have hpartial2 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
        p00 + 2 ^ 64 * (p01 + p10) + 2 ^ 128 * (p02 + p11 + p20) := by
    have h := appendCompletedColumn (shift := 2 ^ 128) hpartial1 he2
    norm_num at h ⊢
    exact h
  have hpartial3 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat +
          2 ^ 256 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
        p00 + 2 ^ 64 * (p01 + p10) + 2 ^ 128 * (p02 + p11 + p20) +
          2 ^ 192 * (p03 + p12 + p21 + p30) := by
    have h := appendCompletedColumn (shift := 2 ^ 192) hpartial2 he3
    norm_num at h ⊢
    exact h
  have hpartial4 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat + 2 ^ 256 * e4.1.toNat +
          2 ^ 320 * accToNat e4.2.1 e4.2.2.1 e4.2.2.2 =
        p00 + 2 ^ 64 * (p01 + p10) + 2 ^ 128 * (p02 + p11 + p20) +
          2 ^ 192 * (p03 + p12 + p21 + p30) +
          2 ^ 256 * (p13 + p22 + p31) := by
    have h := appendCompletedColumn (shift := 2 ^ 256) hpartial3 he4
    norm_num at h ⊢
    exact h
  have hpartial :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat + 2 ^ 256 * e4.1.toNat + 2 ^ 320 * e5.1.toNat +
          2 ^ 384 * accToNat e5.2.1 e5.2.2.1 e5.2.2.2 =
        p00 + 2 ^ 64 * (p01 + p10) + 2 ^ 128 * (p02 + p11 + p20) +
          2 ^ 192 * (p03 + p12 + p21 + p30) + 2 ^ 256 * (p13 + p22 + p31) +
          2 ^ 320 * (p23 + p32) := by
    have h := appendCompletedColumn (shift := 2 ^ 320) hpartial4 he5
    norm_num at h ⊢
    exact h
  let av := (Repr.ofLimbs a0 a1 a2 a3).toNat
  let bv := (Repr.ofLimbs b0 b1 b2 b3).toNat
  have hexpand : av * bv =
      p00 + 2 ^ 64 * (p01 + p10) + 2 ^ 128 * (p02 + p11 + p20) +
        2 ^ 192 * (p03 + p12 + p21 + p30) + 2 ^ 256 * (p13 + p22 + p31) +
        2 ^ 320 * (p23 + p32) + 2 ^ 384 * p33 := by
    simp only [av, bv, Repr.toNat, Repr.ofLimbs, p00, p01, p10, p02, p11, p20,
      p03, p12, p21, p30, p13, p22, p31, p23, p32, p33]
    norm_num [TWO64, TWO128, TWO192]
    ring
  have hav := Repr.toNat_lt_two256 (Repr.ofLimbs a0 a1 a2 a3)
  have hbv := Repr.toNat_lt_two256 (Repr.ofLimbs b0 b1 b2 b3)
  have hab : av * bv < 2 ^ 512 := by
    change av < 2 ^ 256 at hav
    change bv < 2 ^ 256 at hbv
    calc
      av * bv < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul_of_lt_of_lt hav hbv
      _ = 2 ^ 512 := two_pow_512.symm
  have hlastBound : accToNat e5.2.1 e5.2.2.1 e5.2.2.2 + p33 < 2 ^ 128 := by
    norm_num at hpartial hexpand hab ⊢
    omega
  generalize h_e6 : mulColumnFast e5.2.1 e5.2.2.1 e5.2.2.2 a3 b3 = e6
  have he6 : e6.1.toNat + 2 ^ 64 * accToNat e6.2.1 e6.2.2.1 e6.2.2.2 =
      accToNat e5.2.1 e5.2.2.1 e5.2.2.2 + p33 := by
    have h := mulColumnFast_value e5.2.1 e5.2.2.1 e5.2.2.2 a3 b3
      (by
        have hz := mulColumn2_tail e4.2.1 e4.2.2.1 e4.2.2.2 a2 b3 a3 b2
        rw [h_e5] at hz
        exact hz) hlastBound
    rw [h_e6] at h
    simpa only [p33] using h
  have hfull :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat + 2 ^ 256 * e4.1.toNat + 2 ^ 320 * e5.1.toNat +
          2 ^ 384 * e6.1.toNat +
          2 ^ 448 * accToNat e6.2.1 e6.2.2.1 e6.2.2.2 = av * bv := by
    have h := appendCompletedColumn (shift := 2 ^ 384) hpartial he6
    norm_num at h hexpand ⊢
    omega
  have he6tail : accToNat e6.2.1 e6.2.2.1 e6.2.2.2 = e6.2.1.toNat := by
    have hz := mulColumnFast_tail e5.2.1 e5.2.2.1 e5.2.2.2 a3 b3
    rw [h_e6] at hz
    simp [accToNat, hz.1, hz.2]
  rw [he6tail] at hfull
  have hout : limbs8ToNat
      (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e6.2.1) = av * bv := by
    simpa only [limbs8ToNat] using hfull
  have hcolumns : mul512Raw a0 a1 a2 a3 b0 b1 b2 b3 =
      (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e6.2.1) := by
    simpa only [h_e0, h_e1, h_e2, h_e3, h_e4, h_e5, h_e6] using
      mul512Raw_columns a0 a1 a2 a3 b0 b1 b2 b3
  calc
    limbs8ToNat (mul512Raw a0 a1 a2 a3 b0 b1 b2 b3) =
        limbs8ToNat (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e6.1, e6.2.1) := by
      exact congrArg limbs8ToNat hcolumns
    _ = av * bv := hout

/-- Natural-number value of five little-endian 64-bit limbs. -/
private def limbs5ToNat (x : Limbs4Carry) : Nat :=
  (Repr.ofLimbs x.1 x.2.1 x.2.2.1 x.2.2.2.1).toNat +
    2 ^ 256 * x.2.2.2.2.toNat

/-- Final 258-to-256-bit reduction step from `secp256k1_scalar_reduce_512`.
    Returns `(r, c)`, where `c` is the final carry word. -/
@[inline] private def reduce258Raw
    (p0 p1 p2 p3 p4 : UInt64) : Limbs4Carry :=
  let (c0, c1, c2) := mulAddFast p0 0 0 N_C_0 p4
  let (r0, c0, c1, c2) := extractFast c0 c1 c2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 p1
  let (c0, c1, c2) := mulAddFast c0 c1 c2 N_C_1 p4
  let (r1, c0, c1, c2) := extractFast c0 c1 c2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 p2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 p4
  let (r2, c0, c1, c2) := extractFast c0 c1 c2
  let (c0, c1, _c2) := sumAddFast c0 c1 c2 p3
  (r0, r1, r2, c0, c1)

/-- Exact value equation for the final multiply-by-complement fold. -/
private theorem reduce258Raw_value (p0 p1 p2 p3 p4 : UInt64)
    (hinput : limbs5ToNat (p0, p1, p2, p3, p4) < 2 ^ 259) :
    limbs5ToNat (reduce258Raw p0 p1 p2 p3 p4) =
      (Repr.ofLimbs p0 p1 p2 p3).toNat +
        p4.toNat * (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) := by
  have hp0 := p0.toNat_lt_size
  have hp1 := p1.toNat_lt_size
  have hp2 := p2.toNat_lt_size
  have hp3 := p3.toNat_lt_size
  norm_num [UInt64.size] at hp0 hp1 hp2 hp3
  have hp4 : p4.toNat < 8 := by
    unfold limbs5ToNat Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192 at hinput
    norm_num at hinput ⊢
    omega
  let q0 := p4.toNat * N_C_0.toNat
  let q1 := p4.toNat * N_C_1.toNat
  have hq0 : q0 < 8 * 2 ^ 64 := by
    have hc := N_C_0.toNat_lt_size
    norm_num [UInt64.size] at hc
    dsimp [q0]
    nlinarith
  have hq1 : q1 < 8 * 2 ^ 64 := by
    have hc := N_C_1.toNat_lt_size
    norm_num [UInt64.size] at hc
    dsimp [q1]
    nlinarith

  let s0 := mulAddFast p0 0 0 N_C_0 p4
  have hs0 : accToNat s0.1 s0.2.1 s0.2.2 = p0.toNat + q0 := by
    simpa [s0, q0, Nat.mul_comm, accToNat] using
      mulAddFast_value p0 0 0 N_C_0 p4 rfl (by
        have h : p0.toNat + q0 < 2 ^ 128 := by omega
        simpa [accToNat, q0, Nat.mul_comm] using h)
  let e0 := extractFast s0.1 s0.2.1 s0.2.2
  have he0 : e0.1.toNat + 2 ^ 64 * accToNat e0.2.1 e0.2.2.1 e0.2.2.2 =
      accToNat s0.1 s0.2.1 s0.2.2 := by
    apply extractFast_value
    simp [s0, mulAddFast]
  have he0bound : accToNat e0.2.1 e0.2.2.1 e0.2.2.2 < 2 ^ 64 := by
    simpa [e0, extractFast] using accToNat_lt_two64 s0.2.1

  let s1z := sumAddFast e0.2.1 e0.2.2.1 e0.2.2.2 p1
  have hs1z : accToNat s1z.1 s1z.2.1 s1z.2.2 =
      accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + p1.toNat := by
    apply sumAddFast_value
    · simp [e0, extractFast]
    · omega
  let s1 := mulAddFast s1z.1 s1z.2.1 s1z.2.2 N_C_1 p4
  have hs1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat s1z.1 s1z.2.1 s1z.2.2 + q1 := by
    simpa [s1, q1, Nat.mul_comm] using
      mulAddFast_value s1z.1 s1z.2.1 s1z.2.2 N_C_1 p4
        (by simp [s1z, sumAddFast, e0, extractFast]) (by
          rw [hs1z]
          have h : accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + p1.toNat + q1 <
              2 ^ 128 := by omega
          simpa [q1, Nat.mul_comm] using h)
  let e1 := extractFast s1.1 s1.2.1 s1.2.2
  have he1 : e1.1.toNat + 2 ^ 64 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
      accToNat s1.1 s1.2.1 s1.2.2 := by
    apply extractFast_value
    simp [s1, mulAddFast, s1z, sumAddFast, e0, extractFast]
  have he1bound : accToNat e1.2.1 e1.2.2.1 e1.2.2.2 < 2 ^ 64 := by
    simpa [e1, extractFast] using accToNat_lt_two64 s1.2.1

  let s2z := sumAddFast e1.2.1 e1.2.2.1 e1.2.2.2 p2
  have hs2z : accToNat s2z.1 s2z.2.1 s2z.2.2 =
      accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + p2.toNat := by
    apply sumAddFast_value
    · simp [e1, extractFast]
    · omega
  let s2 := sumAddFast s2z.1 s2z.2.1 s2z.2.2 p4
  have hs2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat s2z.1 s2z.2.1 s2z.2.2 + p4.toNat := by
    apply sumAddFast_value
    · simp [s2z, sumAddFast, e1, extractFast]
    · rw [hs2z]
      omega
  let e2 := extractFast s2.1 s2.2.1 s2.2.2
  have he2 : e2.1.toNat + 2 ^ 64 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
      accToNat s2.1 s2.2.1 s2.2.2 := by
    apply extractFast_value
    simp [s2, sumAddFast, s2z, e1, extractFast]
  have he2bound : accToNat e2.2.1 e2.2.2.1 e2.2.2.2 < 2 ^ 64 := by
    simpa [e2, extractFast] using accToNat_lt_two64 s2.2.1

  let s3 := sumAddFast e2.2.1 e2.2.2.1 e2.2.2.2 p3
  have hs3 : accToNat s3.1 s3.2.1 s3.2.2 =
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + p3.toNat := by
    apply sumAddFast_value
    · simp [e2, extractFast]
    · omega
  have hs3shape : s3.2.2 = 0 := by
    simp [s3, sumAddFast, e2, extractFast]
  change limbs5ToNat (e0.1, e1.1, e2.1, s3.1, s3.2.1) = _
  unfold limbs5ToNat Repr.toNat Repr.ofLimbs
  have hcomp : 2 ^ 256 - Secp256k1.Scalar.Basic.CARD =
      N_C_0.toNat + 2 ^ 64 * N_C_1.toNat + 2 ^ 128 := by
    norm_num [N_C_0, N_C_1, Secp256k1.Scalar.Basic.CARD, UInt64.toNat_ofNat]
  rw [hcomp]
  norm_num [TWO64, TWO128, TWO192, accToNat] at he0 he1 he2 hs0 hs1z hs1 hs2z hs2 hs3 hs3shape ⊢
  dsimp [q0, q1] at hs0 hs1
  norm_num [N_C_0, N_C_1, UInt64.toNat_ofNat] at hs0 hs1 ⊢
  omega

/-- The final fold is below twice `2^256`, so its high word is a carry bit. -/
private theorem reduce258Raw_bound (p0 p1 p2 p3 p4 : UInt64)
    (hinput : limbs5ToNat (p0, p1, p2, p3, p4) < 2 ^ 259) :
    limbs5ToNat (reduce258Raw p0 p1 p2 p3 p4) < 2 ^ 257 := by
  rw [reduce258Raw_value _ _ _ _ _ hinput]
  have hp4 : p4.toNat < 8 := by
    unfold limbs5ToNat Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192 at hinput
    norm_num at hinput ⊢
    omega
  have hlow := Repr.toNat_lt_two256 (Repr.ofLimbs p0 p1 p2 p3)
  norm_num [Secp256k1.Scalar.Basic.CARD] at hlow hp4 ⊢
  omega

/-- The carry returned by the final fold is either zero or one. -/
private theorem reduce258Raw_carry_le_one (p0 p1 p2 p3 p4 : UInt64)
    (hinput : limbs5ToNat (p0, p1, p2, p3, p4) < 2 ^ 259) :
    (reduce258Raw p0 p1 p2 p3 p4).2.2.2.2.toNat ≤ 1 := by
  have hbound := reduce258Raw_bound p0 p1 p2 p3 p4 hinput
  unfold limbs5ToNat at hbound
  norm_num at hbound ⊢
  omega

/-- C `secp256k1_scalar_reduce_512`, non-asm path. -/
private abbrev Limbs7 :=
  UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64

/-- First libsecp256k1 reduction stage: fold the high 256 bits with
    `2^256 - n`, producing at most 385 bits. -/
@[inline] private def reduce512To385Raw
    (l0 l1 l2 l3 n0 n1 n2 n3 : UInt64) : Limbs7 :=
  let (c0, c1, c2) := mulAddFast l0 0 0 n0 N_C_0
  let (m0, c0, c1, c2) := extractFast c0 c1 c2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 l1
  let (c0, c1, c2) := mulAdd c0 c1 c2 n1 N_C_0
  let (c0, c1, c2) := mulAdd c0 c1 c2 n0 N_C_1
  let (m1, c0, c1, c2) := extract c0 c1 c2
  let (c0, c1, c2) := sumAdd c0 c1 c2 l2
  let (c0, c1, c2) := mulAdd c0 c1 c2 n2 N_C_0
  let (c0, c1, c2) := mulAdd c0 c1 c2 n1 N_C_1
  let (c0, c1, c2) := sumAdd c0 c1 c2 n0
  let (m2, c0, c1, c2) := extract c0 c1 c2
  let (c0, c1, c2) := sumAdd c0 c1 c2 l3
  let (c0, c1, c2) := mulAdd c0 c1 c2 n3 N_C_0
  let (c0, c1, c2) := mulAdd c0 c1 c2 n2 N_C_1
  let (c0, c1, c2) := sumAdd c0 c1 c2 n1
  let (m3, c0, c1, c2) := extract c0 c1 c2
  let (c0, c1, c2) := mulAdd c0 c1 c2 n3 N_C_1
  let (c0, c1, c2) := sumAdd c0 c1 c2 n2
  let (m4, c0, c1, c2) := extract c0 c1 c2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 n3
  let (m5, c0, _, _) := extractFast c0 c1 c2
  let m6 := c0
  (m0, m1, m2, m3, m4, m5, m6)

/-- Expose the six first-stage reduction columns without unfolding their kernels. -/
private theorem reduce512To385Raw_columns
    (l0 l1 l2 l3 n0 n1 n2 n3 : UInt64) :
    reduce512To385Raw l0 l1 l2 l3 n0 n1 n2 n3 =
      let s0 := mulAddFast l0 0 0 n0 N_C_0
      let e0 := extractFast s0.1 s0.2.1 s0.2.2
      let s1z := sumAddFast e0.2.1 e0.2.2.1 e0.2.2.2 l1
      let s1a := mulAdd s1z.1 s1z.2.1 s1z.2.2 n1 N_C_0
      let s1 := mulAdd s1a.1 s1a.2.1 s1a.2.2 n0 N_C_1
      let e1 := extract s1.1 s1.2.1 s1.2.2
      let s2z := sumAdd e1.2.1 e1.2.2.1 e1.2.2.2 l2
      let s2a := mulAdd s2z.1 s2z.2.1 s2z.2.2 n2 N_C_0
      let s2b := mulAdd s2a.1 s2a.2.1 s2a.2.2 n1 N_C_1
      let s2 := sumAdd s2b.1 s2b.2.1 s2b.2.2 n0
      let e2 := extract s2.1 s2.2.1 s2.2.2
      let s3z := sumAdd e2.2.1 e2.2.2.1 e2.2.2.2 l3
      let s3a := mulAdd s3z.1 s3z.2.1 s3z.2.2 n3 N_C_0
      let s3b := mulAdd s3a.1 s3a.2.1 s3a.2.2 n2 N_C_1
      let s3 := sumAdd s3b.1 s3b.2.1 s3b.2.2 n1
      let e3 := extract s3.1 s3.2.1 s3.2.2
      let s4a := mulAdd e3.2.1 e3.2.2.1 e3.2.2.2 n3 N_C_1
      let s4 := sumAdd s4a.1 s4a.2.1 s4a.2.2 n2
      let e4 := extract s4.1 s4.2.1 s4.2.2
      let s5 := sumAddFast e4.2.1 e4.2.2.1 e4.2.2.2 n3
      let e5 := extractFast s5.1 s5.2.1 s5.2.2
      (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e5.2.1) := rfl

/-- Natural-number value of seven little-endian 64-bit limbs. -/
private def limbs7ToNat (x : Limbs7) : Nat :=
  x.1.toNat + 2 ^ 64 * x.2.1.toNat + 2 ^ 128 * x.2.2.1.toNat +
    2 ^ 192 * x.2.2.2.1.toNat + 2 ^ 256 * x.2.2.2.2.1.toNat +
    2 ^ 320 * x.2.2.2.2.2.1.toNat + 2 ^ 384 * x.2.2.2.2.2.2.toNat

/-- Exact value equation for the first reduction stage. -/
private theorem reduce512To385Raw_value
    (l0 l1 l2 l3 n0 n1 n2 n3 : UInt64) :
    limbs7ToNat (reduce512To385Raw l0 l1 l2 l3 n0 n1 n2 n3) =
      (Repr.ofLimbs l0 l1 l2 l3).toNat +
        (Repr.ofLimbs n0 n1 n2 n3).toNat *
          (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) := by
  let q0 := n0.toNat * N_C_0.toNat
  let q1 := n1.toNat * N_C_0.toNat
  let q2 := n0.toNat * N_C_1.toNat
  let q3 := n2.toNat * N_C_0.toNat
  let q4 := n1.toNat * N_C_1.toNat
  let q5 := n3.toNat * N_C_0.toNat
  let q6 := n2.toNat * N_C_1.toNat
  let q7 := n3.toNat * N_C_1.toNat
  have hq0 : q0 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound n0
  have hq1 : q1 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound n1
  have hq2 : q2 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound n0
  have hq3 : q3 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound n2
  have hq4 : q4 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound n1
  have hq5 : q5 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound n3
  have hq6 : q6 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound n2
  have hq7 : q7 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound n3
  norm_num [N_C_0, N_C_1, UInt64.toNat_ofNat] at hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7
  have hl0 := l0.toNat_lt_size
  have hl1 := l1.toNat_lt_size
  have hl2 := l2.toNat_lt_size
  have hl3 := l3.toNat_lt_size
  have hn0 := n0.toNat_lt_size
  have hn1 := n1.toNat_lt_size
  have hn2 := n2.toNat_lt_size
  have hn3 := n3.toNat_lt_size
  norm_num [UInt64.size] at hl0 hl1 hl2 hl3 hn0 hn1 hn2 hn3

  generalize h_s0 : mulAddFast l0 0 0 n0 N_C_0 = s0
  have hs0 : accToNat s0.1 s0.2.1 s0.2.2 = l0.toNat + q0 := by
    rw [← h_s0]
    apply mulAddFast_value
    · rfl
    · change l0.toNat + q0 < 2 ^ 128
      omega
  generalize h_e0 : extractFast s0.1 s0.2.1 s0.2.2 = e0
  have he0 : e0.1.toNat + 2 ^ 64 * accToNat e0.2.1 e0.2.2.1 e0.2.2.2 =
      accToNat s0.1 s0.2.1 s0.2.2 := by
    have h := extractFast_value s0.1 s0.2.1 s0.2.2 (by
      rw [← h_s0]
      simp [mulAddFast])
    rw [h_e0] at h
    exact h
  have he0bound : accToNat e0.2.1 e0.2.2.1 e0.2.2.2 < 2 ^ 64 := by
    rw [← h_e0]
    simpa [extractFast] using accToNat_lt_two64 s0.2.1

  generalize h_s1z : sumAddFast e0.2.1 e0.2.2.1 e0.2.2.2 l1 = s1z
  have hs1z : accToNat s1z.1 s1z.2.1 s1z.2.2 =
      accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + l1.toNat := by
    rw [← h_s1z]
    apply sumAddFast_value
    · rw [← h_e0]
      simp [extractFast]
    · omega
  generalize h_s1a : mulAdd s1z.1 s1z.2.1 s1z.2.2 n1 N_C_0 = s1a
  have hs1a : accToNat s1a.1 s1a.2.1 s1a.2.2 =
      accToNat s1z.1 s1z.2.1 s1z.2.2 + q1 := by
    rw [← h_s1a]
    apply mulAdd_value
    rw [hs1z]
    change accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + l1.toNat + q1 < 2 ^ 192
    omega
  generalize h_s1 : mulAdd s1a.1 s1a.2.1 s1a.2.2 n0 N_C_1 = s1
  have hs1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat s1a.1 s1a.2.1 s1a.2.2 + q2 := by
    rw [← h_s1]
    apply mulAdd_value
    rw [hs1a, hs1z]
    change accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + l1.toNat + q1 + q2 < 2 ^ 192
    omega
  generalize h_e1 : extract s1.1 s1.2.1 s1.2.2 = e1
  have he1 : e1.1.toNat + 2 ^ 64 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
      accToNat s1.1 s1.2.1 s1.2.2 := by
    have h := extract_value s1.1 s1.2.1 s1.2.2
    rw [h_e1] at h
    exact h
  have he1bound : accToNat e1.2.1 e1.2.2.1 e1.2.2.2 < 2 ^ 128 := by
    rw [← h_e1]
    simpa [extract] using accToNat_lt_two128 s1.2.1 s1.2.2

  generalize h_s2z : sumAdd e1.2.1 e1.2.2.1 e1.2.2.2 l2 = s2z
  have hs2z : accToNat s2z.1 s2z.2.1 s2z.2.2 =
      accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + l2.toNat := by
    rw [← h_s2z]
    apply sumAdd_value
    omega
  generalize h_s2a : mulAdd s2z.1 s2z.2.1 s2z.2.2 n2 N_C_0 = s2a
  have hs2a : accToNat s2a.1 s2a.2.1 s2a.2.2 =
      accToNat s2z.1 s2z.2.1 s2z.2.2 + q3 := by
    rw [← h_s2a]
    apply mulAdd_value
    rw [hs2z]
    change accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + l2.toNat + q3 < 2 ^ 192
    omega
  generalize h_s2b : mulAdd s2a.1 s2a.2.1 s2a.2.2 n1 N_C_1 = s2b
  have hs2b : accToNat s2b.1 s2b.2.1 s2b.2.2 =
      accToNat s2a.1 s2a.2.1 s2a.2.2 + q4 := by
    rw [← h_s2b]
    apply mulAdd_value
    rw [hs2a, hs2z]
    change accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + l2.toNat + q3 + q4 < 2 ^ 192
    omega
  generalize h_s2 : sumAdd s2b.1 s2b.2.1 s2b.2.2 n0 = s2
  have hs2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat s2b.1 s2b.2.1 s2b.2.2 + n0.toNat := by
    rw [← h_s2]
    apply sumAdd_value
    rw [hs2b, hs2a, hs2z]
    omega
  generalize h_e2 : extract s2.1 s2.2.1 s2.2.2 = e2
  have he2 : e2.1.toNat + 2 ^ 64 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
      accToNat s2.1 s2.2.1 s2.2.2 := by
    have h := extract_value s2.1 s2.2.1 s2.2.2
    rw [h_e2] at h
    exact h
  have he2bound : accToNat e2.2.1 e2.2.2.1 e2.2.2.2 < 2 ^ 128 := by
    rw [← h_e2]
    simpa [extract] using accToNat_lt_two128 s2.2.1 s2.2.2

  generalize h_s3z : sumAdd e2.2.1 e2.2.2.1 e2.2.2.2 l3 = s3z
  have hs3z : accToNat s3z.1 s3z.2.1 s3z.2.2 =
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + l3.toNat := by
    rw [← h_s3z]
    apply sumAdd_value
    omega
  generalize h_s3a : mulAdd s3z.1 s3z.2.1 s3z.2.2 n3 N_C_0 = s3a
  have hs3a : accToNat s3a.1 s3a.2.1 s3a.2.2 =
      accToNat s3z.1 s3z.2.1 s3z.2.2 + q5 := by
    rw [← h_s3a]
    apply mulAdd_value
    rw [hs3z]
    change accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + l3.toNat + q5 < 2 ^ 192
    omega
  generalize h_s3b : mulAdd s3a.1 s3a.2.1 s3a.2.2 n2 N_C_1 = s3b
  have hs3b : accToNat s3b.1 s3b.2.1 s3b.2.2 =
      accToNat s3a.1 s3a.2.1 s3a.2.2 + q6 := by
    rw [← h_s3b]
    apply mulAdd_value
    rw [hs3a, hs3z]
    change accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + l3.toNat + q5 + q6 < 2 ^ 192
    omega
  generalize h_s3 : sumAdd s3b.1 s3b.2.1 s3b.2.2 n1 = s3
  have hs3 : accToNat s3.1 s3.2.1 s3.2.2 =
      accToNat s3b.1 s3b.2.1 s3b.2.2 + n1.toNat := by
    rw [← h_s3]
    apply sumAdd_value
    rw [hs3b, hs3a, hs3z]
    omega
  generalize h_e3 : extract s3.1 s3.2.1 s3.2.2 = e3
  have he3 : e3.1.toNat + 2 ^ 64 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
      accToNat s3.1 s3.2.1 s3.2.2 := by
    have h := extract_value s3.1 s3.2.1 s3.2.2
    rw [h_e3] at h
    exact h
  have he3bound : accToNat e3.2.1 e3.2.2.1 e3.2.2.2 < 2 ^ 128 := by
    rw [← h_e3]
    simpa [extract] using accToNat_lt_two128 s3.2.1 s3.2.2

  generalize h_s4a : mulAdd e3.2.1 e3.2.2.1 e3.2.2.2 n3 N_C_1 = s4a
  have hs4a : accToNat s4a.1 s4a.2.1 s4a.2.2 =
      accToNat e3.2.1 e3.2.2.1 e3.2.2.2 + q7 := by
    rw [← h_s4a]
    apply mulAdd_value
    change accToNat e3.2.1 e3.2.2.1 e3.2.2.2 + q7 < 2 ^ 192
    omega
  generalize h_s4 : sumAdd s4a.1 s4a.2.1 s4a.2.2 n2 = s4
  have hs4 : accToNat s4.1 s4.2.1 s4.2.2 =
      accToNat s4a.1 s4a.2.1 s4a.2.2 + n2.toNat := by
    rw [← h_s4]
    apply sumAdd_value
    rw [hs4a]
    omega
  generalize h_e4 : extract s4.1 s4.2.1 s4.2.2 = e4
  have he4 : e4.1.toNat + 2 ^ 64 * accToNat e4.2.1 e4.2.2.1 e4.2.2.2 =
      accToNat s4.1 s4.2.1 s4.2.2 := by
    have h := extract_value s4.1 s4.2.1 s4.2.2
    rw [h_e4] at h
    exact h

  have hpartial0 :
      e0.1.toNat + 2 ^ 64 * accToNat e0.2.1 e0.2.2.1 e0.2.2.2 =
        l0.toNat + q0 :=
    he0.trans hs0
  have hcol1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + (l1.toNat + q1 + q2) :=
    addChain3 hs1z hs1a hs1
  have hpartial1 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat +
          2 ^ 128 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
        l0.toNat + q0 + 2 ^ 64 * (l1.toNat + q1 + q2) := by
    have h := appendRadixColumn (shift := 2 ^ 64) hpartial0 hcol1 he1
    norm_num at h ⊢
    exact h
  have hcol2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat e1.2.1 e1.2.2.1 e1.2.2.2 +
        (l2.toNat + q3 + q4 + n0.toNat) :=
    addChain4 hs2z hs2a hs2b hs2
  have hpartial2 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
        l0.toNat + q0 + 2 ^ 64 * (l1.toNat + q1 + q2) +
          2 ^ 128 * (l2.toNat + q3 + q4 + n0.toNat) := by
    have h := appendRadixColumn (shift := 2 ^ 128) hpartial1 hcol2 he2
    norm_num at h ⊢
    exact h
  have hcol3 : accToNat s3.1 s3.2.1 s3.2.2 =
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 +
        (l3.toNat + q5 + q6 + n1.toNat) :=
    addChain4 hs3z hs3a hs3b hs3
  have hpartial3 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat +
          2 ^ 256 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
        l0.toNat + q0 + 2 ^ 64 * (l1.toNat + q1 + q2) +
          2 ^ 128 * (l2.toNat + q3 + q4 + n0.toNat) +
          2 ^ 192 * (l3.toNat + q5 + q6 + n1.toNat) := by
    have h := appendRadixColumn (shift := 2 ^ 192) hpartial2 hcol3 he3
    norm_num at h ⊢
    exact h
  have hcol4 : accToNat s4.1 s4.2.1 s4.2.2 =
      accToNat e3.2.1 e3.2.2.1 e3.2.2.2 + (q7 + n2.toNat) :=
    addChain2 hs4a hs4
  have hpartial :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat + 2 ^ 256 * e4.1.toNat +
          2 ^ 320 * accToNat e4.2.1 e4.2.2.1 e4.2.2.2 =
        l0.toNat + q0 + 2 ^ 64 * (l1.toNat + q1 + q2) +
          2 ^ 128 * (l2.toNat + q3 + q4 + n0.toNat) +
          2 ^ 192 * (l3.toNat + q5 + q6 + n1.toNat) +
          2 ^ 256 * (q7 + n2.toNat) := by
    have h := appendRadixColumn (shift := 2 ^ 256) hpartial3 hcol4 he4
    norm_num at h ⊢
    exact h
  let low := (Repr.ofLimbs l0 l1 l2 l3).toNat
  let high := (Repr.ofLimbs n0 n1 n2 n3).toNat
  let comp := 2 ^ 256 - Secp256k1.Scalar.Basic.CARD
  have hexpand : low + high * comp =
      l0.toNat + q0 + 2 ^ 64 * (l1.toNat + q1 + q2) +
        2 ^ 128 * (l2.toNat + q3 + q4 + n0.toNat) +
        2 ^ 192 * (l3.toNat + q5 + q6 + n1.toNat) +
        2 ^ 256 * (q7 + n2.toNat) + 2 ^ 320 * n3.toNat := by
    simp only [low, high, comp, Repr.toNat, Repr.ofLimbs, q0, q1, q2, q3, q4,
      q5, q6, q7]
    norm_num [TWO64, TWO128, TWO192, N_C_0, N_C_1, UInt64.toNat_ofNat,
      Secp256k1.Scalar.Basic.CARD]
    ring
  have hlow := Repr.toNat_lt_two256 (Repr.ofLimbs l0 l1 l2 l3)
  have hhigh := Repr.toNat_lt_two256 (Repr.ofLimbs n0 n1 n2 n3)
  have htotal : low + high * comp < 2 ^ 448 := by
    change low < 2 ^ 256 at hlow
    change high < 2 ^ 256 at hhigh
    norm_num [comp, Secp256k1.Scalar.Basic.CARD] at hexpand ⊢
    omega
  have hlastBound : accToNat e4.2.1 e4.2.2.1 e4.2.2.2 + n3.toNat < 2 ^ 128 := by
    norm_num at hpartial hexpand htotal ⊢
    omega
  generalize h_s5 : sumAddFast e4.2.1 e4.2.2.1 e4.2.2.2 n3 = s5
  have hs5 : accToNat s5.1 s5.2.1 s5.2.2 =
      accToNat e4.2.1 e4.2.2.1 e4.2.2.2 + n3.toNat := by
    rw [← h_s5]
    apply sumAddFast_value
    · rw [← h_e4]
      simp [extract]
    · exact hlastBound
  generalize h_e5 : extractFast s5.1 s5.2.1 s5.2.2 = e5
  have he5 : e5.1.toNat + 2 ^ 64 * accToNat e5.2.1 e5.2.2.1 e5.2.2.2 =
      accToNat s5.1 s5.2.1 s5.2.2 := by
    have h := extractFast_value s5.1 s5.2.1 s5.2.2 (by
      rw [← h_s5]
      simp [sumAddFast]
      rw [← h_e4]
      simp [extract])
    rw [h_e5] at h
    exact h
  have he5tail : accToNat e5.2.1 e5.2.2.1 e5.2.2.2 = e5.2.1.toNat := by
    rw [← h_e5]
    simp [extractFast, accToNat]
  have hout : limbs7ToNat
      (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e5.2.1) = low + high * comp := by
    unfold limbs7ToNat
    norm_num at hpartial hexpand hs5 he5 he5tail ⊢
    omega
  have hcolumns : reduce512To385Raw l0 l1 l2 l3 n0 n1 n2 n3 =
      (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e5.2.1) := by
    simpa only [h_s0, h_e0, h_s1z, h_s1a, h_s1, h_e1, h_s2z, h_s2a,
      h_s2b, h_s2, h_e2, h_s3z, h_s3a, h_s3b, h_s3, h_e3, h_s4a, h_s4,
      h_e4, h_s5, h_e5] using
        reduce512To385Raw_columns l0 l1 l2 l3 n0 n1 n2 n3
  calc
    limbs7ToNat (reduce512To385Raw l0 l1 l2 l3 n0 n1 n2 n3) =
        limbs7ToNat (e0.1, e1.1, e2.1, e3.1, e4.1, e5.1, e5.2.1) := by
      exact congrArg limbs7ToNat hcolumns
    _ = low + high * comp := hout

/-- The first reduction stage fits in the 385 bits assumed by the next stage. -/
private theorem reduce512To385Raw_bound
    (l0 l1 l2 l3 n0 n1 n2 n3 : UInt64) :
    limbs7ToNat (reduce512To385Raw l0 l1 l2 l3 n0 n1 n2 n3) < 2 ^ 385 := by
  rw [reduce512To385Raw_value]
  have hlow := Repr.toNat_lt_two256 (Repr.ofLimbs l0 l1 l2 l3)
  have hhigh := Repr.toNat_lt_two256 (Repr.ofLimbs n0 n1 n2 n3)
  norm_num [Secp256k1.Scalar.Basic.CARD] at hlow hhigh ⊢
  omega

/-- Second libsecp256k1 reduction stage: fold limbs four through six with
    `2^256 - n`, producing at most 258 bits. -/
@[inline] private def reduce385To258Raw
    (m0 m1 m2 m3 m4 m5 m6 : UInt64) : Limbs4Carry :=
  let (c0, c1, c2) := mulAddFast m0 0 0 m4 N_C_0
  let (p0, c0, c1, c2) := extractFast c0 c1 c2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 m1
  let (c0, c1, c2) := mulAdd c0 c1 c2 m5 N_C_0
  let (c0, c1, c2) := mulAdd c0 c1 c2 m4 N_C_1
  let (p1, c0, c1, c2) := extract c0 c1 c2
  let (c0, c1, c2) := sumAdd c0 c1 c2 m2
  let (c0, c1, c2) := mulAdd c0 c1 c2 m6 N_C_0
  let (c0, c1, c2) := mulAdd c0 c1 c2 m5 N_C_1
  let (c0, c1, c2) := sumAdd c0 c1 c2 m4
  let (p2, c0, c1, c2) := extract c0 c1 c2
  let (c0, c1, c2) := sumAddFast c0 c1 c2 m3
  let (c0, c1, c2) := mulAddFast c0 c1 c2 m6 N_C_1
  let (c0, c1, c2) := sumAddFast c0 c1 c2 m5
  let (p3, c0, _, _) := extractFast c0 c1 c2
  let p4 := c0 + m6
  (p0, p1, p2, p3, p4)

/-- Expose the four second-stage reduction columns without unfolding their kernels. -/
private theorem reduce385To258Raw_columns (m0 m1 m2 m3 m4 m5 m6 : UInt64) :
    reduce385To258Raw m0 m1 m2 m3 m4 m5 m6 =
      let s0 := mulAddFast m0 0 0 m4 N_C_0
      let e0 := extractFast s0.1 s0.2.1 s0.2.2
      let s1z := sumAddFast e0.2.1 e0.2.2.1 e0.2.2.2 m1
      let s1a := mulAdd s1z.1 s1z.2.1 s1z.2.2 m5 N_C_0
      let s1 := mulAdd s1a.1 s1a.2.1 s1a.2.2 m4 N_C_1
      let e1 := extract s1.1 s1.2.1 s1.2.2
      let s2z := sumAdd e1.2.1 e1.2.2.1 e1.2.2.2 m2
      let s2a := mulAdd s2z.1 s2z.2.1 s2z.2.2 m6 N_C_0
      let s2b := mulAdd s2a.1 s2a.2.1 s2a.2.2 m5 N_C_1
      let s2 := sumAdd s2b.1 s2b.2.1 s2b.2.2 m4
      let e2 := extract s2.1 s2.2.1 s2.2.2
      let s3z := sumAddFast e2.2.1 e2.2.2.1 e2.2.2.2 m3
      let s3a := mulAddFast s3z.1 s3z.2.1 s3z.2.2 m6 N_C_1
      let s3 := sumAddFast s3a.1 s3a.2.1 s3a.2.2 m5
      let e3 := extractFast s3.1 s3.2.1 s3.2.2
      (e0.1, e1.1, e2.1, e3.1, e3.2.1 + m6) := rfl

/-- Exact value equation for the second reduction stage. -/
private theorem reduce385To258Raw_value
    (m0 m1 m2 m3 m4 m5 m6 : UInt64)
    (hinput : limbs7ToNat (m0, m1, m2, m3, m4, m5, m6) < 2 ^ 385) :
    limbs5ToNat (reduce385To258Raw m0 m1 m2 m3 m4 m5 m6) =
      (Repr.ofLimbs m0 m1 m2 m3).toNat +
        (m4.toNat + 2 ^ 64 * m5.toNat + 2 ^ 128 * m6.toNat) *
          (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) := by
  let q0 := m4.toNat * N_C_0.toNat
  let q1 := m5.toNat * N_C_0.toNat
  let q2 := m4.toNat * N_C_1.toNat
  let q3 := m6.toNat * N_C_0.toNat
  let q4 := m5.toNat * N_C_1.toNat
  let q5 := m6.toNat * N_C_1.toNat
  have hq0 : q0 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound m4
  have hq1 : q1 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound m5
  have hq2 : q2 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound m4
  have hq3 : q3 < 2 ^ 64 * N_C_0.toNat := mulNC0_bound m6
  have hq4 : q4 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound m5
  have hq5 : q5 < 2 ^ 64 * N_C_1.toNat := mulNC1_bound m6
  norm_num [N_C_0, N_C_1, UInt64.toNat_ofNat] at hq0 hq1 hq2 hq3 hq4 hq5
  have hm0 := m0.toNat_lt_size
  have hm1 := m1.toNat_lt_size
  have hm2 := m2.toNat_lt_size
  have hm3 := m3.toNat_lt_size
  have hm4 := m4.toNat_lt_size
  have hm5 := m5.toNat_lt_size
  have hm6 := m6.toNat_lt_size
  norm_num [UInt64.size] at hm0 hm1 hm2 hm3 hm4 hm5 hm6

  generalize h_s0 : mulAddFast m0 0 0 m4 N_C_0 = s0
  have hs0 : accToNat s0.1 s0.2.1 s0.2.2 = m0.toNat + q0 := by
    rw [← h_s0]
    apply mulAddFast_value
    · rfl
    · change m0.toNat + q0 < 2 ^ 128
      omega
  generalize h_e0 : extractFast s0.1 s0.2.1 s0.2.2 = e0
  have he0 : e0.1.toNat + 2 ^ 64 * accToNat e0.2.1 e0.2.2.1 e0.2.2.2 =
      accToNat s0.1 s0.2.1 s0.2.2 := by
    have h := extractFast_value s0.1 s0.2.1 s0.2.2 (by
      rw [← h_s0]
      simp [mulAddFast])
    rw [h_e0] at h
    exact h
  have he0bound : accToNat e0.2.1 e0.2.2.1 e0.2.2.2 < 2 ^ 64 := by
    rw [← h_e0]
    simpa [extractFast] using accToNat_lt_two64 s0.2.1

  generalize h_s1z : sumAddFast e0.2.1 e0.2.2.1 e0.2.2.2 m1 = s1z
  have hs1z : accToNat s1z.1 s1z.2.1 s1z.2.2 =
      accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + m1.toNat := by
    rw [← h_s1z]
    apply sumAddFast_value
    · rw [← h_e0]
      simp [extractFast]
    · omega
  generalize h_s1a : mulAdd s1z.1 s1z.2.1 s1z.2.2 m5 N_C_0 = s1a
  have hs1a : accToNat s1a.1 s1a.2.1 s1a.2.2 =
      accToNat s1z.1 s1z.2.1 s1z.2.2 + q1 := by
    rw [← h_s1a]
    apply mulAdd_value
    rw [hs1z]
    change accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + m1.toNat + q1 < 2 ^ 192
    omega
  generalize h_s1 : mulAdd s1a.1 s1a.2.1 s1a.2.2 m4 N_C_1 = s1
  have hs1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat s1a.1 s1a.2.1 s1a.2.2 + q2 := by
    rw [← h_s1]
    apply mulAdd_value
    rw [hs1a, hs1z]
    change accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + m1.toNat + q1 + q2 < 2 ^ 192
    omega
  generalize h_e1 : extract s1.1 s1.2.1 s1.2.2 = e1
  have he1 : e1.1.toNat + 2 ^ 64 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
      accToNat s1.1 s1.2.1 s1.2.2 := by
    have h := extract_value s1.1 s1.2.1 s1.2.2
    rw [h_e1] at h
    exact h
  have he1bound : accToNat e1.2.1 e1.2.2.1 e1.2.2.2 < 2 ^ 128 := by
    rw [← h_e1]
    simpa [extract] using accToNat_lt_two128 s1.2.1 s1.2.2

  generalize h_s2z : sumAdd e1.2.1 e1.2.2.1 e1.2.2.2 m2 = s2z
  have hs2z : accToNat s2z.1 s2z.2.1 s2z.2.2 =
      accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + m2.toNat := by
    rw [← h_s2z]
    apply sumAdd_value
    omega
  generalize h_s2a : mulAdd s2z.1 s2z.2.1 s2z.2.2 m6 N_C_0 = s2a
  have hs2a : accToNat s2a.1 s2a.2.1 s2a.2.2 =
      accToNat s2z.1 s2z.2.1 s2z.2.2 + q3 := by
    rw [← h_s2a]
    apply mulAdd_value
    rw [hs2z]
    change accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + m2.toNat + q3 < 2 ^ 192
    omega
  generalize h_s2b : mulAdd s2a.1 s2a.2.1 s2a.2.2 m5 N_C_1 = s2b
  have hs2b : accToNat s2b.1 s2b.2.1 s2b.2.2 =
      accToNat s2a.1 s2a.2.1 s2a.2.2 + q4 := by
    rw [← h_s2b]
    apply mulAdd_value
    rw [hs2a, hs2z]
    change accToNat e1.2.1 e1.2.2.1 e1.2.2.2 + m2.toNat + q3 + q4 < 2 ^ 192
    omega
  generalize h_s2 : sumAdd s2b.1 s2b.2.1 s2b.2.2 m4 = s2
  have hs2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat s2b.1 s2b.2.1 s2b.2.2 + m4.toNat := by
    rw [← h_s2]
    apply sumAdd_value
    rw [hs2b, hs2a, hs2z]
    omega
  generalize h_e2 : extract s2.1 s2.2.1 s2.2.2 = e2
  have he2 : e2.1.toNat + 2 ^ 64 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
      accToNat s2.1 s2.2.1 s2.2.2 := by
    have h := extract_value s2.1 s2.2.1 s2.2.2
    rw [h_e2] at h
    exact h

  have hpartial0 :
      e0.1.toNat + 2 ^ 64 * accToNat e0.2.1 e0.2.2.1 e0.2.2.2 =
        m0.toNat + q0 :=
    he0.trans hs0
  have hcol1 : accToNat s1.1 s1.2.1 s1.2.2 =
      accToNat e0.2.1 e0.2.2.1 e0.2.2.2 + (m1.toNat + q1 + q2) :=
    addChain3 hs1z hs1a hs1
  have hpartial1 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat +
          2 ^ 128 * accToNat e1.2.1 e1.2.2.1 e1.2.2.2 =
        m0.toNat + q0 + 2 ^ 64 * (m1.toNat + q1 + q2) := by
    have h := appendRadixColumn (shift := 2 ^ 64) hpartial0 hcol1 he1
    norm_num at h ⊢
    exact h
  have hcol2 : accToNat s2.1 s2.2.1 s2.2.2 =
      accToNat e1.2.1 e1.2.2.1 e1.2.2.2 +
        (m2.toNat + q3 + q4 + m4.toNat) :=
    addChain4 hs2z hs2a hs2b hs2
  have hpartial :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * accToNat e2.2.1 e2.2.2.1 e2.2.2.2 =
        m0.toNat + q0 + 2 ^ 64 * (m1.toNat + q1 + q2) +
          2 ^ 128 * (m2.toNat + q3 + q4 + m4.toNat) := by
    have h := appendRadixColumn (shift := 2 ^ 128) hpartial1 hcol2 he2
    norm_num at h ⊢
    exact h
  let low := (Repr.ofLimbs m0 m1 m2 m3).toNat
  let high := m4.toNat + 2 ^ 64 * m5.toNat + 2 ^ 128 * m6.toNat
  let comp := 2 ^ 256 - Secp256k1.Scalar.Basic.CARD
  have hexpand : low + high * comp =
      m0.toNat + q0 + 2 ^ 64 * (m1.toNat + q1 + q2) +
        2 ^ 128 * (m2.toNat + q3 + q4 + m4.toNat) +
        2 ^ 192 * (m3.toNat + q5 + m5.toNat) + 2 ^ 256 * m6.toNat := by
    simp only [low, high, comp, Repr.toNat, Repr.ofLimbs, q0, q1, q2, q3, q4, q5]
    norm_num [TWO64, TWO128, TWO192, N_C_0, N_C_1, UInt64.toNat_ofNat,
      Secp256k1.Scalar.Basic.CARD]
    ring
  have hhigh : high < 2 ^ 129 := by
    unfold limbs7ToNat at hinput
    dsimp [high]
    norm_num at hinput ⊢
    omega
  have hlow := Repr.toNat_lt_two256 (Repr.ofLimbs m0 m1 m2 m3)
  have htarget : low + high * comp < 2 ^ 259 := by
    change low < 2 ^ 256 at hlow
    norm_num [comp, Secp256k1.Scalar.Basic.CARD] at hlow hhigh ⊢
    omega
  have htail :
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + m3.toNat + q5 + m5.toNat +
        2 ^ 64 * m6.toNat < 2 ^ 67 := by
    clear hq0 hq1 hq2 hq3 hq4 hq5 hm0 hm1 hm2 hm3 hm4 hm5 hm6
    clear he0bound he1bound hs0 he0 hs1z hs1a hs1 he1 hs2z hs2a hs2b hs2 he2
    clear hinput hhigh hlow
    norm_num at hpartial hexpand htarget ⊢
    omega

  generalize h_s3z : sumAddFast e2.2.1 e2.2.2.1 e2.2.2.2 m3 = s3z
  have hs3z : accToNat s3z.1 s3z.2.1 s3z.2.2 =
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + m3.toNat := by
    rw [← h_s3z]
    apply sumAddFast_value
    · rw [← h_e2]
      simp [extract]
    · omega
  generalize h_s3a : mulAddFast s3z.1 s3z.2.1 s3z.2.2 m6 N_C_1 = s3a
  have hs3a : accToNat s3a.1 s3a.2.1 s3a.2.2 =
      accToNat s3z.1 s3z.2.1 s3z.2.2 + q5 := by
    rw [← h_s3a]
    apply mulAddFast_value
    · rw [← h_s3z]
      simp [sumAddFast]
      rw [← h_e2]
      simp [extract]
    · rw [hs3z]
      omega
  generalize h_s3 : sumAddFast s3a.1 s3a.2.1 s3a.2.2 m5 = s3
  have hs3 : accToNat s3.1 s3.2.1 s3.2.2 =
      accToNat s3a.1 s3a.2.1 s3a.2.2 + m5.toNat := by
    rw [← h_s3]
    apply sumAddFast_value
    · rw [← h_s3a]
      simp [mulAddFast]
      rw [← h_s3z]
      simp [sumAddFast]
      rw [← h_e2]
      simp [extract]
    · rw [hs3a, hs3z]
      omega
  generalize h_e3 : extractFast s3.1 s3.2.1 s3.2.2 = e3
  have he3 : e3.1.toNat + 2 ^ 64 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
      accToNat s3.1 s3.2.1 s3.2.2 := by
    have h := extractFast_value s3.1 s3.2.1 s3.2.2 (by
      rw [← h_s3]
      simp [sumAddFast]
      rw [← h_s3a]
      simp [mulAddFast]
      rw [← h_s3z]
      simp [sumAddFast]
      rw [← h_e2]
      simp [extract])
    rw [h_e3] at h
    exact h
  have he3tail : accToNat e3.2.1 e3.2.2.1 e3.2.2.2 = e3.2.1.toNat := by
    rw [← h_e3]
    simp [extractFast, accToNat]
  have hp4bound : e3.2.1.toNat + m6.toNat < 2 ^ 64 := by
    norm_num at htail hs3z hs3a hs3 he3 he3tail ⊢
    omega
  have hp4 : (e3.2.1 + m6).toNat = e3.2.1.toNat + m6.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hp4bound]
  have hcol3 : e3.1.toNat + 2 ^ 64 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
      accToNat e2.2.1 e2.2.2.1 e2.2.2.2 + (m3.toNat + q5 + m5.toNat) :=
    he3.trans (addChain3 hs3z hs3a hs3)
  have hpartial3 :
      e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat +
          2 ^ 256 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2 =
        m0.toNat + q0 + 2 ^ 64 * (m1.toNat + q1 + q2) +
          2 ^ 128 * (m2.toNat + q3 + q4 + m4.toNat) +
          2 ^ 192 * (m3.toNat + q5 + m5.toNat) := by
    have h := appendCompletedColumn (shift := 2 ^ 192) hpartial hcol3
    norm_num at h ⊢
    exact h
  have hout : limbs5ToNat (e0.1, e1.1, e2.1, e3.1, e3.2.1 + m6) =
      low + high * comp := by
    change e0.1.toNat + e1.1.toNat * TWO64 + e2.1.toNat * TWO128 +
        e3.1.toNat * TWO192 + 2 ^ 256 * (e3.2.1 + m6).toNat = low + high * comp
    rw [hp4]
    calc
      e0.1.toNat + e1.1.toNat * TWO64 + e2.1.toNat * TWO128 +
          e3.1.toNat * TWO192 +
          2 ^ 256 * (e3.2.1.toNat + m6.toNat) =
        (e0.1.toNat + 2 ^ 64 * e1.1.toNat + 2 ^ 128 * e2.1.toNat +
          2 ^ 192 * e3.1.toNat +
          2 ^ 256 * accToNat e3.2.1 e3.2.2.1 e3.2.2.2) +
          2 ^ 256 * m6.toNat := by
            rw [he3tail]
            norm_num [TWO64, TWO128, TWO192]
            ring
      _ = (m0.toNat + q0 + 2 ^ 64 * (m1.toNat + q1 + q2) +
          2 ^ 128 * (m2.toNat + q3 + q4 + m4.toNat) +
          2 ^ 192 * (m3.toNat + q5 + m5.toNat)) + 2 ^ 256 * m6.toNat := by
            rw [hpartial3]
      _ = low + high * comp := hexpand.symm
  have hcolumns : reduce385To258Raw m0 m1 m2 m3 m4 m5 m6 =
      (e0.1, e1.1, e2.1, e3.1, e3.2.1 + m6) := by
    simpa only [h_s0, h_e0, h_s1z, h_s1a, h_s1, h_e1, h_s2z, h_s2a,
      h_s2b, h_s2, h_e2, h_s3z, h_s3a, h_s3, h_e3] using
        reduce385To258Raw_columns m0 m1 m2 m3 m4 m5 m6
  calc
    limbs5ToNat (reduce385To258Raw m0 m1 m2 m3 m4 m5 m6) =
        limbs5ToNat (e0.1, e1.1, e2.1, e3.1, e3.2.1 + m6) := by
      exact congrArg limbs5ToNat hcolumns
    _ = low + high * comp := hout

/-- The second reduction stage fits in 258 bits. -/
private theorem reduce385To258Raw_bound
    (m0 m1 m2 m3 m4 m5 m6 : UInt64)
    (hinput : limbs7ToNat (m0, m1, m2, m3, m4, m5, m6) < 2 ^ 385) :
    limbs5ToNat (reduce385To258Raw m0 m1 m2 m3 m4 m5 m6) < 2 ^ 259 := by
  rw [reduce385To258Raw_value _ _ _ _ _ _ _ hinput]
  let low := (Repr.ofLimbs m0 m1 m2 m3).toNat
  let high := m4.toNat + 2 ^ 64 * m5.toNat + 2 ^ 128 * m6.toNat
  have hhigh : high < 2 ^ 129 := by
    unfold limbs7ToNat at hinput
    dsimp [high]
    norm_num at hinput ⊢
    omega
  have hlow := Repr.toNat_lt_two256 (Repr.ofLimbs m0 m1 m2 m3)
  change low < 2 ^ 256 at hlow
  norm_num [Secp256k1.Scalar.Basic.CARD] at hlow hhigh ⊢
  omega

/-- C `secp256k1_scalar_reduce_512`, non-asm path. -/
@[inline] def reduce512Raw (l0 l1 l2 l3 l4 l5 l6 l7 : UInt64) : Limbs4 :=
  let (m0, m1, m2, m3, m4, m5, m6) :=
    reduce512To385Raw l0 l1 l2 l3 l4 l5 l6 l7
  let (p0, p1, p2, p3, p4) := reduce385To258Raw m0 m1 m2 m3 m4 m5 m6
  let (r0, r1, r2, r3, carry) := reduce258Raw p0 p1 p2 p3 p4
  reduceRaw r0 r1 r2 r3 (carry != 0 || checkOverflowRaw r0 r1 r2 r3)

/-- Adding one scalar order does not change a natural number's scalar-field cast. -/
private theorem cast_eq_of_add_card_eq (r x : Nat)
    (h : r + Secp256k1.Scalar.Basic.CARD = x) :
    (r : Secp256k1.Scalar.Basic.Field) = (x : Secp256k1.Scalar.Basic.Field) := by
  apply ZMod.val_injective
  simp only [ZMod.val_natCast]
  rw [← h, Nat.add_mod]
  simp

/-- Replacing one factor `2^256` by `2^256 - n` preserves the scalar-field cast. -/
private theorem foldComplement_cast (low high : Nat) :
    ((low + high * (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) : Nat) :
        Secp256k1.Scalar.Basic.Field) =
      ((low + 2 ^ 256 * high : Nat) : Secp256k1.Scalar.Basic.Field) := by
  have hcard : (Secp256k1.Scalar.Basic.CARD : Secp256k1.Scalar.Basic.Field) = 0 :=
    CharP.cast_eq_zero _ _
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  rw [Nat.cast_sub (by norm_num [Secp256k1.Scalar.Basic.CARD])]
  rw [hcard]
  ring

/-- The scalar order is strictly below the 256-bit radix. -/
private theorem card_lt_two256 : Secp256k1.Scalar.Basic.CARD < 2 ^ 256 := by
  norm_num [Secp256k1.Scalar.Basic.CARD]

/-- The scalar-order complement fills the gap to the 256-bit radix. -/
private theorem complement_add_card :
    (2 ^ 256 - Secp256k1.Scalar.Basic.CARD) +
      Secp256k1.Scalar.Basic.CARD = 2 ^ 256 :=
  Nat.sub_add_cancel (Nat.le_of_lt card_lt_two256)

/-- Final conditional subtraction when the folded value has no high carry. -/
private theorem finishReduceRaw_zero_spec (q0 q1 q2 q3 : UInt64)
    (htwo : limbs5ToNat (q0, q1, q2, q3, 0) <
      2 * Secp256k1.Scalar.Basic.CARD) :
    let r := reduceRaw q0 q1 q2 q3 (checkOverflowRaw q0 q1 q2 q3)
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
        Secp256k1.Scalar.Basic.CARD ∧
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
          Secp256k1.Scalar.Basic.Field) =
        (limbs5ToNat (q0, q1, q2, q3, 0) :
          Secp256k1.Scalar.Basic.Field) := by
  let low := (Repr.ofLimbs q0 q1 q2 q3).toNat
  have hqLow : limbs5ToNat (q0, q1, q2, q3, 0) = low := by
    unfold limbs5ToNat low
    norm_num
  have hcheck := checkOverflowRaw_eq_decide q0 q1 q2 q3
  change checkOverflowRaw q0 q1 q2 q3 =
    decide (low ≥ Secp256k1.Scalar.Basic.CARD) at hcheck
  by_cases hge : Secp256k1.Scalar.Basic.CARD ≤ low
  · have hcheckTrue : checkOverflowRaw q0 q1 q2 q3 = true := by
      rw [hcheck]
      simp [hge]
    have hreduce := reduceRaw_true_of_ge q0 q1 q2 q3 hge
    rw [hcheckTrue]
    dsimp only
    rw [hreduce]
    constructor
    · rw [hqLow] at htwo
      omega
    · apply cast_eq_of_add_card_eq
      rw [hqLow]
      exact Nat.sub_add_cancel hge
  · have hlt : low < Secp256k1.Scalar.Basic.CARD := Nat.lt_of_not_ge hge
    have hcheckFalse : checkOverflowRaw q0 q1 q2 q3 = false := by
      rw [hcheck]
      simp [hlt]
    simp [hcheckFalse, reduceRaw]
    exact ⟨hlt, by rw [hqLow]⟩

/-- With one high carry, the reduced value plus the order is the folded input. -/
private theorem finishReduceRaw_carry_value (q0 q1 q2 q3 carry : UInt64)
    (hc : carry ≠ 0) (hcarry : carry.toNat ≤ 1)
    (htwo : limbs5ToNat (q0, q1, q2, q3, carry) <
      2 * Secp256k1.Scalar.Basic.CARD) :
    let r := reduceRaw q0 q1 q2 q3 true
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat +
      Secp256k1.Scalar.Basic.CARD =
        limbs5ToNat (q0, q1, q2, q3, carry) := by
  let low := (Repr.ofLimbs q0 q1 q2 q3).toNat
  have hdecomp : limbs5ToNat (q0, q1, q2, q3, carry) =
      low + 2 ^ 256 * carry.toNat := rfl
  have hcarryNat : carry.toNat = 1 := by
    have hne : carry.toNat ≠ 0 := by
      intro hz
      apply hc
      apply UInt64.toNat.inj
      simpa using hz
    omega
  have hlowLt : low < Secp256k1.Scalar.Basic.CARD := by
    rw [hdecomp, hcarryNat] at htwo
    norm_num only [Nat.mul_one] at htwo
    by_contra hnot
    have hge : Secp256k1.Scalar.Basic.CARD ≤ low := Nat.le_of_not_gt hnot
    have hcard := card_lt_two256
    have htwice : 2 * Secp256k1.Scalar.Basic.CARD <
        Secp256k1.Scalar.Basic.CARD + 2 ^ 256 := by omega
    have hsum : Secp256k1.Scalar.Basic.CARD + 2 ^ 256 ≤ low + 2 ^ 256 :=
      Nat.add_le_add_right hge _
    have hcontra : 2 * Secp256k1.Scalar.Basic.CARD <
        2 * Secp256k1.Scalar.Basic.CARD :=
      lt_of_lt_of_le (lt_of_lt_of_le htwice hsum) (Nat.le_of_lt htwo)
    exact (Nat.lt_irrefl _ hcontra)
  have hreduce := reduceRaw_true_of_lt q0 q1 q2 q3 hlowLt
  have harith :
      ((Repr.ofLimbs q0 q1 q2 q3).toNat +
          (2 ^ 256 - Secp256k1.Scalar.Basic.CARD)) +
        Secp256k1.Scalar.Basic.CARD =
          limbs5ToNat (q0, q1, q2, q3, carry) := by
    change (low + (2 ^ 256 - Secp256k1.Scalar.Basic.CARD)) +
      Secp256k1.Scalar.Basic.CARD = limbs5ToNat (q0, q1, q2, q3, carry)
    rw [Nat.add_assoc, complement_add_card, hdecomp, hcarryNat]
    norm_num
  exact (congrArg (fun x => x + Secp256k1.Scalar.Basic.CARD) hreduce).trans harith

/-- Final conditional subtraction when the folded value has one high carry. -/
private theorem finishReduceRaw_carry_spec (q0 q1 q2 q3 carry : UInt64)
    (hc : carry ≠ 0) (hcarry : carry.toNat ≤ 1)
    (htwo : limbs5ToNat (q0, q1, q2, q3, carry) <
      2 * Secp256k1.Scalar.Basic.CARD) :
    let r := reduceRaw q0 q1 q2 q3 true
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
        Secp256k1.Scalar.Basic.CARD ∧
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
          Secp256k1.Scalar.Basic.Field) =
        (limbs5ToNat (q0, q1, q2, q3, carry) :
          Secp256k1.Scalar.Basic.Field) := by
  have hv := finishReduceRaw_carry_value q0 q1 q2 q3 carry hc hcarry htwo
  constructor
  · dsimp only at hv ⊢
    omega
  · exact cast_eq_of_add_card_eq _ _ hv

/-- Final conditional subtraction for a folded value below twice the scalar order. -/
private theorem finishReduceRaw_spec (q0 q1 q2 q3 carry : UInt64)
    (hcarry : carry.toNat ≤ 1)
    (htwo : limbs5ToNat (q0, q1, q2, q3, carry) <
      2 * Secp256k1.Scalar.Basic.CARD) :
    let r := reduceRaw q0 q1 q2 q3
      (carry != 0 || checkOverflowRaw q0 q1 q2 q3)
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
        Secp256k1.Scalar.Basic.CARD ∧
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
          Secp256k1.Scalar.Basic.Field) =
        (limbs5ToNat (q0, q1, q2, q3, carry) :
          Secp256k1.Scalar.Basic.Field) := by
  by_cases hc : carry = 0
  · subst carry
    have hflag : (((0 : UInt64) != 0) || checkOverflowRaw q0 q1 q2 q3) =
        checkOverflowRaw q0 q1 q2 q3 := by simp
    rw [hflag]
    exact finishReduceRaw_zero_spec q0 q1 q2 q3 htwo
  · have h := finishReduceRaw_carry_spec q0 q1 q2 q3 carry hc hcarry htwo
    have hflag : ((carry != 0) || checkOverflowRaw q0 q1 q2 q3) = true := by
      simp [hc]
    rw [hflag]
    exact h

/-- The complete libsecp256k1 reducer returns a canonical scalar with the same
    scalar-field value as its eight-limb input. -/
private theorem reduce512Raw_spec (l0 l1 l2 l3 l4 l5 l6 l7 : UInt64) :
    let r := reduce512Raw l0 l1 l2 l3 l4 l5 l6 l7
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
        Secp256k1.Scalar.Basic.CARD ∧
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
          Secp256k1.Scalar.Basic.Field) =
        (limbs8ToNat (l0, l1, l2, l3, l4, l5, l6, l7) :
          Secp256k1.Scalar.Basic.Field) := by
  generalize hmEq : reduce512To385Raw l0 l1 l2 l3 l4 l5 l6 l7 = m
  have hmValue := reduce512To385Raw_value l0 l1 l2 l3 l4 l5 l6 l7
  have hmBound := reduce512To385Raw_bound l0 l1 l2 l3 l4 l5 l6 l7
  rw [hmEq] at hmValue hmBound
  change limbs7ToNat m = _ at hmValue
  change limbs7ToNat m < 2 ^ 385 at hmBound
  rcases m with ⟨m0, m1, m2, m3, m4, m5, m6⟩
  generalize hpEq : reduce385To258Raw m0 m1 m2 m3 m4 m5 m6 = p
  have hpValue := reduce385To258Raw_value m0 m1 m2 m3 m4 m5 m6 hmBound
  have hpBound := reduce385To258Raw_bound m0 m1 m2 m3 m4 m5 m6 hmBound
  rw [hpEq] at hpValue hpBound
  change limbs5ToNat p = _ at hpValue
  change limbs5ToNat p < 2 ^ 259 at hpBound
  rcases p with ⟨p0, p1, p2, p3, p4⟩
  generalize hqEq : reduce258Raw p0 p1 p2 p3 p4 = q
  have hqValue := reduce258Raw_value p0 p1 p2 p3 p4 hpBound
  have hqBound := reduce258Raw_bound p0 p1 p2 p3 p4 hpBound
  have hqCarry := reduce258Raw_carry_le_one p0 p1 p2 p3 p4 hpBound
  rw [hqEq] at hqValue hqBound hqCarry
  change limbs5ToNat q = _ at hqValue
  change limbs5ToNat q < 2 ^ 257 at hqBound
  rcases q with ⟨q0, q1, q2, q3, carry⟩
  let lowL := (Repr.ofLimbs l0 l1 l2 l3).toNat
  let highL := (Repr.ofLimbs l4 l5 l6 l7).toNat
  let lowM := (Repr.ofLimbs m0 m1 m2 m3).toNat
  let highM := m4.toNat + 2 ^ 64 * m5.toNat + 2 ^ 128 * m6.toNat
  let lowP := (Repr.ofLimbs p0 p1 p2 p3).toNat
  let lowQ := (Repr.ofLimbs q0 q1 q2 q3).toNat
  have hinputDecomp :
      limbs8ToNat (l0, l1, l2, l3, l4, l5, l6, l7) = lowL + 2 ^ 256 * highL := by
    unfold limbs8ToNat lowL highL Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192
    norm_num
    ring
  have hmDecomp :
      limbs7ToNat (m0, m1, m2, m3, m4, m5, m6) = lowM + 2 ^ 256 * highM := by
    unfold limbs7ToNat lowM highM Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192
    norm_num
    ring
  have hpDecomp : limbs5ToNat (p0, p1, p2, p3, p4) = lowP + 2 ^ 256 * p4.toNat := by
    rfl
  have hqDecomp : limbs5ToNat (q0, q1, q2, q3, carry) =
      lowQ + 2 ^ 256 * carry.toNat := by
    rfl
  have hmCast :
      (limbs7ToNat (m0, m1, m2, m3, m4, m5, m6) :
          Secp256k1.Scalar.Basic.Field) =
        (limbs8ToNat (l0, l1, l2, l3, l4, l5, l6, l7) :
          Secp256k1.Scalar.Basic.Field) := by
    rw [hmValue, hinputDecomp]
    exact foldComplement_cast lowL highL
  have hpCast :
      (limbs5ToNat (p0, p1, p2, p3, p4) : Secp256k1.Scalar.Basic.Field) =
        (limbs7ToNat (m0, m1, m2, m3, m4, m5, m6) :
          Secp256k1.Scalar.Basic.Field) := by
    rw [hpValue, hmDecomp]
    exact foldComplement_cast lowM highM
  have hqCast :
      (limbs5ToNat (q0, q1, q2, q3, carry) : Secp256k1.Scalar.Basic.Field) =
        (limbs5ToNat (p0, p1, p2, p3, p4) : Secp256k1.Scalar.Basic.Field) := by
    rw [hqValue, hpDecomp]
    exact foldComplement_cast lowP p4.toNat
  have hp4 : p4.toNat < 8 := by
    unfold limbs5ToNat Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192 at hpBound
    norm_num at hpBound ⊢
    omega
  have hlowP := Repr.toNat_lt_two256 (Repr.ofLimbs p0 p1 p2 p3)
  have hqTwoCard : limbs5ToNat (q0, q1, q2, q3, carry) <
      2 * Secp256k1.Scalar.Basic.CARD := by
    rw [hqValue]
    change lowP < 2 ^ 256 at hlowP
    norm_num [Secp256k1.Scalar.Basic.CARD] at hlowP hp4 ⊢
    omega
  have hfinish := finishReduceRaw_spec q0 q1 q2 q3 carry hqCarry hqTwoCard
  have hfinalCast :
      (limbs5ToNat (q0, q1, q2, q3, carry) : Secp256k1.Scalar.Basic.Field) =
        (limbs8ToNat (l0, l1, l2, l3, l4, l5, l6, l7) :
          Secp256k1.Scalar.Basic.Field) := hqCast.trans (hpCast.trans hmCast)
  unfold reduce512Raw
  simp only [hmEq, hpEq, hqEq]
  exact ⟨hfinish.1, hfinish.2.trans hfinalCast⟩

/-- Reference multiplication modulo the scalar order.

    This mirrors `secp256k1_scalar_mul`: first compute the 512-bit product with
    `mul512Raw`, then reduce it with `reduce512Raw`.
-/
@[inline] def mulRaw (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Limbs4 :=
  let (l0, l1, l2, l3, l4, l5, l6, l7) := mul512Raw a0 a1 a2 a3 b0 b1 b2 b3
  reduce512Raw l0 l1 l2 l3 l4 l5 l6 l7

/-- Reference squaring modulo the scalar order. -/
@[inline] def squareRaw (a0 a1 a2 a3 : UInt64) : Limbs4 :=
  mulRaw a0 a1 a2 a3 a0 a1 a2 a3

/-- Adding the scalar order to a 256-bit value at the wrap threshold produces
    an exact `2^256` carry. -/
private theorem addModulusRaw_value_of_ge (d0 d1 d2 d3 : UInt64)
    (hge : 2 ^ 256 ≤
      (Repr.ofLimbs d0 d1 d2 d3).toNat + Secp256k1.Scalar.Basic.CARD) :
    let r := addRaw d0 d1 d2 d3 N_0 N_1 N_2 N_3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat + 2 ^ 256 =
      (Repr.ofLimbs d0 d1 d2 d3).toNat + Secp256k1.Scalar.Basic.CARD := by
  let r := addRaw d0 d1 d2 d3 N_0 N_1 N_2 N_3
  have hvalue := addRaw_value d0 d1 d2 d3 N_0 N_1 N_2 N_3
  have hc := addRaw_carry_le_one d0 d1 d2 d3 N_0 N_1 N_2 N_3
  have hout := Repr.toNat_lt_two256
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1)
  change (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat +
      2 ^ 256 * r.2.2.2.2.toNat =
    (Repr.ofLimbs d0 d1 d2 d3).toNat + Repr.modulus.toNat at hvalue
  rw [Repr.modulus_toNat] at hvalue
  change r.2.2.2.2.toNat ≤ 1 at hc
  norm_num [Secp256k1.Scalar.Basic.CARD] at hvalue hout hge ⊢
  have hvaluez :
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) +
          115792089237316195423570985008687907853269984665640564039457584007913129639936 *
            r.2.2.2.2.toNat =
        (Repr.ofLimbs d0 d1 d2 d3).toNat +
          115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    exact_mod_cast hvalue
  have houtz : ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    exact_mod_cast hout
  have hgez : (115792089237316195423570985008687907853269984665640564039457584007913129639936 : Int) ≤
      (Repr.ofLimbs d0 d1 d2 d3).toNat +
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    exact_mod_cast hge
  have hcz : (r.2.2.2.2.toNat : Int) ≤ 1 := by exact_mod_cast hc
  have hz :
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) +
          115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        (Repr.ofLimbs d0 d1 d2 d3).toNat +
          115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    omega
  exact_mod_cast hz

/-- Modular addition returns a canonical scalar representative. -/
theorem addModRaw_lt (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD)
    (hb : (Repr.ofLimbs b0 b1 b2 b3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := addModRaw a0 a1 a2 a3 b0 b1 b2 b3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD := by
  let s := addRaw a0 a1 a2 a3 b0 b1 b2 b3
  let x := Repr.ofLimbs s.1 s.2.1 s.2.2.1 s.2.2.2.1
  change
    let r := reduceRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1
      (s.2.2.2.2 != 0 || checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1)
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat < Secp256k1.Scalar.Basic.CARD
  have hsum := addRaw_value a0 a1 a2 a3 b0 b1 b2 b3
  have hc := addRaw_carry_le_one a0 a1 a2 a3 b0 b1 b2 b3
  change x.toNat + 2 ^ 256 * s.2.2.2.2.toNat =
      (Repr.ofLimbs a0 a1 a2 a3).toNat +
        (Repr.ofLimbs b0 b1 b2 b3).toNat at hsum
  change s.2.2.2.2.toNat ≤ 1 at hc
  have hcheck := checkOverflowRaw_eq_decide s.1 s.2.1 s.2.2.1 s.2.2.2.1
  change checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 =
    decide (x.toNat ≥ Secp256k1.Scalar.Basic.CARD) at hcheck
  by_cases hcarry : s.2.2.2.2 = 0
  · have hcarryBool : (s.2.2.2.2 != 0) = false := by simp [hcarry]
    have hsum0 : x.toNat =
        (Repr.ofLimbs a0 a1 a2 a3).toNat +
          (Repr.ofLimbs b0 b1 b2 b3).toNat := by
      rw [hcarry] at hsum
      norm_num at hsum
      exact hsum
    by_cases hge : Secp256k1.Scalar.Basic.CARD ≤ x.toNat
    · have hcheckTrue : checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 = true := by
        rw [hcheck]
        simp [hge]
      have hreduce := reduceRaw_true_of_ge s.1 s.2.1 s.2.2.1 s.2.2.2.1 hge
      simp only [hcarryBool, Bool.false_or, hcheckTrue]
      rw [hreduce]
      apply (Nat.sub_lt_iff_lt_add hge).2
      omega
    · have hlt : x.toNat < Secp256k1.Scalar.Basic.CARD := Nat.lt_of_not_ge hge
      have hcheckFalse : checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 = false := by
        rw [hcheck]
        simp [hlt]
      simp only [hcarryBool, Bool.false_or, hcheckFalse, reduceRaw]
      exact hlt
  · have hcarryBool : (s.2.2.2.2 != 0) = true := by simp [hcarry]
    have hnatne : s.2.2.2.2.toNat ≠ 0 := by
      intro hzero
      apply hcarry
      apply UInt64.toNat.inj
      simpa using hzero
    have hcarryNat : s.2.2.2.2.toNat = 1 := by
      have hpos : 0 < s.2.2.2.2.toNat := Nat.pos_of_ne_zero hnatne
      omega
    have hslt : x.toNat < Secp256k1.Scalar.Basic.CARD := by
      norm_num [Secp256k1.Scalar.Basic.CARD] at hsum ha hb ⊢
      omega
    have hreduce := reduceRaw_true_of_lt s.1 s.2.1 s.2.2.1 s.2.2.2.1 hslt
    simp only [hcarryBool, Bool.true_or]
    rw [hreduce]
    have hcomp : 2 ^ 256 - Secp256k1.Scalar.Basic.CARD =
        432420386565659656852420866394968145599 := by
      norm_num [Secp256k1.Scalar.Basic.CARD]
    rw [hcomp]
    rw [hcarryNat] at hsum
    norm_num [Secp256k1.Scalar.Basic.CARD] at hsum ha hb ⊢
    have hsumz :
        (x.toNat : Int) +
            115792089237316195423570985008687907853269984665640564039457584007913129639936 =
          (Repr.ofLimbs a0 a1 a2 a3).toNat +
            (Repr.ofLimbs b0 b1 b2 b3).toNat := by exact_mod_cast hsum
    have haz : ((Repr.ofLimbs a0 a1 a2 a3).toNat : Int) <
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      exact_mod_cast ha
    have hbz : ((Repr.ofLimbs b0 b1 b2 b3).toNat : Int) <
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      exact_mod_cast hb
    have hz : (x.toNat : Int) + 432420386565659656852420866394968145599 <
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      omega
    exact_mod_cast hz

/-- Modular addition agrees with addition in the canonical scalar field. -/
theorem addModRaw_cast (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD)
    (hb : (Repr.ofLimbs b0 b1 b2 b3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := addModRaw a0 a1 a2 a3 b0 b1 b2 b3
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
      Secp256k1.Scalar.Basic.Field) =
      ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) +
        ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by
  let s := addRaw a0 a1 a2 a3 b0 b1 b2 b3
  let x := Repr.ofLimbs s.1 s.2.1 s.2.2.1 s.2.2.2.1
  change
    let r := reduceRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1
      (s.2.2.2.2 != 0 || checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1)
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat : Secp256k1.Scalar.Basic.Field) = _
  have hsum := addRaw_value a0 a1 a2 a3 b0 b1 b2 b3
  have hc := addRaw_carry_le_one a0 a1 a2 a3 b0 b1 b2 b3
  change x.toNat + 2 ^ 256 * s.2.2.2.2.toNat =
      (Repr.ofLimbs a0 a1 a2 a3).toNat +
        (Repr.ofLimbs b0 b1 b2 b3).toNat at hsum
  change s.2.2.2.2.toNat ≤ 1 at hc
  have hcheck := checkOverflowRaw_eq_decide s.1 s.2.1 s.2.2.1 s.2.2.2.1
  change checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 =
    decide (x.toNat ≥ Secp256k1.Scalar.Basic.CARD) at hcheck
  rw [← Nat.cast_add]
  by_cases hcarry : s.2.2.2.2 = 0
  · have hcarryBool : (s.2.2.2.2 != 0) = false := by simp [hcarry]
    have hsum0 : x.toNat =
        (Repr.ofLimbs a0 a1 a2 a3).toNat +
          (Repr.ofLimbs b0 b1 b2 b3).toNat := by
      rw [hcarry] at hsum
      norm_num at hsum
      exact hsum
    by_cases hge : Secp256k1.Scalar.Basic.CARD ≤ x.toNat
    · have hcheckTrue : checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 = true := by
        rw [hcheck]
        simp [hge]
      have hreduce := reduceRaw_true_of_ge s.1 s.2.1 s.2.2.1 s.2.2.2.1 hge
      simp only [hcarryBool, Bool.false_or, hcheckTrue]
      rw [hreduce]
      apply cast_eq_of_add_card_eq
      rw [Nat.sub_add_cancel hge, hsum0]
    · have hlt : x.toNat < Secp256k1.Scalar.Basic.CARD := Nat.lt_of_not_ge hge
      have hcheckFalse : checkOverflowRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 = false := by
        rw [hcheck]
        simp [hlt]
      simp [hcarryBool, hcheckFalse, reduceRaw]
      rw [hsum0]
      exact Nat.cast_add _ _
  · have hcarryBool : (s.2.2.2.2 != 0) = true := by simp [hcarry]
    have hnatne : s.2.2.2.2.toNat ≠ 0 := by
      intro hzero
      apply hcarry
      apply UInt64.toNat.inj
      simpa using hzero
    have hcarryNat : s.2.2.2.2.toNat = 1 := by
      have hpos : 0 < s.2.2.2.2.toNat := Nat.pos_of_ne_zero hnatne
      omega
    have hslt : x.toNat < Secp256k1.Scalar.Basic.CARD := by
      rw [hcarryNat] at hsum
      norm_num [Secp256k1.Scalar.Basic.CARD] at hsum ha hb ⊢
      omega
    have hreduce := reduceRaw_true_of_lt s.1 s.2.1 s.2.2.1 s.2.2.2.1 hslt
    simp only [hcarryBool, Bool.true_or]
    rw [hreduce]
    apply cast_eq_of_add_card_eq
    rw [hcarryNat] at hsum
    norm_num [Secp256k1.Scalar.Basic.CARD] at hsum ⊢
    have hsumz :
        (x.toNat : Int) +
            115792089237316195423570985008687907853269984665640564039457584007913129639936 =
          (Repr.ofLimbs a0 a1 a2 a3).toNat +
            (Repr.ofLimbs b0 b1 b2 b3).toNat := by exact_mod_cast hsum
    have hz :
        (x.toNat + 432420386565659656852420866394968145599 : Int) +
            115792089237316195423570985008687907852837564279074904382605163141518161494337 =
          (Repr.ofLimbs a0 a1 a2 a3).toNat +
            (Repr.ofLimbs b0 b1 b2 b3).toNat := by
      omega
    exact_mod_cast hz

/-- Modular subtraction returns a canonical scalar representative. -/
theorem subModRaw_lt (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD)
    (hb : (Repr.ofLimbs b0 b1 b2 b3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := subModRaw a0 a1 a2 a3 b0 b1 b2 b3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD := by
  let s := subRaw a0 a1 a2 a3 b0 b1 b2 b3
  let x := Repr.ofLimbs s.1 s.2.1 s.2.2.1 s.2.2.2.1
  rw [subModRaw_eq_finish]
  rw [show subRaw a0 a1 a2 a3 b0 b1 b2 b3 = s from rfl]
  simp only
  have hdiff := subRaw_value a0 a1 a2 a3 b0 b1 b2 b3
  have hc := subRaw_borrow_le_one a0 a1 a2 a3 b0 b1 b2 b3
  change x.toNat + (Repr.ofLimbs b0 b1 b2 b3).toNat =
      (Repr.ofLimbs a0 a1 a2 a3).toNat + 2 ^ 256 * s.2.2.2.2.toNat at hdiff
  change s.2.2.2.2.toNat ≤ 1 at hc
  by_cases hborrow : s.2.2.2.2 = 0
  · rw [hborrow, finishSubRaw_zero]
    rw [hborrow] at hdiff
    norm_num at hdiff
    have hxlt : x.toNat < Secp256k1.Scalar.Basic.CARD := by omega
    simpa [x] using hxlt
  · rw [finishSubRaw_of_ne_zero _ _ _ _ _ hborrow]
    have hnatne : s.2.2.2.2.toNat ≠ 0 := by
      intro hzero
      apply hborrow
      apply UInt64.toNat.inj
      simpa using hzero
    have hborrowNat : s.2.2.2.2.toNat = 1 := by
      have hpos : 0 < s.2.2.2.2.toNat := Nat.pos_of_ne_zero hnatne
      omega
    rw [hborrowNat] at hdiff
    have hge : 2 ^ 256 ≤ x.toNat + Secp256k1.Scalar.Basic.CARD := by
      norm_num [Secp256k1.Scalar.Basic.CARD] at hdiff hb ⊢
      omega
    have hresult := addModulusRaw_value_of_ge s.1 s.2.1 s.2.2.1 s.2.2.2.1 hge
    let r := addRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 N_0 N_1 N_2 N_3
    change (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat + 2 ^ 256 =
      x.toNat + Secp256k1.Scalar.Basic.CARD at hresult
    have hresultz :
        ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) +
            115792089237316195423570985008687907853269984665640564039457584007913129639936 =
          x.toNat +
            115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      norm_num [Secp256k1.Scalar.Basic.CARD] at hresult
      exact_mod_cast hresult
    have hdiffz : (x.toNat : Int) + (Repr.ofLimbs b0 b1 b2 b3).toNat =
        (Repr.ofLimbs a0 a1 a2 a3).toNat +
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num at hdiff
      exact_mod_cast hdiff
    have haz : ((Repr.ofLimbs a0 a1 a2 a3).toNat : Int) <
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      norm_num [Secp256k1.Scalar.Basic.CARD] at ha
      exact_mod_cast ha
    have hxbound := Repr.toNat_lt_two256 x
    have hxboundz : (x.toNat : Int) <
        115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num at hxbound
      exact_mod_cast hxbound
    have hz : ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) <
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      omega
    exact_mod_cast hz

/-- Modular subtraction agrees with subtraction in the canonical scalar field. -/
theorem subModRaw_cast (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD)
    (hb : (Repr.ofLimbs b0 b1 b2 b3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := subModRaw a0 a1 a2 a3 b0 b1 b2 b3
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
      Secp256k1.Scalar.Basic.Field) =
      ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) -
        ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by
  let s := subRaw a0 a1 a2 a3 b0 b1 b2 b3
  let x := Repr.ofLimbs s.1 s.2.1 s.2.2.1 s.2.2.2.1
  rw [subModRaw_eq_finish]
  rw [show subRaw a0 a1 a2 a3 b0 b1 b2 b3 = s from rfl]
  simp only
  have _ := ha
  have hdiff := subRaw_value a0 a1 a2 a3 b0 b1 b2 b3
  have hc := subRaw_borrow_le_one a0 a1 a2 a3 b0 b1 b2 b3
  change x.toNat + (Repr.ofLimbs b0 b1 b2 b3).toNat =
      (Repr.ofLimbs a0 a1 a2 a3).toNat + 2 ^ 256 * s.2.2.2.2.toNat at hdiff
  change s.2.2.2.2.toNat ≤ 1 at hc
  by_cases hborrow : s.2.2.2.2 = 0
  · rw [hborrow, finishSubRaw_zero]
    rw [hborrow] at hdiff
    norm_num at hdiff
    have hz := congrArg (fun n : Nat => (n : Secp256k1.Scalar.Basic.Field)) hdiff
    push_cast at hz
    calc
      (x.toNat : Secp256k1.Scalar.Basic.Field) =
          (x.toNat : Secp256k1.Scalar.Basic.Field) +
            ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) -
              ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by ring
      _ = ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) -
            ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by rw [hz]
  · rw [finishSubRaw_of_ne_zero _ _ _ _ _ hborrow]
    have hnatne : s.2.2.2.2.toNat ≠ 0 := by
      intro hzero
      apply hborrow
      apply UInt64.toNat.inj
      simpa using hzero
    have hborrowNat : s.2.2.2.2.toNat = 1 := by
      have hpos : 0 < s.2.2.2.2.toNat := Nat.pos_of_ne_zero hnatne
      omega
    rw [hborrowNat] at hdiff
    have hge : 2 ^ 256 ≤ x.toNat + Secp256k1.Scalar.Basic.CARD := by
      norm_num [Secp256k1.Scalar.Basic.CARD] at hdiff hb ⊢
      omega
    have hresult := addModulusRaw_value_of_ge s.1 s.2.1 s.2.2.1 s.2.2.2.1 hge
    let r := addRaw s.1 s.2.1 s.2.2.1 s.2.2.2.1 N_0 N_1 N_2 N_3
    change (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat + 2 ^ 256 =
      x.toNat + Secp256k1.Scalar.Basic.CARD at hresult
    have hresultz :
        ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) +
            115792089237316195423570985008687907853269984665640564039457584007913129639936 =
          x.toNat +
            115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      norm_num [Secp256k1.Scalar.Basic.CARD] at hresult
      exact_mod_cast hresult
    have hdiffz : (x.toNat : Int) + (Repr.ofLimbs b0 b1 b2 b3).toNat =
        (Repr.ofLimbs a0 a1 a2 a3).toNat +
          115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      norm_num at hdiff
      exact_mod_cast hdiff
    have heqz :
        ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Int) +
            (Repr.ofLimbs b0 b1 b2 b3).toNat =
          (Repr.ofLimbs a0 a1 a2 a3).toNat +
            115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
      omega
    have heq :
        (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat +
            (Repr.ofLimbs b0 b1 b2 b3).toNat =
          (Repr.ofLimbs a0 a1 a2 a3).toNat + Secp256k1.Scalar.Basic.CARD := by
      norm_num [Secp256k1.Scalar.Basic.CARD]
      exact_mod_cast heqz
    have hz := congrArg (fun n : Nat => (n : Secp256k1.Scalar.Basic.Field)) heq
    simp only [Nat.cast_add] at hz
    have hcard : (Secp256k1.Scalar.Basic.CARD : Secp256k1.Scalar.Basic.Field) = 0 := by
      exact CharP.cast_eq_zero _ _
    rw [hcard, add_zero] at hz
    change
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Secp256k1.Scalar.Basic.Field) = _
    calc
      ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Secp256k1.Scalar.Basic.Field) =
          ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat : Secp256k1.Scalar.Basic.Field) +
            ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) -
              ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by ring
      _ = ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) -
            ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by rw [hz]

/-- The raw zero test is exact on four limbs. -/
private theorem isZeroRaw_eq_true_iff (a0 a1 a2 a3 : UInt64) :
    isZeroRaw a0 a1 a2 a3 = true ↔ a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  unfold isZeroRaw
  bv_decide

/-- Complementing every limb complements the complete 256-bit value. -/
private theorem notRepr_toNat (a0 a1 a2 a3 : UInt64) :
    (Repr.ofLimbs (~~~a0) (~~~a1) (~~~a2) (~~~a3)).toNat =
      2 ^ 256 - 1 - (Repr.ofLimbs a0 a1 a2 a3).toNat := by
  have h0 : (~~~a0).toNat = 2 ^ 64 - 1 - a0.toNat := BitVec.toNat_not
  have h1 : (~~~a1).toNat = 2 ^ 64 - 1 - a1.toNat := BitVec.toNat_not
  have h2 : (~~~a2).toNat = 2 ^ 64 - 1 - a2.toNat := BitVec.toNat_not
  have h3 : (~~~a3).toNat = 2 ^ 64 - 1 - a3.toNat := BitVec.toNat_not
  have ha0 := a0.toNat_lt_size
  have ha1 := a1.toNat_lt_size
  have ha2 := a2.toNat_lt_size
  have ha3 := a3.toNat_lt_size
  norm_num [UInt64.size] at ha0 ha1 ha2 ha3
  unfold Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192
  norm_num at h0 h1 h2 h3 ⊢
  omega

/-- The incremented modulus limbs denote the scalar order plus one. -/
private theorem incrementedModulus_toNat :
    (Repr.ofLimbs (N_0 + 1) N_1 N_2 N_3).toNat =
      Secp256k1.Scalar.Basic.CARD + 1 := by
  norm_num [Repr.toNat, Repr.ofLimbs, N_0, N_1, N_2, N_3, TWO64, TWO128, TWO192,
    UInt64.toNat_ofNat, Secp256k1.Scalar.Basic.CARD]

/-- Masking a word by 64 one-bits leaves it unchanged. -/
private theorem and_max_eq (x : UInt64) : x &&& 0xffffffffffffffff = x := by
  bv_decide

/-- The nonzero libsecp256k1 negation path sums with its input to the order. -/
private theorem negRaw_nonzero_value (a0 a1 a2 a3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD)
    (hzero : isZeroRaw a0 a1 a2 a3 = false) :
    let r := negRaw a0 a1 a2 a3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat +
        (Repr.ofLimbs a0 a1 a2 a3).toNat = Secp256k1.Scalar.Basic.CARD := by
  let q := addRaw (~~~a0) (~~~a1) (~~~a2) (~~~a3) (N_0 + 1) N_1 N_2 N_3
  have hvalue := addRaw_value (~~~a0) (~~~a1) (~~~a2) (~~~a3)
    (N_0 + 1) N_1 N_2 N_3
  have hc := addRaw_carry_le_one (~~~a0) (~~~a1) (~~~a2) (~~~a3)
    (N_0 + 1) N_1 N_2 N_3
  change
    (Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1).toNat +
        2 ^ 256 * q.2.2.2.2.toNat =
      (Repr.ofLimbs (~~~a0) (~~~a1) (~~~a2) (~~~a3)).toNat +
        (Repr.ofLimbs (N_0 + 1) N_1 N_2 N_3).toNat at hvalue
  change q.2.2.2.2.toNat ≤ 1 at hc
  rw [notRepr_toNat, incrementedModulus_toNat] at hvalue
  have hapos : 0 < (Repr.ofLimbs a0 a1 a2 a3).toNat := by
    by_contra h
    have hnat : (Repr.ofLimbs a0 a1 a2 a3).toNat = 0 := Nat.eq_zero_of_not_pos h
    have hrepr : Repr.ofLimbs a0 a1 a2 a3 = Repr.zero := Repr.toNat_injective hnat
    have hz : isZeroRaw a0 a1 a2 a3 = true := by
      cases hrepr
      rfl
    simp [hz] at hzero
  have hout := Repr.toNat_lt_two256
    (Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1)
  have hvalue' :
      (Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1).toNat +
          2 ^ 256 * q.2.2.2.2.toNat + (Repr.ofLimbs a0 a1 a2 a3).toNat =
        2 ^ 256 + Secp256k1.Scalar.Basic.CARD := by
    norm_num [Secp256k1.Scalar.Basic.CARD] at hvalue ha ⊢
    omega
  have hvaluez :
      ((Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1).toNat : Int) +
          115792089237316195423570985008687907853269984665640564039457584007913129639936 *
            q.2.2.2.2.toNat + (Repr.ofLimbs a0 a1 a2 a3).toNat =
        115792089237316195423570985008687907853269984665640564039457584007913129639936 +
          115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    norm_num [Secp256k1.Scalar.Basic.CARD] at hvalue'
    exact_mod_cast hvalue'
  have houtz : ((Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1).toNat : Int) <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hout
    exact_mod_cast hout
  have hcz : (q.2.2.2.2.toNat : Int) ≤ 1 := by exact_mod_cast hc
  have haposz : (0 : Int) < (Repr.ofLimbs a0 a1 a2 a3).toNat := by exact_mod_cast hapos
  have haz : ((Repr.ofLimbs a0 a1 a2 a3).toNat : Int) <
      115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    norm_num [Secp256k1.Scalar.Basic.CARD] at ha
    exact_mod_cast ha
  have heqz :
      ((Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1).toNat : Int) +
          (Repr.ofLimbs a0 a1 a2 a3).toNat =
        115792089237316195423570985008687907852837564279074904382605163141518161494337 := by
    omega
  have heq :
      (Repr.ofLimbs q.1 q.2.1 q.2.2.1 q.2.2.2.1).toNat +
          (Repr.ofLimbs a0 a1 a2 a3).toNat = Secp256k1.Scalar.Basic.CARD := by
    norm_num [Secp256k1.Scalar.Basic.CARD]
    exact_mod_cast heqz
  have hneg : negRaw a0 a1 a2 a3 =
      (q.1, q.2.1, q.2.2.1, q.2.2.2.1) := by
    unfold negRaw
    rw [hzero]
    simp only [Bool.false_eq_true, if_false]
    change
      (q.1 &&& 0xffffffffffffffff, q.2.1 &&& 0xffffffffffffffff,
        q.2.2.1 &&& 0xffffffffffffffff, q.2.2.2.1 &&& 0xffffffffffffffff) =
        (q.1, q.2.1, q.2.2.1, q.2.2.2.1)
    simp only [and_max_eq]
  rw [hneg]
  exact heq

/-- Modular negation returns a canonical scalar representative. -/
theorem negRaw_lt (a0 a1 a2 a3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := negRaw a0 a1 a2 a3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD := by
  by_cases hzero : isZeroRaw a0 a1 a2 a3 = true
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := (isZeroRaw_eq_true_iff a0 a1 a2 a3).mp hzero
    norm_num [negRaw, isZeroRaw, Secp256k1.Scalar.Basic.CARD,
      Repr.toNat, Repr.ofLimbs, addCarry]
  · have hzeroFalse := Bool.eq_false_of_not_eq_true hzero
    have hvalue := negRaw_nonzero_value a0 a1 a2 a3 ha hzeroFalse
    have hapos : 0 < (Repr.ofLimbs a0 a1 a2 a3).toNat := by
      by_contra h
      have hnat := Nat.eq_zero_of_not_pos h
      have hrepr : Repr.ofLimbs a0 a1 a2 a3 = Repr.zero := Repr.toNat_injective hnat
      apply hzero
      cases hrepr
      rfl
    omega

/-- Modular negation agrees with negation in the canonical scalar field. -/
theorem negRaw_cast (a0 a1 a2 a3 : UInt64)
    (ha : (Repr.ofLimbs a0 a1 a2 a3).toNat < Secp256k1.Scalar.Basic.CARD) :
    let r := negRaw a0 a1 a2 a3
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
      Secp256k1.Scalar.Basic.Field) =
      -((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) := by
  by_cases hzero : isZeroRaw a0 a1 a2 a3 = true
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := (isZeroRaw_eq_true_iff a0 a1 a2 a3).mp hzero
    norm_num [negRaw, isZeroRaw, Repr.toNat, Repr.ofLimbs, addCarry]
  · have hvalue := negRaw_nonzero_value a0 a1 a2 a3 ha
      (Bool.eq_false_of_not_eq_true hzero)
    have hz := congrArg (fun n : Nat => (n : Secp256k1.Scalar.Basic.Field)) hvalue
    simp only [Nat.cast_add] at hz
    have hcard : (Secp256k1.Scalar.Basic.CARD : Secp256k1.Scalar.Basic.Field) = 0 := by
      exact CharP.cast_eq_zero _ _
    rw [hcard] at hz
    calc
      _ = _ + ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) -
          ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) := by ring
      _ = -((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) := by rw [hz]; ring

/-- Modular multiplication returns a canonical scalar representative. -/
theorem mulRaw_lt (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    : let r := mulRaw a0 a1 a2 a3 b0 b1 b2 b3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD := by
  generalize hlEq : mul512Raw a0 a1 a2 a3 b0 b1 b2 b3 = l
  rcases l with ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩
  unfold mulRaw
  rw [hlEq]
  exact (reduce512Raw_spec l0 l1 l2 l3 l4 l5 l6 l7).1

/-- Modular multiplication agrees with multiplication in the canonical scalar field. -/
theorem mulRaw_cast (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    : let r := mulRaw a0 a1 a2 a3 b0 b1 b2 b3
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
      Secp256k1.Scalar.Basic.Field) =
      ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) *
        ((Repr.ofLimbs b0 b1 b2 b3).toNat : Secp256k1.Scalar.Basic.Field) := by
  generalize hlEq : mul512Raw a0 a1 a2 a3 b0 b1 b2 b3 = l
  have hl := mul512Raw_value a0 a1 a2 a3 b0 b1 b2 b3
  rw [hlEq] at hl
  rcases l with ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩
  have hr := (reduce512Raw_spec l0 l1 l2 l3 l4 l5 l6 l7).2
  rw [hl] at hr
  unfold mulRaw
  rw [hlEq]
  simpa only [Nat.cast_mul] using hr

/-- Modular squaring returns a canonical scalar representative. -/
theorem squareRaw_lt (a0 a1 a2 a3 : UInt64) :
    let r := squareRaw a0 a1 a2 a3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD := by
  simpa only [squareRaw] using mulRaw_lt a0 a1 a2 a3 a0 a1 a2 a3

/-- Modular squaring agrees with squaring in the canonical scalar field. -/
theorem squareRaw_cast (a0 a1 a2 a3 : UInt64) :
    let r := squareRaw a0 a1 a2 a3
    ((Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat :
      Secp256k1.Scalar.Basic.Field) =
      ((Repr.ofLimbs a0 a1 a2 a3).toNat : Secp256k1.Scalar.Basic.Field) ^ 2 := by
  simpa only [squareRaw, pow_two] using mulRaw_cast a0 a1 a2 a3 a0 a1 a2 a3

end Reduction
end Secp256k1.Scalar.Fast
