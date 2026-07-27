/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Common
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Direct Binary-Extension Prelude

Shared small helpers for direct polynomial-basis extensions
`GF(2)[X] / (X^m + tail)`.

The concrete `GF2_48` and `GF2_72` modules use this file for defining-polynomial
metadata, sparse bitmask helpers, and kernel-safe Nat-level carry-less
multiplication checkers. Field instances and irreducibility certificates live in
the concrete field modules.
-/

namespace BinaryField

namespace Extension

open Polynomial

/-- Metadata for a direct binary extension polynomial `X^degree + tail`. -/
structure DefiningPolynomialData where
  degree : Nat
  tail : Polynomial (ZMod 2)
  tailDegree : Nat
  bitmask : Nat
  tail_natDegree : tail.natDegree = tailDegree
  tailDegree_lt_degree : tailDegree < degree

/-- The monic defining polynomial `X^degree + tail` over `GF(2)`. -/
noncomputable def polynomial (data : DefiningPolynomialData) : Polynomial (ZMod 2) :=
  X ^ data.degree + data.tail

/-- `X^degree + tail` is monic of degree `degree` when `tail` has smaller degree. -/
lemma polynomial_isMonicOfDegree (data : DefiningPolynomialData) :
    IsMonicOfDegree (polynomial data) data.degree := by
  unfold polynomial
  exact (Polynomial.isMonicOfDegree_X_pow (ZMod 2) data.degree).add_right (by
    rw [data.tail_natDegree]
    exact data.tailDegree_lt_degree)

/-- The natural degree of the direct-extension defining polynomial. -/
lemma polynomial_natDegree (data : DefiningPolynomialData) :
    (polynomial data).natDegree = data.degree :=
  (polynomial_isMonicOfDegree data).natDegree_eq

/-- The direct-extension defining polynomial is monic. -/
lemma polynomial_monic (data : DefiningPolynomialData) :
    (polynomial data).Monic :=
  (polynomial_isMonicOfDegree data).monic

/-- The direct-extension defining polynomial is nonzero. -/
lemma polynomial_ne_zero (data : DefiningPolynomialData) :
    polynomial data ≠ 0 :=
  (polynomial_monic data).ne_zero

/-- The degree of the direct-extension defining polynomial. -/
lemma polynomial_degree (data : DefiningPolynomialData) :
    (polynomial data).degree = data.degree := by
  rw [degree_eq_natDegree (hp := polynomial_ne_zero data), polynomial_natDegree]

/-- Field cardinality for a degree-`m` binary extension. -/
def fieldSize (degree : Nat) : Nat :=
  2 ^ degree

/-- Multiplicative-group order for a degree-`m` binary extension. -/
def multiplicativeGroupOrder (degree : Nat) : Nat :=
  fieldSize degree - 1

/-- Fold a smooth-refinement schedule from a starting multiplicative order. -/
def foldSmoothSchedule (schedule : Array Nat) (order : Nat) : Nat :=
  schedule.toList.foldl (fun order ell ↦ order / ell) order

/-- Carry-less polynomial multiplication on natural-number bit encodings.

The recursion visits exactly the low `width` bits of `a`, using only kernel-safe
`Nat.testBit`, `Nat.xor`, and `Nat.shiftLeft` primitives.
-/
def clMulNat (a b : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 =>
      let prev := clMulNat a b width
      if a.testBit width then prev ^^^ (b <<< width) else prev

/-- Carry-less squaring on natural-number bit encodings. -/
abbrev clSqNat (a width : Nat) : Nat :=
  clMulNat a a width

/-- XOR together shifts of `a` at the supplied polynomial exponents. -/
def sparseMulByNat : List Nat → Nat → Nat
  | [], _ => 0
  | exponent :: rest, a => (a <<< exponent) ^^^ sparseMulByNat rest a

/-- Kernel-safe Boolean checker for a modular squaring certificate step. -/
def checkSquareStep (width : Nat) (polyExponents : List Nat)
    (rPrev q rNext : BitVec width) : Bool :=
  let lhs := clSqNat rPrev.toNat width
  let rhs := sparseMulByNat polyExponents q.toNat ^^^ rNext.toNat
  lhs == rhs

/-- Kernel-safe Boolean checker for a polynomial division certificate step. -/
def checkDivStep (width : Nat) (a q b r : BitVec width) : Bool :=
  let rhs := clMulNat q.toNat b.toNat width ^^^ r.toNat
  a.toNat == rhs

/-- Zero-extend a bit-vector to a larger width without changing its natural value. -/
lemma zeroExtend_toNat {w W : Nat} (h : w ≤ W) (v : BitVec w) :
    (BitVec.zeroExtend W v).toNat = v.toNat := by
  simp [BitVec.zeroExtend, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (x := v) h)

/-- Zero-extension preserves the polynomial interpretation of a bit-vector. -/
lemma toPoly_zeroExtend {w W : Nat} (h : w ≤ W) (v : BitVec w) :
    toPoly (BitVec.zeroExtend W v) = toPoly v := by
  ext n
  by_cases hnW : n < W
  · by_cases hnw : n < w
    · have hnat := zeroExtend_toNat h v
      simp [toPoly_coeff, hnW, hnw, BitVec.getLsb, hnat]
    · have hwle : w ≤ n := Nat.le_of_not_gt hnw
      have hvbit : v.toNat.testBit n = false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le v.isLt (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hwle))
      have lhs : (toPoly (BitVec.zeroExtend W v)).coeff n = 0 := by
        rw [toPoly_coeff]
        simp [hnW, BitVec.getLsb, zeroExtend_toNat h v, hvbit]
      have rhs : (toPoly v).coeff n = 0 := by
        rw [toPoly_coeff]
        simp [hnw]
      rw [lhs, rhs]
  · have hnw : ¬ n < w := by omega
    simp [toPoly_coeff, hnW, hnw]

/-- `BitVec.ofNat` transports `Nat.xor` to `BitVec.xor`. -/
lemma ofNat_xor {W : Nat} (x y : Nat) :
    (BitVec.ofNat W (x ^^^ y) : BitVec W) =
      (BitVec.ofNat W x : BitVec W) ^^^ (BitVec.ofNat W y : BitVec W) := by
  apply BitVec.eq_of_toNat_eq
  change (x ^^^ y) % 2 ^ W =
    (((BitVec.ofNat W x : BitVec W) ^^^ (BitVec.ofNat W y : BitVec W)).toNat)
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.xor_mod_two_pow]

/-- `BitVec.ofNat` transports left shift modulo the target width. -/
lemma ofNat_shiftLeft {W : Nat} (x n : Nat) :
    (BitVec.ofNat W (x <<< n) : BitVec W) =
      ((BitVec.ofNat W x : BitVec W) <<< n) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.mod_mul_mod]

/-- Bit-vector view of the structural `Nat` carry-less multiplication checker. -/
lemma clMulNat_bv_eq_fold_range (a b : Nat) (W : Nat) :
    ∀ n,
      (BitVec.ofNat W (clMulNat a b n) : BitVec W) =
        (Finset.range n).fold BitVec.xor 0
          (fun i => if a.testBit i then ((BitVec.ofNat W b : BitVec W) <<< i) else 0)
  | 0 => by simp [clMulNat]
  | n + 1 => by
      rw [Finset.range_add_one, Finset.fold_insert (by simp)]
      by_cases hbit : a.testBit n
      · simp [clMulNat, hbit, clMulNat_bv_eq_fold_range a b W n, ofNat_shiftLeft,
          BitVec.xor_comm]
      · simp [clMulNat, hbit, clMulNat_bv_eq_fold_range a b W n]

/-- Polynomial semantics of structural `Nat` carry-less multiplication. -/
lemma toPoly_clMulNat {w : Nat} (a b : BitVec w) :
    toPoly (BitVec.ofNat (2 * w) (clMulNat a.toNat b.toNat w)) = toPoly a * toPoly b := by
  rw [clMulNat_bv_eq_fold_range a.toNat b.toNat (2 * w) w]
  rw [fold_range_xor_eq_foldl]
  rw [toPoly_fold_xor
    (f := fun i =>
      if a.toNat.testBit i = true then ((BitVec.ofNat (2 * w) b.toNat : BitVec (2 * w)) <<< i)
      else 0)]
  conv_rhs =>
    enter [1]
    unfold toPoly
    simp only [BitVec.getLsb]
  change (∑ i ∈ Finset.range w,
      toPoly (if a.toNat.testBit i = true then
        ((BitVec.ofNat (2 * w) b.toNat : BitVec (2 * w)) <<< i) else 0)) =
    (∑ i : Fin w, if a.toNat.testBit i.val = true then (X : Polynomial (ZMod 2)) ^ i.val else 0) *
      toPoly b
  rw [Fin.sum_univ_eq_sum_range
    (f := fun i => if a.toNat.testBit i = true then (X : Polynomial (ZMod 2)) ^ i else 0)
    (n := w)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  by_cases hbit : a.toNat.testBit i
  · simp [hbit]
    have hWidth : w ≤ 2 * w := Nat.le_mul_of_pos_left w (by norm_num : 0 < 2)
    have hb_lt : (BitVec.setWidth (2 * w) b).toNat < 2 ^ w := by
      simpa [BitVec.zeroExtend] using
        (by
          rw [zeroExtend_toNat hWidth b]
          exact b.isLt :
          (BitVec.zeroExtend (2 * w) b).toNat < 2 ^ w)
    have h_no_overflow : w + i ≤ 2 * w := by omega
    rw [toPoly_shiftLeft_no_overflow (d := w) (BitVec.setWidth (2 * w) b)
      (ha := hb_lt) (h_no_overflow := h_no_overflow)]
    have hpoly : toPoly (BitVec.setWidth (2 * w) b) = toPoly b := by
      simpa [BitVec.zeroExtend] using toPoly_zeroExtend hWidth b
    rw [hpoly]
    ring
  · have hbitFalse : a.toNat.testBit i = false := Bool.eq_false_iff.mpr hbit
    simp [hbitFalse, toPoly_zero_eq_zero]

/-- Sparse polynomial with coefficients at the listed exponents. -/
noncomputable def sparsePolynomial : List Nat → Polynomial (ZMod 2)
  | [] => 0
  | exponent :: rest => X ^ exponent + sparsePolynomial rest

/-- Polynomial semantics of `sparseMulByNat`. -/
lemma toPoly_sparseMulByNat {w W : Nat} (hW : w ≤ W) (exponents : List Nat)
    (hExp : ∀ exponent ∈ exponents, w + exponent ≤ W) (a : BitVec w) :
    toPoly (BitVec.ofNat W (sparseMulByNat exponents a.toNat)) =
      toPoly (BitVec.zeroExtend W a) * sparsePolynomial exponents := by
  induction exponents generalizing a with
  | nil =>
      simp [sparseMulByNat, sparsePolynomial, toPoly_zero_eq_zero]
  | cons exponent rest ih =>
      have hExp_head : w + exponent ≤ W := hExp exponent (by simp)
      have hExp_rest : ∀ exponent ∈ rest, w + exponent ≤ W := by
        intro e he
        exact hExp e (by simp [he])
      change toPoly (BitVec.ofNat W ((a.toNat <<< exponent) ^^^ sparseMulByNat rest a.toNat)) =
        toPoly (BitVec.zeroExtend W a) * (X ^ exponent + sparsePolynomial rest)
      rw [ofNat_xor]
      rw [toPoly_xor]
      rw [ih hExp_rest a]
      have ha_lt : (BitVec.zeroExtend W a).toNat < 2 ^ w := by
        rw [zeroExtend_toNat hW a]
        exact a.isLt
      have hshift :
          toPoly (BitVec.ofNat W (a.toNat <<< exponent)) =
            toPoly (BitVec.zeroExtend W a) * X ^ exponent := by
        have hofNat_eq : (BitVec.ofNat W a.toNat : BitVec W) = BitVec.zeroExtend W a := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, zeroExtend_toNat hW a]
          exact Nat.mod_eq_of_lt
            (lt_of_lt_of_le a.isLt (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hW))
        rw [ofNat_shiftLeft, hofNat_eq]
        exact toPoly_shiftLeft_no_overflow (d := w) (BitVec.zeroExtend W a)
          (ha := ha_lt) (h_no_overflow := hExp_head)
      rw [hshift]
      ring

/-- Soundness of the kernel-safe square-step checker. -/
theorem checkSquareStep_correct {width : Nat} {polyExponents : List Nat}
    (hExp : ∀ exponent ∈ polyExponents, width + exponent ≤ 2 * width)
    (rPrev q rNext : BitVec width) :
    checkSquareStep width polyExponents rPrev q rNext = true →
    (toPoly rPrev) ^ 2 =
      toPoly (BitVec.zeroExtend (2 * width) q) * sparsePolynomial polyExponents +
        toPoly rNext := by
  intro h
  unfold checkSquareStep at h
  rw [beq_iff_eq] at h
  have hWidth : width ≤ 2 * width := Nat.le_mul_of_pos_left width (by norm_num : 0 < 2)
  have hBv :
      (BitVec.ofNat (2 * width) (clSqNat rPrev.toNat width) : BitVec (2 * width)) =
        (BitVec.ofNat (2 * width) (sparseMulByNat polyExponents q.toNat ^^^ rNext.toNat) :
          BitVec (2 * width)) := by
    simpa using congrArg (fun n => (BitVec.ofNat (2 * width) n : BitVec (2 * width))) h
  rw [ofNat_xor] at hBv
  apply_fun toPoly at hBv
  rw [toPoly_xor] at hBv
  rw [toPoly_clMulNat rPrev rPrev] at hBv
  rw [← pow_two] at hBv
  rw [toPoly_sparseMulByNat hWidth polyExponents hExp q] at hBv
  have hr : toPoly (BitVec.ofNat (2 * width) rNext.toNat : BitVec (2 * width)) =
      toPoly rNext := by
    have hofNat_eq :
        (BitVec.ofNat (2 * width) rNext.toNat : BitVec (2 * width)) =
          BitVec.zeroExtend (2 * width) rNext := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, zeroExtend_toNat hWidth rNext]
      exact Nat.mod_eq_of_lt
        (lt_of_lt_of_le rNext.isLt (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hWidth))
    rw [hofNat_eq, toPoly_zeroExtend hWidth]
  rw [hr] at hBv
  exact hBv

/-- Soundness of the kernel-safe division-step checker. -/
theorem checkDivStep_correct {width : Nat} (a q b r : BitVec width) :
    checkDivStep width a q b r = true →
    toPoly a = toPoly q * toPoly b + toPoly r := by
  intro h
  unfold checkDivStep at h
  rw [beq_iff_eq] at h
  have hWidth : width ≤ 2 * width := Nat.le_mul_of_pos_left width (by norm_num : 0 < 2)
  have hBv :
      (BitVec.ofNat (2 * width) a.toNat : BitVec (2 * width)) =
        (BitVec.ofNat (2 * width) (clMulNat q.toNat b.toNat width ^^^ r.toNat) :
          BitVec (2 * width)) := by
    simpa using congrArg (fun n => (BitVec.ofNat (2 * width) n : BitVec (2 * width))) h
  rw [ofNat_xor] at hBv
  apply_fun toPoly at hBv
  rw [toPoly_xor, toPoly_clMulNat q b] at hBv
  have ha :
      toPoly (BitVec.ofNat (2 * width) a.toNat : BitVec (2 * width)) = toPoly a := by
    have hofNat_eq :
        (BitVec.ofNat (2 * width) a.toNat : BitVec (2 * width)) =
          BitVec.zeroExtend (2 * width) a := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, zeroExtend_toNat hWidth a]
      exact Nat.mod_eq_of_lt
        (lt_of_lt_of_le a.isLt (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hWidth))
    rw [hofNat_eq, toPoly_zeroExtend hWidth]
  have hr :
      toPoly (BitVec.ofNat (2 * width) r.toNat : BitVec (2 * width)) = toPoly r := by
    have hofNat_eq :
        (BitVec.ofNat (2 * width) r.toNat : BitVec (2 * width)) =
          BitVec.zeroExtend (2 * width) r := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, zeroExtend_toNat hWidth r]
      exact Nat.mod_eq_of_lt
        (lt_of_lt_of_le r.isLt (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hWidth))
    rw [hofNat_eq, toPoly_zeroExtend hWidth]
  rw [ha, hr] at hBv
  exact hBv

/-- Helper lemma for chaining modular Frobenius-squaring certificate steps. -/
lemma chain_step {width : Nat} {P : Polynomial (ZMod 2)} (hP : P ≠ 0) {k : Nat}
    {prev next : Polynomial (ZMod 2)} {qVal : BitVec width}
    (hPrev : X ^ (2 ^ k) % P = prev % P)
    (hStep : prev ^ 2 = toPoly (BitVec.zeroExtend (2 * width) qVal) * P + next) :
    X ^ (2 ^ (k + 1)) % P = next % P := by
  rw [pow_succ', pow_mul, ← pow_mul, mul_comm, pow_mul, pow_two]
  rw [CanonicalEuclideanDomain.mul_mod_eq (hn := hP), hPrev]
  rw [← CanonicalEuclideanDomain.mul_mod_eq (hn := hP), ← pow_two]
  conv_lhs => rw [hStep]
  conv_lhs => rw [CanonicalEuclideanDomain.add_mod_eq (hn := hP)]
  conv_lhs => rw [CanonicalEuclideanDomain.mul_mod_eq (hn := hP)]
  conv_lhs => simp only [EuclideanDomain.mod_self, mul_zero, zero_add]
  conv_lhs => rw [EuclideanDomain.zero_mod, zero_add]
  rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := hP)]

/-- Polynomial interpretation of a one-hot bitvector. -/
lemma toPoly_one_shiftLeft {w : Nat} (n : Nat) (h : n < w) :
    toPoly (1 <<< n : BitVec w) = X ^ n := by
  rw [toPoly]
  rw [Finset.sum_eq_single (⟨n, h⟩ : Fin w)]
  · simp only
    simp only [BitVec.natCast_eq_ofNat, ite_eq_left_iff, Bool.not_eq_true]
    intro h_getLsb_eq_false
    have h_getLsb_eq_true : (BitVec.ofNat w (1 <<< n)).getLsb ⟨n, h⟩ = true := by
      rw [BitVec.getLsb]
      simp only [BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, h, decide_true,
        Nat.testBit_shiftLeft, ge_iff_le, le_refl, tsub_self, Nat.testBit_zero,
        Nat.mod_succ, Bool.and_self]
    rw [h_getLsb_eq_false] at h_getLsb_eq_true
    exact (Bool.false_ne_true h_getLsb_eq_true).elim
  · intro b _ hb_ne_n_fin
    split_ifs with h_lsb
    · exfalso
      have h_getLsb_eq_false : ((1 <<< n) : BitVec w).getLsb b = false := by
        rw [BitVec.getLsb]
        have h_lhs : ((1 <<< n) : BitVec w).toNat = 1 <<< n := by
          simp only [Nat.shiftLeft_eq, one_mul, BitVec.natCast_eq_ofNat,
            BitVec.toNat_ofNat]
          apply Nat.mod_eq_of_lt
          apply Nat.pow_lt_pow_right (ha := by omega) (h := by omega)
        rw [h_lhs]
        rw [Nat.one_shiftLeft]
        rw [Nat.testBit_two_pow]
        let h_ne := Fin.val_ne_of_ne hb_ne_n_fin
        exact decide_eq_false (id (Ne.symm h_ne))
      rw [h_getLsb_eq_false] at h_lsb
      exact (Bool.false_ne_true h_lsb).elim
    · rfl
  · intro h_absurd
    simp at h_absurd

end Extension

end BinaryField
