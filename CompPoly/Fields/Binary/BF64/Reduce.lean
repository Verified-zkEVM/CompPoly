/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Basic
public import CompPoly.Fields.Binary.BF128Ghash.Prelude

/-!
# Reducing a carry-less product modulo the `GF(2^64)` modulus

A product of two 64-bit values occupies 128 bits. Because `x^64 ≡ x^4 + x^3 + x + 1`
(`BF64.mul_pow_reduce`), the high half can be folded back down by a single carry-less
multiplication by `reductionConstant = 0x1B`. Each fold shrinks the excess, and two folds
land back inside 64 bits — no long division is needed.

This mirrors `CompPoly.Fields.Binary.BF128Ghash`'s reduction for the GHASH polynomial,
at the 64-bit width and with this modulus.

## Main definitions

* `highHalf`, `lowHalf` — the two 64-bit halves of a 128-bit value.
* `reductionConstant` — `0x1B`, the modulus below its leading term.
* `foldStep` — one reduction fold.
* `reduce` — two folds and a truncation.

## Main statements

* `toPoly_reductionConstant` — `0x1B` denotes `baseTail`.
* `foldStep_mod` — a fold preserves the residue modulo the modulus.
* `foldStep_lt` — a fold shrinks the value.
* `toPoly_reduce` — `reduce` computes the remainder modulo the modulus.
-/

@[expose] public section

namespace BF64

open Polynomial BinaryField

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

/-! ## Halves of a double-width value -/

/-- The high 64 bits of a 128-bit value. -/
def highHalf (x : BitVec 128) : BitVec 64 := BitVec.setWidth 64 (x >>> 64)

/-- The low 64 bits of a 128-bit value. -/
def lowHalf (x : BitVec 128) : BitVec 64 := BitVec.setWidth 64 x

theorem highHalf_testBit (x : BitVec 128) (i : ℕ) (h : i < 64) :
    (highHalf x).toNat.testBit i = x.toNat.testBit (64 + i) := by
  unfold highHalf
  rw [BitVec.toNat_setWidth, Nat.testBit_mod_two_pow]
  simp only [h, decide_true, Bool.true_and, BitVec.toNat_ushiftRight, Nat.testBit_shiftRight]

theorem lowHalf_testBit (x : BitVec 128) (i : ℕ) (h : i < 64) :
    (lowHalf x).toNat.testBit i = x.toNat.testBit i := by
  unfold lowHalf
  rw [BitVec.toNat_setWidth, Nat.testBit_mod_two_pow]
  simp [h]

/-- Splitting a 128-bit value into `high * x^64 + low`. -/
theorem toPoly_halves (x : BitVec 128) :
    toPoly x = toPoly (highHalf x) * X ^ 64 + toPoly (lowHalf x) := by
  have hhi : (∑ i ∈ Finset.range (128 - 64),
      if x.toNat.testBit (64 + i) then (X : (ZMod 2)[X]) ^ i else 0)
      = toPoly (highHalf x) := by
    rw [toPoly_eq_range (highHalf x), show (128 : ℕ) - 64 = 64 from rfl]
    refine Finset.sum_congr rfl fun i hmem => ?_
    simp only [Finset.mem_range] at hmem
    rw [highHalf_testBit x i hmem]
  have hlo : (∑ i ∈ Finset.range 64,
      if x.toNat.testBit i then (X : (ZMod 2)[X]) ^ i else 0) = toPoly (lowHalf x) := by
    rw [toPoly_eq_range (lowHalf x)]
    refine Finset.sum_congr rfl fun i hmem => ?_
    simp only [Finset.mem_range] at hmem
    rw [lowHalf_testBit x i hmem]
  rw [toPoly_split x 64 (by omega), hhi, hlo]

/-- If `x < 2 ^ (64 + d)` then its high half is below `2 ^ d`. -/
theorem highHalf_lt (x : BitVec 128) {d : ℕ} (hx : x.toNat < 2 ^ (64 + d)) :
    (highHalf x).toNat < 2 ^ d := by
  unfold highHalf
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hx)

theorem lowHalf_lt (x : BitVec 128) : (lowHalf x).toNat < 2 ^ 64 := (lowHalf x).isLt

/-- A carry-less product of values below `2 ^ p` and `2 ^ q` is below `2 ^ (p + q)`. -/
theorem carryLessMul_lt {v w : ℕ} (a b : BitVec v) {p q : ℕ}
    (ha : a.toNat < 2 ^ p) (hb : b.toNat < 2 ^ q) (h : v + v ≤ w) :
    (carryLessMul (w := w) a b).toNat < 2 ^ (p + q) := by
  apply BitVec_lt_two_pow_of_toPoly_degree_lt
  rw [toPoly_carryLessMul a b h]
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  have hda := toPoly_degree_of_lt_two_pow a ha
  have hdb := toPoly_degree_of_lt_two_pow b hb
  rcases eq_or_ne (toPoly a) 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne (toPoly b) 0 with h1 | h1
  · simp [h1]
  · rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree h1] at *
    rw [← Nat.cast_add]
    exact_mod_cast Nat.add_lt_add (by exact_mod_cast hda) (by exact_mod_cast hdb)

/-! ## The reduction fold -/

/-- The reduction constant `0x1B`: the modulus below its leading term,
`x^4 + x^3 + x + 1`. -/
def reductionConstant : BitVec 64 := 0x1B

theorem toPoly_reductionConstant : toPoly reductionConstant = baseTail := by
  have h : reductionConstant = (1 <<< 4) ^^^ (1 <<< 3) ^^^ (1 <<< 1) ^^^ 1 := by decide +kernel
  rw [h, baseTail_eq]
  simp only [toPoly_xor]
  rw [BF128Ghash.toPoly_one_shiftLeft 4 (by omega),
      BF128Ghash.toPoly_one_shiftLeft 3 (by omega),
      BF128Ghash.toPoly_one_shiftLeft 1 (by omega),
      show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      toPoly_one_eq_one (w := 64) (h_w_pos := by omega)]
  ring

theorem reductionConstant_lt : reductionConstant.toNat < 2 ^ 5 := by decide +kernel

/-- One reduction fold: replace the high half's factor of `x^64` by `baseTail`. -/
def foldStep (x : BitVec 128) : BitVec 128 :=
  carryLessMul (w := 128) (highHalf x) reductionConstant ^^^ zeroExtendTo (lowHalf x)

/-- A fold preserves the residue modulo the modulus. -/
theorem foldStep_mod (x : BitVec 128) :
    toPoly (foldStep x) % basePoly = toPoly x % basePoly := by
  unfold foldStep
  rw [toPoly_xor, toPoly_carryLessMul (highHalf x) reductionConstant (by omega),
    toPoly_reductionConstant, toPoly_zeroExtendTo (lowHalf x) (by omega), toPoly_halves x]
  rw [CanonicalEuclideanDomain.add_mod_eq (hn := basePoly_ne_zero)]
  conv_rhs => rw [CanonicalEuclideanDomain.add_mod_eq (hn := basePoly_ne_zero)]
  rw [mul_pow_reduce (toPoly (highHalf x))]

/-- A fold of a value below `2 ^ (64 + d)` lands below `2 ^ (max 64 (d + 5))`. -/
theorem foldStep_lt (x : BitVec 128) {d : ℕ} (hx : x.toNat < 2 ^ (64 + d)) :
    (foldStep x).toNat < 2 ^ (max 64 (d + 5)) := by
  unfold foldStep
  rw [BitVec.toNat_xor]
  refine Nat.xor_lt_two_pow ?_ ?_
  · exact lt_of_lt_of_le
      (carryLessMul_lt (highHalf x) reductionConstant (highHalf_lt x hx)
        reductionConstant_lt (by omega))
      (Nat.pow_le_pow_right (by norm_num) (le_max_right 64 (d + 5)))
  · rw [toNat_zeroExtendTo (lowHalf x) (by omega)]
    exact lt_of_lt_of_le (lowHalf_lt x)
      (Nat.pow_le_pow_right (by norm_num) (le_max_left 64 (d + 5)))

/-! ## Full reduction -/

/-- Reduce a 128-bit carry-less product into the base field: two folds, then truncate. -/
def reduce (x : BitVec 128) : BitVec 64 := lowHalf (foldStep (foldStep x))

/-- Two folds bring any 128-bit value below `2 ^ 64`. -/
theorem foldStep_foldStep_lt (x : BitVec 128) : (foldStep (foldStep x)).toNat < 2 ^ 64 := by
  have h1 : x.toNat < 2 ^ (64 + 64) := x.isLt
  have h2 : (foldStep x).toNat < 2 ^ (64 + 5) := by simpa using foldStep_lt x h1
  simpa using foldStep_lt (foldStep x) h2

/-- Truncation is faithful on values already below `2 ^ 64`. -/
theorem toPoly_lowHalf_of_lt (x : BitVec 128) (h : x.toNat < 2 ^ 64) :
    toPoly (lowHalf x) = toPoly x := by
  rw [toPoly_halves x]
  have hhi : highHalf x = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa using highHalf_lt x (d := 0) (by simpa using h)
  rw [hhi]
  simp [toPoly_zero_eq_zero]

/-- `reduce` computes the remainder of the denoted polynomial modulo the modulus. -/
theorem toPoly_reduce (x : BitVec 128) :
    toPoly (reduce x) = toPoly x % basePoly := by
  unfold reduce
  rw [toPoly_lowHalf_of_lt _ (foldStep_foldStep_lt x)]
  have hmod : toPoly (foldStep (foldStep x)) % basePoly = toPoly x % basePoly := by
    rw [foldStep_mod, foldStep_mod]
  rw [← hmod]
  refine ((Polynomial.mod_eq_self_iff basePoly_ne_zero).mpr ?_).symm
  refine lt_of_lt_of_le (toPoly_degree_of_lt_two_pow _ (foldStep_foldStep_lt x)) ?_
  rw [basePoly_degree]

end BF64
