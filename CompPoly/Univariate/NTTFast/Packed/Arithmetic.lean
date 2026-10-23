/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native32Field

/-! # Raw Montgomery words for the packed FFT

The packed kernels operate on the Montgomery residues of a `Mont32Field p` as raw words, with
the field's constants taken from the instance. These lemmas connect their word arithmetic
directly to the verified field operations of `FastField p`. Kernels using them are
`@[specialize]`d, so a concrete instance turns the constants into immediates.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

open Montgomery.Native32

variable (p : ℕ) [P : Mont32Field p]

/-- Reduce `u < 2 p` below `p` as the unsigned minimum of `u` and `u - p`, which vectorizes to a
single minimum instruction. -/
@[inline] def reduceOnce (u : UInt32) : UInt32 :=
  let v := u - P.modulus32
  if v < u then v else u

/-- Add canonical Montgomery residues without converting their representation. -/
@[inline] def add (x y : UInt32) : UInt32 :=
  reduceOnce p (x + y)

/-- Subtract canonical Montgomery residues: the unsigned minimum of `x - y` and `x - y + p`. -/
@[inline] def sub (x y : UInt32) : UInt32 :=
  let d := x - y
  let e := d + P.modulus32
  if e < d then e else d

/-- Multiply canonical Montgomery residues: the high word of the product minus the high word of
its Montgomery quotient `q = x y p⁻¹ mod 2 ^ 32` times `p`, reduced as in `sub`. The quotient is a
product of words, so the compiler computes it with one vector multiplication per lane group, and
the difference needs no 64-bit comparison. -/
@[inline] def mul (x y : UInt32) : UInt32 :=
  let q := x * y * (0 - P.montgomeryNegInv)
  sub p ((x.toUInt64 * y.toUInt64) >>> 32).toUInt32 ((q.toUInt64 * P.modulus64) >>> 32).toUInt32

/-- Decode a Montgomery coordinate, rejecting a noncanonical word. -/
@[inline] def ofWord (x : UInt32) : FastField p :=
  if h : x.toNat < p then ⟨x, h⟩ else 0

variable {p}

@[simp] theorem ofWord_val (x : FastField p) : ofWord p x.val = x := by
  apply Subtype.ext
  simp only [ofWord, x.property, ↓reduceDIte]

/-- The minimum form of the conditional subtraction. -/
theorem reduceOnce_eq (u : UInt32) :
    reduceOnce p u = if u < P.modulus32 then u else u - P.modulus32 := by
  have := P.modulus_lt_two_pow_31
  have := P.modulus32_toNat
  simp only [reduceOnce]
  split <;> split <;> simp_all only [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub, ← UInt32.toNat_inj,
    Nat.not_lt] <;> omega

/-- The raw addition is exactly the carrier's verified addition. -/
theorem add_val (x y : FastField p) : add p x.val y.val = (x + y).val := by
  rw [add, reduceOnce_eq]
  rfl

/-- The minimum form of the subtraction of canonical residues. -/
theorem sub_eq (x y : UInt32) (hx : x.toNat < p) (hy : y.toNat < p) :
    sub p x y = if y ≤ x then x - y else x + P.modulus32 - y := by
  have := P.modulus_lt_two_pow_31
  have := P.modulus32_toNat
  simp only [sub]
  split <;> split <;> simp_all only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
    UInt32.toNat_sub, UInt32.toNat_add, ← UInt32.toNat_inj, Nat.not_lt, Nat.not_le] <;> omega

/-- The raw subtraction is exactly the carrier's verified subtraction. -/
theorem sub_val (x y : FastField p) : sub p x.val y.val = (x - y).val := by
  rw [sub_eq _ _ x.property y.property]
  simp only [Montgomery.Native32.sub_def, Montgomery.Native32.sub]
  split <;> rfl

/-- The Montgomery quotients `q₁ = L n` and `q₂ = L (-n)` of `L`, with `n m ≡ -1` modulo
`2 ^ 32`: `L + q₁ m ≡ 0` and `q₁ + q₂ ≡ 0`. -/
theorem mont_quotients (L n m : Nat) (hn : n < 2 ^ 32) (hnp : n * m % 2 ^ 32 = 2 ^ 32 - 1) :
    (L + L * n % 2 ^ 32 * m) % 2 ^ 32 = 0 ∧
      (L * n % 2 ^ 32 + L * ((2 ^ 32 - n) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = 0 := by
  constructor
  · have h1 : L * n % 2 ^ 32 * m ≡ L * (2 ^ 32 - 1) [MOD 2 ^ 32] := by
      rw [show L * (2 ^ 32 - 1) = L * ((n * m) % 2 ^ 32) by rw [hnp]]
      refine Nat.ModEq.trans (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)) ?_
      rw [Nat.mul_assoc]
      exact Nat.ModEq.mul_left _ (Nat.mod_modEq _ _).symm
    have h2 := Nat.ModEq.add_left L h1
    have h3 : L + L * (2 ^ 32 - 1) = L * 2 ^ 32 := by
      have h4 : L ≤ L * 2 ^ 32 := Nat.le_mul_of_pos_right L (by decide)
      rw [Nat.mul_sub, Nat.mul_one]
      omega
    rw [h3] at h2
    rw [h2, Nat.mul_mod_left]
  · have h1 : L * n % 2 ^ 32 + L * ((2 ^ 32 - n) % 2 ^ 32) % 2 ^ 32 ≡
        L * n + L * (2 ^ 32 - n) [MOD 2 ^ 32] :=
      Nat.ModEq.add (Nat.mod_modEq _ _)
        (Nat.ModEq.trans (Nat.mod_modEq _ _) (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)))
    rw [← Nat.mul_add, Nat.add_sub_cancel' hn.le] at h1
    rw [h1, Nat.mul_mod_left]

/-- On canonical residues, `mul` is the Montgomery reduction `(z + (z n mod 2 ^ 32) p) / 2 ^ 32`
of the product `z`, reduced once. -/
theorem mul_eq_reduceOnce (x y : UInt32) (hx : x.toNat < p) (hy : y.toNat < p) :
    mul p x y = reduceOnce p (((x.toUInt64 * y.toUInt64 + ((x.toUInt64 * y.toUInt64).toUInt32 *
      P.montgomeryNegInv).toUInt64 * P.modulus64) >>> 32).toUInt32) := by
  have hp31 := P.modulus_lt_two_pow_31
  have hp32 := P.modulus32_toNat
  have hp64 := P.modulus64_toNat
  have hp2 := P.two_lt_modulus
  have hnp := P.montgomeryNegInv_mul_modulus_mod_two_pow_32
  have hn := P.montgomeryNegInv.toNat_lt
  set n := P.montgomeryNegInv.toNat with hn_def
  have hz : x.toNat * y.toNat < p * 2 ^ 32 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx hy.le (by omega))
      (Nat.mul_le_mul_left _ (by omega))
  set z := x.toNat * y.toNat with hz_def
  have hz64 : (x.toUInt64 * y.toUInt64).toNat = z := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    exact Nat.mod_eq_of_lt (by omega)
  set L := z % 2 ^ 32 with hL
  set q1 := L * n % 2 ^ 32 with hq1
  set q2 := L * ((2 ^ 32 - n) % 2 ^ 32) % 2 ^ 32 with hq2
  obtain ⟨c1, c2⟩ := mont_quotients L n p hn hnp
  rw [← hq1, ← hq2] at c2
  rw [← hq1] at c1
  have hq1R : q1 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hq2R : q2 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hq1p : q1 * p < 2 ^ 32 * p := Nat.mul_lt_mul_of_pos_right hq1R (by omega)
  have e32 : (32 : UInt64).toNat % 64 = 32 := rfl
  have hz' : x.toNat * y.toNat % 2 ^ 64 = z := Nat.mod_eq_of_lt (by omega)
  -- The reduction.
  have hA : (reduceOnce p (((x.toUInt64 * y.toUInt64 + ((x.toUInt64 * y.toUInt64).toUInt32 *
      P.montgomeryNegInv).toUInt64 * P.modulus64) >>> 32).toUInt32)).toNat =
      if (z + q1 * p) / 2 ^ 32 < p then (z + q1 * p) / 2 ^ 32 else (z + q1 * p) / 2 ^ 32 - p := by
    have hS : (((x.toUInt64 * y.toUInt64 + ((x.toUInt64 * y.toUInt64).toUInt32 *
        P.montgomeryNegInv).toUInt64 * P.modulus64) >>> 32).toUInt32).toNat =
        (z + q1 * p) / 2 ^ 32 := by
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_add,
        UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_mul, e32, hz', hp64, ← hL]
      rw [Nat.mod_eq_of_lt (show q1 * p < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show z + q1 * p < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    rw [reduceOnce_eq]
    split
    · rename_i h
      rw [UInt32.lt_iff_toNat_lt, hS, hp32] at h
      rw [hS, ite_eq_left h]
    · rename_i h
      rw [UInt32.lt_iff_toNat_lt, hS, hp32] at h
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hS, hp32]; omega)), hS,
        hp32, ite_eq_right h]
  -- The difference of high words.
  have hB : (mul p x y).toNat = if (q2 * p) / 2 ^ 32 ≤ z / 2 ^ 32 then
      z / 2 ^ 32 - (q2 * p) / 2 ^ 32 else z / 2 ^ 32 + p - (q2 * p) / 2 ^ 32 := by
    have hq2p : q2 * p < 2 ^ 32 * p := Nat.mul_lt_mul_of_pos_right hq2R (by omega)
    have hH : ((x.toUInt64 * y.toUInt64) >>> 32).toUInt32.toNat = z / 2 ^ 32 := by
      rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hz64, e32, Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have hH2 : (((x * y * (0 - P.montgomeryNegInv)).toUInt64 * P.modulus64) >>> 32).toUInt32.toNat =
        q2 * p / 2 ^ 32 := by
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.toNat_mul,
        UInt32.toNat_toUInt64, UInt32.toNat_mul, UInt32.toNat_sub, UInt32.toNat_zero, Nat.add_zero,
        e32, hp64, ← hn_def]
      rw [← hz_def, ← hL, ← hq2, Nat.mod_eq_of_lt (show q2 * p < 2 ^ 64 by omega),
        Nat.shiftRight_eq_div_pow]
      exact Nat.mod_eq_of_lt (by omega)
    unfold mul
    dsimp only
    rw [sub_eq _ _ (by rw [hH]; omega) (by rw [hH2]; omega)]
    split
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hH, hH2] at h
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hH, hH2]; omega)), hH,
        hH2, ite_eq_left h]
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hH, hH2] at h
      have hs : (((x.toUInt64 * y.toUInt64) >>> 32).toUInt32 + P.modulus32).toNat =
          z / 2 ^ 32 + p := by
        rw [UInt32.toNat_add, hH, hp32]; exact Nat.mod_eq_of_lt (by omega)
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hs, hH2]; omega)), hs,
        hH2, ite_eq_right h]
  apply UInt32.toNat_inj.mp
  rw [hA, hB]
  have hzL : z = z / 2 ^ 32 * 2 ^ 32 + L := by omega
  rcases Nat.eq_zero_or_pos q1 with h0 | h0
  · have hq20 : q2 = 0 := by omega
    have hL0 : L = 0 := by rw [h0, Nat.zero_mul, Nat.add_zero] at c1; omega
    rw [h0, hq20, Nat.zero_mul, Nat.add_zero, Nat.zero_div]
    split <;> split <;> omega
  · have hq2' : q2 = 2 ^ 32 - q1 := by omega
    have hQ2 : q2 * p = 2 ^ 32 * p - q1 * p := by rw [hq2', Nat.sub_mul]
    have hp1 : p ≤ q1 * p := Nat.le_mul_of_pos_left p h0
    rw [hQ2]
    split <;> split <;> omega

/-- The raw multiplication is exactly the carrier's verified multiplication. -/
theorem mul_val (x y : FastField p) : mul p x.val y.val = (x * y).val := by
  rw [mul_eq_reduceOnce _ _ x.property y.property, reduceOnce_eq]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
