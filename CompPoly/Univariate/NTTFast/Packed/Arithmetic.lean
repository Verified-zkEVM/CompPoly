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

/-- Multiply canonical Montgomery residues: the native Montgomery quotient, then `reduceOnce`. -/
@[inline] def mul (x y : UInt32) : UInt32 :=
  let z := x.toUInt64 * y.toUInt64
  reduceOnce p (((z + (z.toUInt32 * P.montgomeryNegInv).toUInt64 * P.modulus64) >>> 32).toUInt32)

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

/-- The raw multiplication is exactly the carrier's verified multiplication. -/
theorem mul_val (x y : FastField p) : mul p x.val y.val = (x * y).val := by
  rw [mul, reduceOnce_eq]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
