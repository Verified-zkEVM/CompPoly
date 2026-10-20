/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.Fast

/-! # Raw KoalaBear coordinates for the packed FFT

The packed kernels operate on Montgomery residues. These lemmas connect their word
arithmetic directly to the existing verified field operations.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Reduce `u < 2 p` below `p` as the unsigned minimum of `u` and `u - p`, which vectorizes to a
single minimum instruction. -/
@[inline] def reduceOnce (u : UInt32) : UInt32 :=
  let v := u - 0x7f000001
  if v < u then v else u

/-- Add canonical Montgomery residues without converting their representation. -/
@[inline] def add (x y : UInt32) : UInt32 :=
  reduceOnce (x + y)

/-- Subtract canonical Montgomery residues: the unsigned minimum of `x - y` and `x - y + p`. -/
@[inline] def sub (x y : UInt32) : UInt32 :=
  let d := x - y
  let e := d + 0x7f000001
  if e < d then e else d

/-- Multiply canonical Montgomery residues: the native Montgomery quotient, then `reduceOnce`. -/
@[inline] def mul (x y : UInt32) : UInt32 :=
  let z := x.toUInt64 * y.toUInt64
  reduceOnce (((z + (z.toUInt32 * 0x7effffff).toUInt64 * 0x7f000001) >>> 32).toUInt32)

/-- Decode a Montgomery coordinate, rejecting a noncanonical word. -/
@[inline] def ofWord (x : UInt32) : KoalaBear.Fast.Field :=
  if h : x.toNat < KoalaBear.fieldSize then ⟨x, h⟩ else 0

@[simp] theorem ofWord_val (x : KoalaBear.Fast.Field) : ofWord x.val = x := by
  apply Subtype.ext
  simp only [ofWord, x.property, ↓reduceDIte]

/-- The minimum form of the conditional subtraction. -/
theorem reduceOnce_eq (u : UInt32) :
    reduceOnce u = if u < 0x7f000001 then u else u - 0x7f000001 := by
  simp only [reduceOnce]
  split <;> split <;> simp_all only [UInt32.lt_iff_toNat_lt, UInt32.toNat_sub, ← UInt32.toNat_inj,
    UInt32.reduceToNat, Nat.not_lt] <;> omega

/-- The raw addition is exactly the carrier's verified addition. -/
theorem add_val (x y : KoalaBear.Fast.Field) : add x.val y.val = (x + y).val := by
  rw [add, reduceOnce_eq]
  rfl

/-- The minimum form of the subtraction of canonical residues. -/
theorem sub_eq (x y : UInt32) (hx : x.toNat < 0x7f000001) (hy : y.toNat < 0x7f000001) :
    sub x y = if y ≤ x then x - y else x + 0x7f000001 - y := by
  simp only [sub]
  split <;> split <;> simp_all only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
    UInt32.toNat_sub, UInt32.toNat_add, ← UInt32.toNat_inj, UInt32.reduceToNat, Nat.not_lt,
    Nat.not_le] <;> omega

/-- The raw subtraction is exactly the carrier's verified subtraction. -/
theorem sub_val (x y : KoalaBear.Fast.Field) : sub x.val y.val = (x - y).val := by
  rw [sub_eq _ _ x.property y.property]
  simp only [Montgomery.Native32.sub_def, Montgomery.Native32.sub]
  split <;> rfl

/-- The raw multiplication is exactly the carrier's verified multiplication. -/
theorem mul_val (x y : KoalaBear.Fast.Field) : mul x.val y.val = (x * y).val := by
  rw [mul, reduceOnce_eq]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
