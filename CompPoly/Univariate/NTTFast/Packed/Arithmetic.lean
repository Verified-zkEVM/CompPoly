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

/-- Add canonical Montgomery residues without converting their representation. -/
@[inline] def add (x y : UInt32) : UInt32 :=
  let z := x + y
  if z < 0x7f000001 then z else z - 0x7f000001

/-- Subtract canonical Montgomery residues. -/
@[inline] def sub (x y : UInt32) : UInt32 :=
  if y ≤ x then x - y else x + 0x7f000001 - y

/-- Multiply canonical Montgomery residues with the proved native reduction. -/
@[inline] def mul (x y : UInt32) : UInt32 :=
  Montgomery.Native32.reduceRaw 0x7f000001 0x7f000001 0x7effffff
    (x.toUInt64 * y.toUInt64)

/-- Decode a Montgomery coordinate, rejecting a noncanonical word. -/
@[inline] def ofWord (x : UInt32) : KoalaBear.Fast.Field :=
  if h : x.toNat < KoalaBear.fieldSize then ⟨x, h⟩ else 0

@[simp] theorem ofWord_val (x : KoalaBear.Fast.Field) : ofWord x.val = x := by
  apply Subtype.ext
  simp only [ofWord, x.property, ↓reduceDIte]

/-- The raw addition is exactly the carrier's verified addition. -/
theorem add_val (x y : KoalaBear.Fast.Field) : add x.val y.val = (x + y).val := rfl

/-- The raw subtraction is exactly the carrier's verified subtraction. -/
theorem sub_val (x y : KoalaBear.Fast.Field) : sub x.val y.val = (x - y).val := by
  simp only [sub, Montgomery.Native32.sub_def, Montgomery.Native32.sub]
  split <;> rfl

/-- The raw multiplication is exactly the carrier's verified multiplication. -/
theorem mul_val (x y : KoalaBear.Fast.Field) : mul x.val y.val = (x * y).val := rfl

/-- The scalar split kernel is multiplication of a field difference. -/
theorem mul_sub_val (w x y : KoalaBear.Fast.Field) :
    mul w.val (sub x.val y.val) = (w * (x - y)).val := by
  rw [sub_val, mul_val]

end CompPoly.CPolynomial.NTTFast.Packed
