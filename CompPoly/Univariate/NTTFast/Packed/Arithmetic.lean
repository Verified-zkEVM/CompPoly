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

/-- Add canonical Montgomery residues without converting their representation. -/
@[inline] def add (x y : UInt32) : UInt32 :=
  let z := x + y
  if z < P.modulus32 then z else z - P.modulus32

/-- Subtract canonical Montgomery residues. -/
@[inline] def sub (x y : UInt32) : UInt32 :=
  if y ≤ x then x - y else x + P.modulus32 - y

/-- Multiply canonical Montgomery residues with the proved native reduction. -/
@[inline] def mul (x y : UInt32) : UInt32 :=
  reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv (x.toUInt64 * y.toUInt64)

/-- Decode a Montgomery coordinate, rejecting a noncanonical word. -/
@[inline] def ofWord (x : UInt32) : FastField p :=
  if h : x.toNat < p then ⟨x, h⟩ else 0

variable {p}

@[simp] theorem ofWord_val (x : FastField p) : ofWord p x.val = x := by
  apply Subtype.ext
  simp only [ofWord, x.property, ↓reduceDIte]

/-- The raw addition is exactly the carrier's verified addition. -/
theorem add_val (x y : FastField p) : add p x.val y.val = (x + y).val := rfl

/-- The raw subtraction is exactly the carrier's verified subtraction. -/
theorem sub_val (x y : FastField p) : sub p x.val y.val = (x - y).val := by
  simp only [sub, Montgomery.Native32.sub_def, Montgomery.Native32.sub]
  split <;> rfl

/-- The raw multiplication is exactly the carrier's verified multiplication. -/
theorem mul_val (x y : FastField p) : mul p x.val y.val = (x * y).val := rfl

end CompPoly.CPolynomial.NTTFast.Packed
