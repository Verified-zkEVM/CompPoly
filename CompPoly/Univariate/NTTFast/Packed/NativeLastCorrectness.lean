/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.NativeLast
public import CompPoly.Univariate.NTTFast.Packed.NativeLast
public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.KernelCorrectness
public import CompPoly.Univariate.NTTFast.Packed.KernelSpecialization
public import CompPoly.Univariate.NTTFast.Packed.StageTail
public import CompPoly.Univariate.NTTFast.Packed.NativeOrderCorrectness
public import CompPoly.Univariate.NTTFast.Packed.StageRefinement
import all CompPoly.Univariate.NTTFast.Packed.NativeOrder
import all CompPoly.Univariate.NTTFast.Packed.Native

/-! # Correctness of the fused final leaf layers

`laneLine` is the field-level expression graph of one lane of `lastHalf`: the four final DIF
layers of one sixteen-word block, exactly as in `leaf16Field`. A kernel call writes, for each
`t < 16`, eight words of line `bitrev (16 c + t)` (`writeLines`); the batch loop covers every
line once, so `lastRev` is the bit-reversed, optionally scaled result of the final layers.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode size_encode_uint32)

/-- Sixteen field coordinates. -/
structure FieldLine where
  w0 : KoalaBear.Fast.Field
  w1 : KoalaBear.Fast.Field
  w2 : KoalaBear.Fast.Field
  w3 : KoalaBear.Fast.Field
  w4 : KoalaBear.Fast.Field
  w5 : KoalaBear.Fast.Field
  w6 : KoalaBear.Fast.Field
  w7 : KoalaBear.Fast.Field
  w8 : KoalaBear.Fast.Field
  w9 : KoalaBear.Fast.Field
  w10 : KoalaBear.Fast.Field
  w11 : KoalaBear.Fast.Field
  w12 : KoalaBear.Fast.Field
  w13 : KoalaBear.Fast.Field
  w14 : KoalaBear.Fast.Field
  w15 : KoalaBear.Fast.Field

/-- Coordinate `t` of a line. -/
def FieldLine.get (y : FieldLine) : Nat → KoalaBear.Fast.Field
  | 0 => y.w0
  | 1 => y.w1
  | 2 => y.w2
  | 3 => y.w3
  | 4 => y.w4
  | 5 => y.w5
  | 6 => y.w6
  | 7 => y.w7
  | 8 => y.w8
  | 9 => y.w9
  | 10 => y.w10
  | 11 => y.w11
  | 12 => y.w12
  | 13 => y.w13
  | 14 => y.w14
  | _ => y.w15

/-- The four final DIF layers of the block at `i`, as in `leaf16Field`. -/
def laneLine (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (b : Array KoalaBear.Fast.Field) : FieldLine :=
  let x0_0 := readField b i 0
  let x0_1 := readField b i 1
  let x0_2 := readField b i 2
  let x0_3 := readField b i 3
  let x0_4 := readField b i 4
  let x0_5 := readField b i 5
  let x0_6 := readField b i 6
  let x0_7 := readField b i 7
  let x0_8 := readField b i 8
  let x0_9 := readField b i 9
  let x0_10 := readField b i 10
  let x0_11 := readField b i 11
  let x0_12 := readField b i 12
  let x0_13 := readField b i 13
  let x0_14 := readField b i 14
  let x0_15 := readField b i 15
  let w0_1 := readField t3 0 1
  let w0_2 := readField t3 0 2
  let w0_3 := readField t3 0 3
  let w0_4 := readField t3 0 4
  let w0_5 := readField t3 0 5
  let w0_6 := readField t3 0 6
  let w0_7 := readField t3 0 7
  let x1_0 := fieldAdd x0_0 x0_8
  let x1_8 := fieldSub x0_0 x0_8
  let x1_1 := fieldAdd x0_1 x0_9
  let x1_9 := fieldMul w0_1 (fieldSub x0_1 x0_9)
  let x1_2 := fieldAdd x0_2 x0_10
  let x1_10 := fieldMul w0_2 (fieldSub x0_2 x0_10)
  let x1_3 := fieldAdd x0_3 x0_11
  let x1_11 := fieldMul w0_3 (fieldSub x0_3 x0_11)
  let x1_4 := fieldAdd x0_4 x0_12
  let x1_12 := fieldMul w0_4 (fieldSub x0_4 x0_12)
  let x1_5 := fieldAdd x0_5 x0_13
  let x1_13 := fieldMul w0_5 (fieldSub x0_5 x0_13)
  let x1_6 := fieldAdd x0_6 x0_14
  let x1_14 := fieldMul w0_6 (fieldSub x0_6 x0_14)
  let x1_7 := fieldAdd x0_7 x0_15
  let x1_15 := fieldMul w0_7 (fieldSub x0_7 x0_15)
  let w1_1 := readField t2 0 1
  let w1_2 := readField t2 0 2
  let w1_3 := readField t2 0 3
  let x2_0 := fieldAdd x1_0 x1_4
  let x2_4 := fieldSub x1_0 x1_4
  let x2_1 := fieldAdd x1_1 x1_5
  let x2_5 := fieldMul w1_1 (fieldSub x1_1 x1_5)
  let x2_2 := fieldAdd x1_2 x1_6
  let x2_6 := fieldMul w1_2 (fieldSub x1_2 x1_6)
  let x2_3 := fieldAdd x1_3 x1_7
  let x2_7 := fieldMul w1_3 (fieldSub x1_3 x1_7)
  let x2_8 := fieldAdd x1_8 x1_12
  let x2_12 := fieldSub x1_8 x1_12
  let x2_9 := fieldAdd x1_9 x1_13
  let x2_13 := fieldMul w1_1 (fieldSub x1_9 x1_13)
  let x2_10 := fieldAdd x1_10 x1_14
  let x2_14 := fieldMul w1_2 (fieldSub x1_10 x1_14)
  let x2_11 := fieldAdd x1_11 x1_15
  let x2_15 := fieldMul w1_3 (fieldSub x1_11 x1_15)
  let w2_1 := readField t1 0 1
  let x3_0 := fieldAdd x2_0 x2_2
  let x3_2 := fieldSub x2_0 x2_2
  let x3_1 := fieldAdd x2_1 x2_3
  let x3_3 := fieldMul w2_1 (fieldSub x2_1 x2_3)
  let x3_4 := fieldAdd x2_4 x2_6
  let x3_6 := fieldSub x2_4 x2_6
  let x3_5 := fieldAdd x2_5 x2_7
  let x3_7 := fieldMul w2_1 (fieldSub x2_5 x2_7)
  let x3_8 := fieldAdd x2_8 x2_10
  let x3_10 := fieldSub x2_8 x2_10
  let x3_9 := fieldAdd x2_9 x2_11
  let x3_11 := fieldMul w2_1 (fieldSub x2_9 x2_11)
  let x3_12 := fieldAdd x2_12 x2_14
  let x3_14 := fieldSub x2_12 x2_14
  let x3_13 := fieldAdd x2_13 x2_15
  let x3_15 := fieldMul w2_1 (fieldSub x2_13 x2_15)
  let x4_0 := fieldAdd x3_0 x3_1
  let x4_1 := fieldSub x3_0 x3_1
  let x4_2 := fieldAdd x3_2 x3_3
  let x4_3 := fieldSub x3_2 x3_3
  let x4_4 := fieldAdd x3_4 x3_5
  let x4_5 := fieldSub x3_4 x3_5
  let x4_6 := fieldAdd x3_6 x3_7
  let x4_7 := fieldSub x3_6 x3_7
  let x4_8 := fieldAdd x3_8 x3_9
  let x4_9 := fieldSub x3_8 x3_9
  let x4_10 := fieldAdd x3_10 x3_11
  let x4_11 := fieldSub x3_10 x3_11
  let x4_12 := fieldAdd x3_12 x3_13
  let x4_13 := fieldSub x3_12 x3_13
  let x4_14 := fieldAdd x3_14 x3_15
  let x4_15 := fieldSub x3_14 x3_15
  ⟨x4_0, x4_1, x4_2, x4_3, x4_4, x4_5, x4_6, x4_7, x4_8, x4_9, x4_10, x4_11, x4_12, x4_13,
    x4_14, x4_15⟩

/-- The fused leaf kernel is the lane graph followed by one splice. -/
theorem leaf16Field_eq_laneLine (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (b : Array KoalaBear.Fast.Field) :
    leaf16Field t3 t2 t1 i b = splice b i.toNat
      #[(laneLine t3 t2 t1 i b).w0, (laneLine t3 t2 t1 i b).w1, (laneLine t3 t2 t1 i b).w2,
        (laneLine t3 t2 t1 i b).w3, (laneLine t3 t2 t1 i b).w4, (laneLine t3 t2 t1 i b).w5,
        (laneLine t3 t2 t1 i b).w6, (laneLine t3 t2 t1 i b).w7, (laneLine t3 t2 t1 i b).w8,
        (laneLine t3 t2 t1 i b).w9, (laneLine t3 t2 t1 i b).w10, (laneLine t3 t2 t1 i b).w11,
        (laneLine t3 t2 t1 i b).w12, (laneLine t3 t2 t1 i b).w13, (laneLine t3 t2 t1 i b).w14,
        (laneLine t3 t2 t1 i b).w15] := by
  unfold leaf16Field laneLine
  rfl

/-- A literal line returns its coordinates. -/
theorem getD_lit_line (y : FieldLine) (k : Nat) (hk : k < 16) :
    (#[y.w0, y.w1, y.w2, y.w3, y.w4, y.w5, y.w6, y.w7, y.w8, y.w9, y.w10, y.w11, y.w12, y.w13,
      y.w14, y.w15] : Array KoalaBear.Fast.Field).getD k 0 = y.get k := by
  interval_cases k <;> rfl

/-- Coordinate `t` of a lane is the fused kernel's coordinate `i + t`. -/
theorem getD_leaf16Field_laneLine (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (b : Array KoalaBear.Fast.Field) (hi : i.toNat + 16 ≤ b.size) (t : Nat) (ht : t < 16) :
    (leaf16Field t3 t2 t1 i b).getD (i.toNat + t) 0 = (laneLine t3 t2 t1 i b).get t := by
  have hsz : ∀ v : Array KoalaBear.Fast.Field, v.size = 16 → i.toNat + v.size ≤ b.size := by
    intro v hv; omega
  rw [leaf16Field_eq_laneLine, getD_splice _ _ _ (hsz _ rfl)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(i.toNat + t < i.toNat) by omega))]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd,
    show i.toNat + t < i.toNat + 16 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  exact getD_lit_line _ t ht

/-- Coordinate `t` of a lane is coordinate `i + t` of the four final DIF layers at `i`. -/
theorem laneLine_get (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (b : Array KoalaBear.Fast.Field) (hi : i.toNat + 16 ≤ b.size)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) (t : Nat)
    (ht : t < 16) :
    (laneLine t3 t2 t1 i b).get t =
      (Expressions.leaf16Stages t3 t2 t1 b i.toNat).getD (i.toNat + t) 0 := by
  rw [← getD_leaf16Field_laneLine t3 t2 t1 i b hi t ht, leaf16Field_eq_expression,
    Expressions.leaf16Field_eq_stages t3 t2 t1 b i hi h3 h2 h1]

/-- Eight words stored at word `idx`, if they fit; a model of a guarded half-line store. -/
def spliceHalf (O : Array UInt32) (idx : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) : Array UInt32 :=
  if idx + 8 ≤ O.size then
    O.extract 0 idx ++ #[v0, v1, v2, v3, v4, v5, v6, v7, 0, 0, 0, 0, 0, 0, 0, 0].extract 0 8 ++
      O.extract (idx + 8) O.size
  else O

@[simp] theorem size_spliceHalf (O : Array UInt32) (idx : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) :
    (spliceHalf O idx v0 v1 v2 v3 v4 v5 v6 v7).size = O.size := by
  unfold spliceHalf
  split
  · simp only [Array.size_append, Array.size_extract, List.size_toArray, List.length_cons,
      List.length_nil]
    omega
  · rfl

/-- A half-line store into packed words. -/
theorem storeWords_half (O : Array UInt32) (off : USize) (idx : Nat) (ho : off.toNat = 4 * idx)
    (hs : (encode O).size < USize.size) (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) :
    Native.storeWords (encode O) off 8 v0 v1 v2 v3 v4 v5 v6 v7 0 0 0 0 0 0 0 0 =
      encode (spliceHalf O idx v0 v1 v2 v3 v4 v5 v6 v7) := by
  unfold spliceHalf
  split
  · rename_i hi
    exact Native.storeWords_replace_encodeWords O off 8 idx (by decide) ho hi hs _ _ _ _ _ _ _ _ _
        _ _ _
      _ _ _ _
  · rename_i hi
    have hf := (Native.storeWords_fits O off 8 idx (by decide) ho hs).not.mpr hi
    simp only [Native.storeWords_eq, ↓reduceIte,
      show (8 : UInt8).toNat = 8 from rfl, show ¬(8 > 16) by decide] at hf ⊢
    exact ite_eq_right_iff.mpr (fun h ↦ absurd h hf)

/-- The byte offset of half `half` of line `bitrev (16 c + T)`. -/
theorem lineOffset (mm : Nat) (hm : 0 < mm) (h32 : mm ≤ 32) (c T half : USize)
    (hT : T.toNat < 16) (hh : half.toNat < 2) (hc : 16 * c.toNat + 16 ≤ 2 ^ mm)
    (hu : 64 * 2 ^ mm < USize.size) :
    (4 * (16 * (reverse32 (16 * c + T).toUInt32 >>> (32 - mm).toUInt32).toUSize +
      8 * half)).toNat =
      4 * (16 * NTT.Transform.bitRevNat mm (16 * c.toNat + T.toNat) + 8 * half.toNat) := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have h32' : 2 ^ mm ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) h32
  have hx : (16 * c + T).toNat = 16 * c.toNat + T.toNat := by
    simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, hsize]
    rw [Nat.mod_eq_of_lt (show 16 * c.toNat < USize.size by omega),
      Nat.mod_eq_of_lt (show 16 * c.toNat + T.toNat < USize.size by omega)]
  have hr : (reverse32 (16 * c + T).toUInt32 >>> (32 - mm).toUInt32).toUSize.toNat =
      NTT.Transform.bitRevNat mm (16 * c.toNat + T.toNat) := by
    rw [UInt32.toNat_toUSize, show (16 * c + T).toUInt32 = (16 * c + T).toNat.toUInt32 from
      UInt32.toFin_inj.mp rfl, hx]
    exact reverse32_shift_eq_bitRevNat mm _ hm h32
  have hg := NTT.Transform.bitRevNat_lt mm (16 * c.toNat + T.toNat)
  simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, hr, hsize]
  rw [Nat.mod_eq_of_lt (show 16 * NTT.Transform.bitRevNat mm (16 * c.toNat + T.toNat) <
      USize.size by omega),
    Nat.mod_eq_of_lt (show 8 * half.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show 16 * NTT.Transform.bitRevNat mm (16 * c.toNat + T.toNat) +
      8 * half.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show 4 * (16 * NTT.Transform.bitRevNat mm (16 * c.toNat + T.toNat) +
      8 * half.toNat) < USize.size by omega)]

/-- Lane `k` of eight. -/
def pick8 (i0 i1 i2 i3 i4 i5 i6 i7 : USize) : Nat → USize
  | 0 => i0
  | 1 => i1
  | 2 => i2
  | 3 => i3
  | 4 => i4
  | 5 => i5
  | 6 => i6
  | _ => i7

/-- Half `half` of the sixteen lines `bitrev (16 c + t)`, word `8 half + k` from `val t k`. -/
def lineStores (O : Array UInt32) (mm c half : Nat) (val : Nat → Nat → UInt32) : Array UInt32 :=
  (List.range 16).foldl (fun O t ↦ spliceHalf O
    (16 * NTT.Transform.bitRevNat mm (16 * c + t) + 8 * half)
    (val t 0) (val t 1) (val t 2) (val t 3) (val t 4) (val t 5) (val t 6) (val t 7)) O

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- One kernel call stores the final layers of its eight lanes into sixteen half lines. -/
theorem lastHalf_encodeWords (t3 t2 t1 U : Array KoalaBear.Fast.Field) (i0 i1 i2 i3 i4 i5 i6 i7 c
    half :
    USize) (mm : Nat) (f : KoalaBear.Fast.Field) (sc : Bool) (O : Array UInt32)
    (hm : 0 < mm) (hm32 : mm ≤ 32) (hh : half.toNat < 2) (hc : 16 * c.toNat + 16 ≤ 2 ^ mm)
    (hu : 64 * 2 ^ mm < USize.size) (hs : (encode O).size < USize.size) (h) :
    Native.lastHalf (encode t3) (encode t2) (encode t1) (encode U)
      i0 i1 i2 i3 i4 i5 i6 i7 c (32 - mm).toUInt32 half f.val sc (encode O) h =
      encode (lineStores O mm c.toNat half.toNat fun t k ↦
        Native.scaleWord f.val sc
          ((laneLine t3 t2 t1 (pick8 i0 i1 i2 i3 i4 i5 i6 i7 k) U).get t).val) := by
  unfold Native.lastHalf
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 0 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    hs]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 1 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 2 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 3 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 4 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 5 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 6 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 7 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 8 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 9 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 10 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 11 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 12 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 13 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 14 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  rw [storeWords_half _ _ _
    (lineOffset mm hm hm32 c 15 half (by simp only [USize.reduceToNat]; omega) hh hc hu)
    (by simp only [size_encode_uint32, size_spliceHalf] at hs ⊢; exact hs)]
  unfold lineStores
  rw [show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, laneLine, FieldLine.get, pick8,
    readField, fieldAdd, fieldSub, fieldMul, USize.reduceToNat, Nat.add_zero, Nat.zero_add]

/-- In range, a half-line store is a splice of eight words. -/
theorem spliceHalf_eq (O : Array UInt32) (idx : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32)
    (hi : idx + 8 ≤ O.size) :
    spliceHalf O idx v0 v1 v2 v3 v4 v5 v6 v7 = splice O idx #[v0, v1, v2, v3, v4, v5, v6, v7] := by
  unfold spliceHalf splice
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi)]
  rfl

/-- A stored half line changes exactly its eight words. -/
theorem getD_spliceHalf (O : Array UInt32) (idx : Nat) (g : Nat → UInt32) (hi : idx + 8 ≤ O.size)
    (n : Nat) :
    (spliceHalf O idx (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)).getD n 0 =
      if idx ≤ n ∧ n < idx + 8 then g (n - idx) else O.getD n 0 := by
  rw [spliceHalf_eq _ _ _ _ _ _ _ _ _ _ hi, getD_splice _ _ _ (by
    simp only [List.size_toArray, List.length_cons, List.length_nil]; omega)]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd]
  by_cases h1 : n < idx
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : n < idx + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega,
        h2⟩)]
      obtain ⟨k, rfl, hk⟩ : ∃ k, n = idx + k ∧ k < 8 := ⟨n - idx, by omega, by omega⟩
      rw [Nat.add_sub_cancel_left]
      interval_cases k <;> rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

@[simp] theorem size_lineStores (O : Array UInt32) (mm c half : Nat) (val : Nat → Nat → UInt32) :
    (lineStores O mm c half val).size = O.size := by
  unfold lineStores
  suffices h : ∀ (l : List Nat) (A : Array UInt32), A.size = O.size →
      (l.foldl (fun O t ↦ spliceHalf O (16 * NTT.Transform.bitRevNat mm (16 * c + t) + 8 * half)
        (val t 0) (val t 1) (val t 2) (val t 3) (val t 4) (val t 5) (val t 6) (val t 7))
        A).size = O.size from h _ O rfl
  intro l
  induction l with
  | nil => intro A hA; exact hA
  | cons t l ih => intro A hA; exact ih _ (by rw [size_spliceHalf, hA])

/-- One kernel call: word `n` is set iff its line reverses into batch `c` and its half is
`half`; then it is lane `n % 8` at coordinate `bitrev (n / 16) % 16`. -/
theorem getD_lineStores (O : Array UInt32) (mm c half : Nat) (val : Nat → Nat → UInt32)
    (hO : O.size = 16 * 2 ^ mm) (hc : 16 * c + 16 ≤ 2 ^ mm) (hh : half < 2) (n : Nat) :
    (lineStores O mm c half val).getD n 0 =
      if n < 16 * 2 ^ mm ∧ NTT.Transform.bitRevNat mm (n / 16) / 16 = c ∧ n % 16 / 8 = half then
        val (NTT.Transform.bitRevNat mm (n / 16) % 16) (n % 8)
      else O.getD n 0 := by
  unfold lineStores
  suffices h : ∀ T ≤ 16,
      ((List.range T).foldl (fun O t ↦ spliceHalf O
        (16 * NTT.Transform.bitRevNat mm (16 * c + t) + 8 * half)
        (val t 0) (val t 1) (val t 2) (val t 3) (val t 4) (val t 5) (val t 6) (val t 7))
        O).getD n 0 =
      if n < 16 * 2 ^ mm ∧ NTT.Transform.bitRevNat mm (n / 16) / 16 = c ∧
          NTT.Transform.bitRevNat mm (n / 16) % 16 < T ∧ n % 16 / 8 = half then
        val (NTT.Transform.bitRevNat mm (n / 16) % 16) (n % 8)
      else O.getD n 0 by
    rw [h 16 le_rfl]
    congr 1
    apply propext
    have := Nat.mod_lt (NTT.Transform.bitRevNat mm (n / 16)) (show 0 < 16 by decide)
    constructor
    · intro hx; exact ⟨hx.1, hx.2.1, hx.2.2.2⟩
    · intro hx; exact ⟨hx.1, hx.2.1, this, hx.2.2⟩
  intro T
  induction T with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, false_and, and_false,
      ↓reduceIte]
  | succ T ih =>
    intro hT
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hsz : ((List.range T).foldl (fun O t ↦ spliceHalf O
        (16 * NTT.Transform.bitRevNat mm (16 * c + t) + 8 * half)
        (val t 0) (val t 1) (val t 2) (val t 3) (val t 4) (val t 5) (val t 6) (val t 7))
        O).size = O.size := by
      have := size_lineStores O mm c half val
      clear ih
      induction T with
      | zero => rfl
      | succ T ih' =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, size_spliceHalf,
          ih' (by omega)]
    have hg := NTT.Transform.bitRevNat_lt mm (16 * c + T)
    rw [getD_spliceHalf _ _ (val T) (by rw [hsz, hO]; omega), ih (by omega)]
    have hinv : NTT.Transform.bitRevNat mm (NTT.Transform.bitRevNat mm (16 * c + T)) = 16 * c + T :=
      NTT.Transform.bitRevNat_involutive _ _ (by omega)
    by_cases hn : n < 16 * 2 ^ mm ∧ NTT.Transform.bitRevNat mm (n / 16) = 16 * c + T
    · have hq : n / 16 = NTT.Transform.bitRevNat mm (16 * c + T) := by
        rw [← hn.2, NTT.Transform.bitRevNat_involutive _ _ (by omega)]
      by_cases hhalf : n % 16 / 8 = half
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨hn.1, by omega, by omega, hhalf⟩), hn.2]
        congr 1 <;> omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    · have hout : ¬(16 * NTT.Transform.bitRevNat mm (16 * c + T) + 8 * half ≤ n ∧
          n < 16 * NTT.Transform.bitRevNat mm (16 * c + T) + 8 * half + 8) := by
        intro hin
        apply hn
        have hq : n / 16 = NTT.Transform.bitRevNat mm (16 * c + T) := by omega
        exact ⟨by omega, by rw [hq, hinv]⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hout)]
      by_cases hn2 : n < 16 * 2 ^ mm ∧ NTT.Transform.bitRevNat mm (n / 16) / 16 = c
      · have hne : NTT.Transform.bitRevNat mm (n / 16) ≠ 16 * c + T := fun h ↦ hn ⟨hn2.1, h⟩
        congr 1
        apply propext
        constructor
        · intro hx; exact ⟨hx.1, hx.2.1, by omega, hx.2.2.2⟩
        · intro hx; exact ⟨hx.1, hx.2.1, by omega, hx.2.2.2⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by tauto)),
          ite_eq_right_of_eq_false _ _ (eq_false (by tauto))]

/-- A lane's word index. -/
theorem laneIndex (v Lw c : USize) (hv : v.toNat < 16) (hc : 16 * c.toNat + 16 ≤ Lw.toNat)
    (hL : 16 * Lw.toNat < USize.size) :
    (v * Lw + 16 * c).toNat = v.toNat * Lw.toNat + 16 * c.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hvL : v.toNat * Lw.toNat ≤ 15 * Lw.toNat := Nat.mul_le_mul_right _ (by omega)
  simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, hsize]
  rw [Nat.mod_eq_of_lt (show v.toNat * Lw.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show 16 * c.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show v.toNat * Lw.toNat + 16 * c.toNat < USize.size by omega)]

/-- Lane `k` of half `0` reads block `bitrev₄ k`. -/
theorem pick8_lanes0 (Lw c : USize) (hc : 16 * c.toNat + 16 ≤ Lw.toNat)
    (hL : 16 * Lw.toNat < USize.size) (k : Nat) (hk : k < 8) :
    (pick8 (0 * Lw + 16 * c) (8 * Lw + 16 * c) (4 * Lw + 16 * c) (12 * Lw + 16 * c)
        (2 * Lw + 16 * c)
      (10 * Lw + 16 * c) (6 * Lw + 16 * c) (14 * Lw + 16 * c) k).toNat =
      NTT.Transform.bitRevNat 4 k * Lw.toNat + 16 * c.toNat := by
  interval_cases k <;> simp only [pick8] <;>
    rw [laneIndex _ _ _ (by simp only [USize.reduceToNat]; omega) hc hL] <;>
    simp only [USize.reduceToNat] <;> rfl

/-- Lane `k` of half `1` reads block `bitrev₄ (8 + k)`. -/
theorem pick8_lanes1 (Lw c : USize) (hc : 16 * c.toNat + 16 ≤ Lw.toNat)
    (hL : 16 * Lw.toNat < USize.size) (k : Nat) (hk : k < 8) :
    (pick8 (1 * Lw + 16 * c) (9 * Lw + 16 * c) (5 * Lw + 16 * c) (13 * Lw + 16 * c)
        (3 * Lw + 16 * c)
      (11 * Lw + 16 * c) (7 * Lw + 16 * c) (15 * Lw + 16 * c) k).toNat =
      NTT.Transform.bitRevNat 4 (8 + k) * Lw.toNat + 16 * c.toNat := by
  interval_cases k <;> simp only [pick8] <;>
    rw [laneIndex _ _ _ (by simp only [USize.reduceToNat]; omega) hc hL] <;>
    simp only [USize.reduceToNat] <;> rfl

/-- Coordinate `t` of the four final DIF layers of the block at `i`. -/
def lastVal (t3 t2 t1 U : Array KoalaBear.Fast.Field) (i t : Nat) : KoalaBear.Fast.Field :=
  (Expressions.leaf16Stages t3 t2 t1 U i).getD (i + t) 0

/-- The natural-order word `w` of a fused leaf: line `w / 16` reverses to block column
`r / 16` and coordinate `r % 16`, and position `w % 16` reverses to block `bitrev₄ (w % 16)`. -/
def lastTarget (t3 t2 t1 U : Array KoalaBear.Fast.Field) (mm : Nat) (f : KoalaBear.Fast.Field)
    (sc : Bool) (w : Nat) : UInt32 :=
  let r := NTT.Transform.bitRevNat mm (w / 16)
  Native.scaleWord f.val sc (lastVal t3 t2 t1 U
    (NTT.Transform.bitRevNat 4 (w % 16) * 2 ^ mm + 16 * (r / 16)) (r % 16)).val

/-- The batch loop: after batches `c, …, c + n - 1`, exactly the words whose lines reverse into
them hold their final values. -/
theorem lastRevGo_encodeWords (t3 t2 t1 U : Array KoalaBear.Fast.Field) (mm : Nat) (Lw : USize)
    (f : KoalaBear.Fast.Field) (sc : Bool) (hb) (hL : Lw.toNat = 2 ^ mm) (hm : 0 < mm)
    (hm32 : mm ≤ 32) (hu : 64 * 2 ^ mm < USize.size) (hU : U.size = 16 * 2 ^ mm)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    ∀ (n : Nat) (c : USize) (O : Array UInt32), O.size = 16 * 2 ^ mm →
      16 * (c.toNat + n) ≤ 2 ^ mm →
      ∃ O', Native.lastRevGo (encode t3) (encode t2) (encode t1) (encode U) Lw
          (32 - mm).toUInt32 f.val sc hb n c (encode O) = encode O' ∧
        O'.size = O.size ∧ ∀ w, O'.getD w 0 =
          if w < 16 * 2 ^ mm ∧ c.toNat ≤ NTT.Transform.bitRevNat mm (w / 16) / 16 ∧
              NTT.Transform.bitRevNat mm (w / 16) / 16 < c.toNat + n then
            lastTarget t3 t2 t1 U mm f sc w
          else O.getD w 0 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  intro n
  induction n with
  | zero =>
    intro c O _ _
    refine ⟨O, rfl, rfl, fun w ↦ ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  | succ n ih =>
    intro c O hO hcn
    have hc : 16 * c.toNat + 16 ≤ Lw.toNat := by rw [hL]; omega
    have hc' : 16 * c.toNat + 16 ≤ 2 ^ mm := by omega
    have hLu : 16 * Lw.toNat < USize.size := by rw [hL]; omega
    have hs : (encode O).size < USize.size := by rw [size_encode_uint32, hO]; omega
    rw [Native.lastRevGo, dite_eq_left_of_eq_true (eq_true hc)]
    dsimp only
    rw [lastHalf_encodeWords t3 t2 t1 U _ _ _ _ _ _ _ _ c 0 mm f sc O hm hm32
      (by simp only [USize.reduceToNat]; omega) hc' hu hs]
    rw [lastHalf_encodeWords t3 t2 t1 U _ _ _ _ _ _ _ _ c 1 mm f sc _ hm hm32
      (by simp only [USize.reduceToNat]; omega) hc' hu
      (by rw [size_encode_uint32, size_lineStores, hO]; omega)]
    have hc1 : (c + 1).toNat = c.toNat + 1 := Plan.usize_add_one c (by omega)
    let V0 := fun t k ↦ Native.scaleWord f.val sc ((laneLine t3 t2 t1
      (pick8 (0 * Lw + 16 * c) (8 * Lw + 16 * c) (4 * Lw + 16 * c) (12 * Lw + 16 * c)
          (2 * Lw + 16 * c) (10 * Lw + 16 * c) (6 * Lw + 16 * c) (14 * Lw + 16 * c) k) U).get t).val
    let V1 := fun t k ↦ Native.scaleWord f.val sc ((laneLine t3 t2 t1
      (pick8 (1 * Lw + 16 * c) (9 * Lw + 16 * c) (5 * Lw + 16 * c) (13 * Lw + 16 * c)
          (3 * Lw + 16 * c) (11 * Lw + 16 * c) (7 * Lw + 16 * c) (15 * Lw + 16 * c) k) U).get t).val
    obtain ⟨O', hO'1, hO'2, hO'3⟩ := ih (c + 1)
      (lineStores (lineStores O mm c.toNat (USize.toNat 0) V0) mm c.toNat (USize.toNat 1) V1)
      (by rw [size_lineStores, size_lineStores, hO]) (by rw [hc1]; omega)
    refine ⟨O', hO'1, by rw [hO'2, size_lineStores, size_lineStores], fun w ↦ ?_⟩
    rw [hO'3 w, hc1]
    simp only [USize.reduceToNat]
    rw [getD_lineStores _ _ _ _ _ (by rw [size_lineStores, hO]) hc' (by decide),
      getD_lineStores _ _ _ _ _ hO hc' (by decide)]
    have hlane (h : Nat) (i : USize) (hi : i.toNat = NTT.Transform.bitRevNat 4 (8 * h + w % 8) *
        2 ^ mm + 16 * c.toNat) (hh : h < 2) (hwh : w % 16 / 8 = h)
        (hr : NTT.Transform.bitRevNat mm (w / 16) / 16 = c.toNat) :
        Native.scaleWord f.val sc ((laneLine t3 t2 t1 i U).get
          (NTT.Transform.bitRevNat mm (w / 16) % 16)).val = lastTarget t3 t2 t1 U mm f sc w := by
      have hb4 := NTT.Transform.bitRevNat_lt 4 (8 * h + w % 8)
      have hb4' : NTT.Transform.bitRevNat 4 (8 * h + w % 8) * 2 ^ mm ≤ 15 * 2 ^ mm :=
        Nat.mul_le_mul_right _ (by omega)
      rw [laneLine_get t3 t2 t1 i U (by rw [hi, hU]; omega) h3 h2 h1 _ (Nat.mod_lt _ (by decide))]
      unfold lastTarget lastVal
      dsimp only
      rw [hi, show 8 * h + w % 8 = w % 16 by omega, hr]
    set r := NTT.Transform.bitRevNat mm (w / 16) with hr0
    by_cases hA : w < 16 * 2 ^ mm ∧ c.toNat + 1 ≤ r / 16 ∧ r / 16 < c.toNat + 1 + n
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_left_of_eq_true _ _
        (eq_true (show w < 16 * 2 ^ mm ∧ c.toNat ≤ r / 16 ∧ r / 16 < c.toNat + (n + 1) by
          omega))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hA)]
    by_cases hB : w < 16 * 2 ^ mm ∧ r / 16 = c.toNat ∧ w % 16 / 8 = 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hB), ite_eq_left_of_eq_true _ _
        (eq_true (show w < 16 * 2 ^ mm ∧ c.toNat ≤ r / 16 ∧ r / 16 < c.toNat + (n + 1) by
          omega))]
      exact hlane 1 _ (by rw [pick8_lanes1 Lw c hc hLu _ (Nat.mod_lt _ (by decide)), hL])
        (by decide) hB.2.2 hB.2.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hB)]
    by_cases hC : w < 16 * 2 ^ mm ∧ r / 16 = c.toNat ∧ w % 16 / 8 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hC), ite_eq_left_of_eq_true _ _
        (eq_true (show w < 16 * 2 ^ mm ∧ c.toNat ≤ r / 16 ∧ r / 16 < c.toNat + (n + 1) by
          omega))]
      exact hlane 0 _ (by rw [pick8_lanes0 Lw c hc hLu _ (Nat.mod_lt _ (by decide)), hL,
          Nat.mul_zero, Nat.zero_add])
        (by decide) hC.2.2 hC.2.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hC), ite_eq_right_of_eq_false _ _
      (eq_false (show ¬(w < 16 * 2 ^ mm ∧ c.toNat ≤ r / 16 ∧ r / 16 < c.toNat + (n + 1)) by
        omega))]

/-- The fused final layers of a leaf, in natural order. -/
theorem lastRev_encodeWords (t3 t2 t1 U : Array KoalaBear.Fast.Field) (m : Nat) (f :
    KoalaBear.Fast.Field)
    (sc : Bool) (hm : 8 ≤ m) (hm36 : m ≤ 36) (hu : 4 * 2 ^ m < USize.size) (hU : U.size = 2 ^ m)
    (ht3 : t3.size = 8) (ht2 : t2.size = 4) (ht1 : t1.size = 2)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.lastRev (encode t3) (encode t2) (encode t1) (encode U) m f.val sc =
      encode (Array.ofFn (n := 2 ^ m) fun w ↦ lastTarget t3 t2 t1 U (m - 4) f sc w) := by
  have hp : 2 ^ m = 16 * 2 ^ (m - 4) := by
    rw [show m = m - 4 + 4 by omega, Nat.pow_add]; simp only [Nat.add_sub_cancel]; omega
  have hpos := Nat.two_pow_pos (m - 4)
  have h16 : 16 ∣ 2 ^ (m - 4) := by
    rw [show m - 4 = 4 + (m - 4 - 4) by omega, Nat.pow_add]; exact Nat.dvd_mul_right _ _
  have hg : 2 ^ (m - 4) < USize.size ∧ 64 * 2 ^ (m - 4) ≤ (encode U).size ∧
      (encode U).size < USize.size ∧ 31 < (encode t3).size ∧
      (encode t3).size < USize.size ∧ 15 < (encode t2).size ∧
      (encode t2).size < USize.size ∧ 7 < (encode t1).size ∧
      (encode t1).size < USize.size := by
    simp only [size_encode_fields, hU, ht3, ht2, ht1]; omega
  unfold Native.lastRev
  rw [dite_eq_left_of_eq_true (eq_true hg)]
  obtain ⟨O', hO'1, hO'2, hO'3⟩ := lastRevGo_encodeWords t3 t2 t1 U (m - 4)
    (USize.ofNatLT (2 ^ (m - 4)) hg.1) f sc _ (by simp only [USize.toNat_ofNatLT]) (by omega)
    (by omega) (by omega) (by omega) h3 h2 h1 (2 ^ (m - 4) / 16) 0 (U.map Subtype.val)
    (by rw [Array.size_map, hU, hp]) (by simp only [USize.toNat_zero, Nat.zero_add]; omega)
  conv_lhs => arg 12; rw [encode_eq_map_val]
  rw [hO'1]
  congr 1
  apply array_eq_of_getD _ _ 0 (by rw [hO'2, Array.size_map, Array.size_ofFn, hU])
  intro w
  rw [hO'3 w]
  by_cases hw : w < 16 * 2 ^ (m - 4)
  · have hr := NTT.Transform.bitRevNat_lt (m - 4) (w / 16)
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hw, by simp only [USize.toNat_zero]; omega,
      by simp only [USize.toNat_zero, Nat.zero_add]; omega⟩),
      getD_ofFn_bounded _ _ (by omega)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hw h.1))]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_none (show U.size ≤ w by omega), Option.map_none, Option.getD_none,
      Array.getElem?_eq_none (show (Array.ofFn (n := 2 ^ m) fun w ↦
        lastTarget t3 t2 t1 U (m - 4) f sc w).size ≤ w by rw [Array.size_ofFn]; omega)]

/-- The four final layers of a block leave the rest of the array unchanged. -/
theorem getD_leaf16Stages_outside (t3 t2 t1 a : Array KoalaBear.Fast.Field) (base : Nat)
    (hs : base + 16 ≤ a.size) (k : Nat) (hk : ¬(base ≤ k ∧ k < base + 16)) :
    (Expressions.leaf16Stages t3 t2 t1 a base).getD k 0 = a.getD k 0 := by
  have s8 : base + 16 ≤ (layer16_8 t3 a base).size := by rw [size_layer16_8]; exact hs
  have s4 : base + 16 ≤ (layer16_4 t2 (layer16_8 t3 a base) base).size := by
    rw [size_layer16_4]; exact s8
  have s2 : base + 16 ≤ (layer16_2 t1 (layer16_4 t2 (layer16_8 t3 a base) base) base).size := by
    rw [size_layer16_2]; exact s4
  unfold Expressions.leaf16Stages
  rw [getD_layer16_1_outside _ _ _ s2 _ hk, getD_layer16_2_outside _ _ _ s4 _ hk,
    getD_layer16_4_outside _ _ _ s8 _ hk, getD_layer16_8_outside _ _ _ hs _ hk]

/-- Inside its block, the four final layers depend only on the block's coordinates. -/
theorem lastVal_congr (t3 t2 t1 a a' : Array KoalaBear.Fast.Field) (base : Nat)
    (hs : base + 16 ≤ a.size) (hs' : base + 16 ≤ a'.size) (hu : a.size < USize.size)
    (hagree : ∀ o < 16, a.getD (base + o) 0 = a'.getD (base + o) 0)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) (t : Nat)
    (ht : t < 16) : lastVal t3 t2 t1 a base t = lastVal t3 t2 t1 a' base t := by
  have hb : (USize.ofNatLT base (by omega)).toNat = base := USize.toNat_ofNatLT ..
  unfold lastVal
  rw [← hb, ← laneLine_get t3 t2 t1 _ a (by rw [hb]; omega) h3 h2 h1 t ht,
    ← laneLine_get t3 t2 t1 _ a' (by rw [hb]; omega) h3 h2 h1 t ht]
  have he : laneLine t3 t2 t1 (USize.ofNatLT base (by omega)) a =
      laneLine t3 t2 t1 (USize.ofNatLT base (by omega)) a' := by
    have hagree' : ∀ o : USize, o.toNat < 16 →
        a.getD ((USize.ofNatLT base (by omega)).toNat + o.toNat) 0 =
          a'.getD ((USize.ofNatLT base (by omega)).toNat + o.toNat) 0 := by
      intro o ho; rw [hb]; exact hagree _ ho
    unfold laneLine readField
    simp (disch := (simp only [USize.reduceToNat]; omega)) only [hagree']
  rw [he]

/-- The fold of final-layer blocks, block by block. -/
theorem getD_fold_leafBlocks (t3 t2 t1 U : Array KoalaBear.Fast.Field) (f : KoalaBear.Fast.Field)
    (B : Nat) (hs : U.size = 16 * B) (hu : U.size < USize.size)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    ∀ K ≤ B, ((List.range K).foldl (fun b block ↦ leafBlock t3 t2 t1 (block * 16) f false b)
      U).size = U.size ∧ ∀ k < B, ∀ t < 16,
      ((List.range K).foldl (fun b block ↦ leafBlock t3 t2 t1 (block * 16) f false b)
        U).getD (16 * k + t) 0 =
        if k < K then lastVal t3 t2 t1 U (16 * k) t else U.getD (16 * k + t) 0 := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨rfl, fun k _ t _ ↦ ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.not_lt_zero k))]
    rfl
  | succ K ih =>
    intro hK
    obtain ⟨hsz, hv⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hleaf : ∀ A : Array KoalaBear.Fast.Field, leafBlock t3 t2 t1 (K * 16) f false A =
        Expressions.leaf16Stages t3 t2 t1 A (K * 16) := fun A ↦ by
      simp only [leafBlock, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by rw [hleaf, size_leaf16Stages, hsz], fun k hk t ht ↦ ?_⟩
    rw [hleaf]
    by_cases hkK : k = K
    · subst k
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.lt_succ_self K))]
      rw [show 16 * K + t = K * 16 + t by omega]
      change lastVal t3 t2 t1 _ (K * 16) t = _
      rw [Nat.mul_comm 16 K]
      apply lastVal_congr _ _ _ _ _ _ (by rw [hsz]; omega) (by omega) (by rw [hsz]; exact hu)
        _ h3 h2 h1 t ht
      intro o ho
      have := hv K (by omega) o ho
      rw [Nat.mul_comm 16 K, ite_eq_right_of_eq_false _ _ (eq_false (Nat.lt_irrefl K))] at this
      exact this
    · rw [getD_leaf16Stages_outside _ _ _ _ _ (by rw [hsz]; omega) _ (by omega), hv k hk t ht]
      by_cases hk2 : k < K
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hk2),
          ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hk2),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- The radix-four passes before the fused final layers, as folds. -/
theorem Native.upperStages_eq_folds (logN : Nat) (tw : Array ByteArray) (a : ByteArray) :
    Native.upperStages logN tw a =
      (List.range (logN / 2 - 2)).foldl (fun b pass ↦ rawPass logN tw pass b) a := by
  simp only [Native.upperStages, rawPass, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range', List.forIn_pure_yield_eq_foldl, bind_pure, pure_bind, Id.run_pure]

/-- The fused leaf is the reversed, optionally scaled leaf of the sequential stages. -/
theorem Native.leafNatural_encode (m : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (X : Array KoalaBear.Fast.Field) (f : KoalaBear.Fast.Field) (sc : Bool)
    (htw : TwiddleSizes m tw) (hone : TwiddleOnes m tw) (hs : X.size = 2 ^ m)
    (hu : 4 * 2 ^ m < USize.size) (hm32 : m ≤ 32) :
    Native.leafNatural (tw.map encode) m f.val sc (encode X) =
      Native.leafRev (Native.stages m (tw.map encode) (encode X) f.val false) m f.val
        sc := by
  unfold Native.leafNatural
  split
  · rename_i hm
    let U := (List.range (m / 2 - 2)).foldl (fun b pass ↦ fieldPass m tw pass b) X
    have hU : Native.upperStages m (tw.map encode) (encode X) = encode U := by
      rw [Native.upperStages_eq_folds]
      exact Native.passes_encode m (m / 2 - 2) tw X (by omega) htw hs hu
    have hUs : U.size = 2 ^ m :=
      foldl_invariant (List.range (m / 2 - 2)) (fun b ↦ b.size = 2 ^ m)
        (fun b pass ↦ fieldPass m tw pass b)
        (fun pass _ b hb ↦ by simpa only [size_fieldPass] using hb) X hs
    have h3 : (tw.getD 3 #[]).size = 8 := by simpa using htw 3 (by omega)
    have h2 : (tw.getD 2 #[]).size = 4 := by simpa using htw 2 (by omega)
    have h1 : (tw.getD 1 #[]).size = 2 := by simpa using htw 1 (by omega)
    rw [hU, getD_map_encode, getD_map_encode, getD_map_encode,
      lastRev_encodeWords _ _ _ U m f sc hm.2 (by omega) hu hUs h3 h2 h1 (hone 3 (by omega))
        (hone 2 (by omega)) (hone 1 (by omega)),
      Native.stages_encode m tw X f false htw hone hs hu]
    let W := (List.range (2 ^ m / 16)).foldl (fun b block ↦
      leafBlock (tw.getD 3 #[]) (tw.getD 2 #[]) (tw.getD 1 #[]) (block * 16) f false b) U
    have hfs : fieldStages m tw X f false = W := by
      have hf : (decide (m ≥ 4) && m % 2 == 0) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
      have ho : ¬(m % 2 = 1) := by omega
      simp only [fieldStages, hf, ↓reduceIte, ho]
      rfl
    have hp : 2 ^ m = 16 * (2 ^ m / 16) := by
      have : 16 ∣ 2 ^ m := by
        rw [show m = 4 + (m - 4) by omega, Nat.pow_add]; exact Nat.dvd_mul_right _ _
      omega
    have hfold := getD_fold_leafBlocks (tw.getD 3 #[]) (tw.getD 2 #[]) (tw.getD 1 #[]) U f
      (2 ^ m / 16) (by rw [hUs]; exact hp) (by omega) (hone 3 (by omega)) (hone 2 (by omega))
      (hone 1 (by omega)) (2 ^ m / 16) le_rfl
    have hWs : W.size = 2 ^ m := by rw [hfold.1, hUs]
    rw [hfs]
    simp only [encode_eq_map_val] at *
    rw [Native.leafRev_encodeWords (W.map Subtype.val) m f.val sc (by omega) hm32
      (by rw [Array.size_map, hWs]) (by rw [size_encode_uint32, Array.size_map, hWs]; exact hu)]
    congr 1
    apply array_eq_of_getD _ _ 0 (by rw [Array.size_ofFn, size_rows]; omega)
    intro w
    by_cases hw : w < 2 ^ m
    · rw [getD_ofFn_bounded _ _ hw, getD_rows _ _ _ (by omega),
        show 16 * (w / 16) + w % 16 = w by omega, getD_map_val]
      unfold lastTarget
      dsimp only
      have h4 : m - 4 + 4 = m := by omega
      have hwm : w % 16 < 2 ^ 4 := Nat.mod_lt _ (by decide)
      have hcat := bitRevNat_concat (m - 4) 4 (w / 16) (w % 16) hwm
      rw [h4, show 2 ^ 4 * (w / 16) + w % 16 = w by omega] at hcat
      rw [hcat]
      generalize hv : NTT.Transform.bitRevNat 4 (w % 16) = v
      generalize hr : NTT.Transform.bitRevNat (m - 4) (w / 16) = r
      have hvl : v < 16 := by rw [← hv]; exact NTT.Transform.bitRevNat_lt 4 _
      have hrl : r < 2 ^ (m - 4) := by rw [← hr]; exact NTT.Transform.bitRevNat_lt _ _
      have hL : 2 ^ (m - 4) = 16 * (2 ^ (m - 4) / 16) := by
        have : 16 ∣ 2 ^ (m - 4) := by
          rw [show m - 4 = 4 + (m - 4 - 4) by omega, Nat.pow_add]; exact Nat.dvd_mul_right _ _
        omega
      have hB : 2 ^ m / 16 = 2 ^ (m - 4) := by
        rw [show m = m - 4 + 4 by omega, Nat.pow_add]; simp only [Nat.add_sub_cancel]; omega
      generalize hq : 2 ^ (m - 4) / 16 = q at hL
      have hk : v * q + r / 16 < 2 ^ m / 16 := by
        have : v * q + q ≤ 16 * q := by
          have := Nat.mul_le_mul_right q (show v + 1 ≤ 16 by omega)
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        omega
      have e1 : 2 ^ (m - 4) * v + r = 16 * (v * q + r / 16) + r % 16 := by
        rw [hL]; have := Nat.div_add_mod r 16; nlinarith
      have e2 : v * 2 ^ (m - 4) + 16 * (r / 16) = 16 * (v * q + r / 16) := by
        rw [hL]; ring
      rw [e1, e2, hfold.2 _ hk _ (Nat.mod_lt _ (by decide)),
        ite_eq_left_of_eq_true _ _ (eq_true hk)]
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega),
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [size_rows]; omega)]
  · rfl

/-- The leaves of the sliced packed tree are the post-processed DIF leaf blocks. -/
theorem Native.sliceChunks_leaves (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (normalize : Bool) (P depth : Nat)
    (post : ByteArray → ByteArray) (leaf : Nat → ByteArray → ByteArray) (ht : TwiddlesFor D tw)
    (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hleaf : ∀ X : Array KoalaBear.Fast.Field, X.size = 2 ^ (D.logN - depth) →
      leaf (D.logN - depth) (encode X) = post (Native.stages (D.logN - depth)
        (tw.map encode) (encode X) factor.val normalize)) :
    (Native.sliceChunks (tw.map encode) D.logN #[encode a] factor.val normalize P post
      leaf depth).get =
      (Native.splitChunks (tw.map encode) D.logN (encode a) factor.val normalize
        depth).get.map post := by
  rw [← Native.slicesOf_one a D.n hs,
    Native.sliceChunks_eq tw _ _ _ _ _ _ D.logN 1 D.n _ (Nat.one_mul _) (by decide)
      (TwiddlesFor.invariants D tw ht).1 hu hleaf,
    Native.ofFn_getD a (2 ^ D.logN) hs]

/-- The natural-order leaf function agrees with reversing the sequential stages. -/
theorem Native.leafNatural_hyp (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (factor : KoalaBear.Fast.Field) (inverse : Bool)
    (ht : TwiddlesFor D tw) (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size)
    (X : Array KoalaBear.Fast.Field) (hX : X.size = 2 ^ (D.logN - 4)) :
    Native.leafNatural (tw.map encode) (D.logN - 4) factor.val inverse (encode X) =
      Native.leafRev (Native.stages (D.logN - 4) (tw.map encode) (encode X) factor.val
        false) (D.logN - 4) factor.val inverse := by
  obtain ⟨hsz, hone⟩ := TwiddlesFor.invariants D tw ht
  have hp : 2 ^ (D.logN - 4) ≤ 2 ^ D.logN := Nat.pow_le_pow_right (by omega) (by omega)
  exact Native.leafNatural_encode (D.logN - 4) tw X factor inverse
    (fun s hs ↦ hsz s (by omega)) (fun s hs ↦ hone s (by omega)) hX
    (by simp only [NTT.Domain.n] at hu; omega) (by omega)

/-- The decoding pipeline computes the DFT with optional inverse normalization. -/
theorem Native.runDecoded_dft (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (depth : Nat) (factor : KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (inverse : Bool) (ht : TwiddlesFor D tw) (hs : a.size = D.n)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    Native.runDecoded (tw.map encode) D.logN depth factor.val (encode a) inverse =
      if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
      else NTT.Forward.forwardSpec D a := by
  unfold Native.runDecoded
  let normalize := inverse && D.logN - depth ≥ 4 && (D.logN - depth) % 2 == 0
  have hn : ValidLeafNormalization D.logN depth normalize := by
    intro h
    simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.2, h.2⟩
  have hi : normalize = true → inverse = true := by
    intro h
    simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.1.1
  have hsize : (normalizedDifSpec D a factor normalize).size = 2 ^ D.logN :=
    size_normalizedDifSpec D a factor normalize
  have hpu : (encode (normalizedDifSpec D a factor normalize)).size < USize.size := by
    rw [size_encode_fields, hsize]
    exact hu
  change Native.decodeTiled D.logN (Native.assembleChunks (4 * 2 ^ D.logN)
    (Native.sliceChunks (tw.map encode) D.logN #[encode a] factor.val normalize
      (Native.sliceCount D.logN depth) id
      (fun m b ↦ Native.stages m (tw.map encode) b factor.val normalize) depth).get)
      factor.val (inverse && !normalize) = _
  rw [Native.sliceChunks_leaves D tw a factor normalize _ depth _ _ ht hs hu (fun _ _ ↦ rfl),
    Array.map_id, Native.assembleChunks_capacity, Native.splitChunks_eq,
    Native.splitTask_correct D tw a factor normalize depth ht hs hu hn,
    Native.decodeTiled_encode _ _ factor _ h32 hsize hpu,
    decodedFields_normalizedDifSpec D a factor normalize inverse hi]

/-- The packed in/out pipeline computes the DFT with optional inverse normalization. -/
theorem Native.runPacked_dft (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (depth : Nat) (factor : KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (inverse : Bool) (ht : TwiddlesFor D tw) (hs : a.size = D.n)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    Native.runPacked (tw.map encode) D.logN depth factor.val (encode a) inverse =
      encode (if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
        else NTT.Forward.forwardSpec D a) := by
  unfold Native.runPacked
  split
  · rename_i hshape
    simp only [Native.naturalShape, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hshape
    obtain ⟨⟨rfl, h12⟩, _⟩ := hshape
    have hn : ValidLeafNormalization D.logN 4 false := by intro h; cases h
    have hsize : (normalizedDifSpec D a factor false).size = 2 ^ D.logN :=
      size_normalizedDifSpec D a factor false
    rw [Native.sliceChunks_leaves D tw a factor false _ 4 _ _ ht hs hu
      (Native.leafNatural_hyp D tw factor inverse ht h32 hu),
      Native.splitChunks_leaves D tw a factor false 4 ht hs hu hn (by omega)]
    rw [show (Array.ofFn (n := 2 ^ 4) fun l ↦ encode ((normalizedDifSpec D a factor
        false).extract (l * 2 ^ (D.logN - 4)) ((l + 1) * 2 ^ (D.logN - 4)))) =
        Native.leafBlocks (normalizedDifSpec D a factor false) D.logN from rfl,
      Native.naturalLeaves_encode _ _ factor _ h12 h32 hsize hu,
      show inverse = (inverse && !false) by simp only [Bool.not_false, Bool.and_true],
      decodedFields_normalizedDifSpec D a factor false _ (fun h ↦ by cases h)]
    simp only [Bool.not_false, Bool.and_true]
  · rw [Native.runDecoded_dft D tw depth factor a inverse ht hs h32 hu, Native.encodeFields_eq]

end CompPoly.CPolynomial.NTTFast.Packed
