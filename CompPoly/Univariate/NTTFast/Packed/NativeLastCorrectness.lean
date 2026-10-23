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
public import CompPoly.Univariate.NTTFast.Packed.Twiddles
public import CompPoly.Univariate.NTTFast.Packed.LocalLayers
public import CompPoly.Univariate.NTTFast.Packed.PassRefinement
public import CompPoly.Univariate.NTTFast.Packed.Radix2Refinement
public import CompPoly.Univariate.NTTFast.Packed.NativeOrderCorrectness
import all CompPoly.Univariate.NTTFast.Packed.NativeOrder
import all CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.Unrolled

/-! # Correctness of the fused final leaf layers

`laneLine` is the field-level expression graph of one lane of `lastHalf`: the four final DIF
layers of one sixteen-word block, exactly as in `leaf16Field`. A kernel call writes, for each
`t < 16`, eight words of line `bitrev (16 c + t)` (`writeLines`); the batch loop covers every
line once, so `lastRev` is the bit-reversed, optionally scaled result of the final layers.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode size_encode_uint32)

/-- Sixteen field coordinates. -/
structure FieldLine (p : ℕ) [Mont32Field p] where
  w0 : FastField p
  w1 : FastField p
  w2 : FastField p
  w3 : FastField p
  w4 : FastField p
  w5 : FastField p
  w6 : FastField p
  w7 : FastField p
  w8 : FastField p
  w9 : FastField p
  w10 : FastField p
  w11 : FastField p
  w12 : FastField p
  w13 : FastField p
  w14 : FastField p
  w15 : FastField p

/-- Coordinate `t` of a line. -/
def FieldLine.get (y : FieldLine p) : Nat → FastField p
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
def laneLine (t3 t2 t1 : Array (FastField p)) (i : USize)
    (b : Array (FastField p)) : FieldLine p :=
  leaf16_line%

/-- The fused leaf kernel is the lane graph followed by one splice. -/
theorem leaf16Field_eq_laneLine (t3 t2 t1 : Array (FastField p)) (i : USize)
    (b : Array (FastField p)) :
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
theorem getD_lit_line (y : FieldLine p) (k : Nat) (hk : k < 16) :
    (#[y.w0, y.w1, y.w2, y.w3, y.w4, y.w5, y.w6, y.w7, y.w8, y.w9, y.w10, y.w11, y.w12, y.w13,
      y.w14, y.w15] : Array (FastField p)).getD k 0 = y.get k := by
  interval_cases k <;> rfl

/-- Coordinate `t` of a lane is the fused kernel's coordinate `i + t`. -/
theorem getD_leaf16Field_laneLine (t3 t2 t1 : Array (FastField p)) (i : USize)
    (b : Array (FastField p)) (hi : i.toNat + 16 ≤ b.size) (t : Nat) (ht : t < 16) :
    (leaf16Field t3 t2 t1 i b).getD (i.toNat + t) 0 = (laneLine t3 t2 t1 i b).get t := by
  have hsz : ∀ v : Array (FastField p), v.size = 16 → i.toNat + v.size ≤ b.size := by
    intro v hv; omega
  rw [leaf16Field_eq_laneLine, getD_splice _ _ _ (hsz _ rfl)]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬(i.toNat + t < i.toNat) by omega))]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.reduceAdd,
    show i.toNat + t < i.toNat + 16 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  exact getD_lit_line _ t ht

/-- Coordinate `t` of a lane is coordinate `i + t` of the four final DIF layers at `i`. -/
theorem laneLine_get (t3 t2 t1 : Array (FastField p)) (i : USize)
    (b : Array (FastField p)) (hi : i.toNat + 16 ≤ b.size)
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

/-- An output of `2 ^ mm` lines passes the output check of `lastHalf`. -/
theorem lastHalf_check_of (out : ByteArray) (mm : Nat) (half : USize) (hm : 0 < mm)
    (hm32 : mm < 32) (hh : half.toNat < 2) (hO : 64 * 2 ^ mm ≤ out.size)
    (hs : out.size < USize.size) :
    0 < (32 - mm).toUInt32 ∧ (32 - mm).toUInt32 < 32 ∧ half < 2 ∧
      (1 : USize) <<< (32 - (32 - mm).toUInt32).toUSize ≤ out.usize / 64 := by
  have hk : (32 - mm).toUInt32.toNat = 32 - mm := by
    rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hk' : (32 - (32 - mm).toUInt32).toUSize.toNat = mm := by
    rw [UInt32.toNat_toUSize, UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le, hk]; change 32 - mm ≤ 32; omega), hk]
    change 32 - (32 - mm) = mm
    omega
  have hu : out.usize.toNat = out.size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' hs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UInt32.lt_iff_toNat_lt, hk]; change 0 < 32 - mm; omega
  · rw [UInt32.lt_iff_toNat_lt, hk]; change 32 - mm < 32; omega
  · rw [USize.lt_iff_toNat_lt, Native.usize_numeral 2 (by decide)]; exact hh
  · rw [USize.le_iff_toNat_le, Native.one_shiftLeft_toNat _ (by rw [hk']; exact hm32), hk',
      USize.toNat_div, Native.usize_numeral 64 (by decide), hu]
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- One kernel call stores the final layers of its eight lanes into sixteen half lines. -/
theorem lastHalf_encodeWords (t3 t2 t1 U : Array (FastField p)) (i0 i1 i2 i3 i4 i5 i6 i7 c
    half :
    USize) (mm : Nat) (f : FastField p) (sc : Bool) (O : Array UInt32)
    (hm : 0 < mm) (hm32 : mm < 32) (hh : half.toNat < 2) (hc : 16 * c.toNat + 16 ≤ 2 ^ mm)
    (hu : 64 * 2 ^ mm < USize.size) (hO : O.size = 16 * 2 ^ mm)
    (hs : (encode O).size < USize.size) (h) :
    Native.lastHalf p (encode t3) (encode t2) (encode t1) (encode U)
      i0 i1 i2 i3 i4 i5 i6 i7 c (32 - mm).toUInt32 half f.val sc (encode O) h =
      encode (lineStores O mm c.toNat half.toNat fun t k ↦
        Native.scaleWord p f.val sc
          ((laneLine t3 t2 t1 (pick8 i0 i1 i2 i3 i4 i5 i6 i7 k) U).get t).val) := by
  have hm32 : mm ≤ 32 := by omega
  unfold Native.lastHalf
  rw [dite_eq_left_of_eq_true (eq_true (lastHalf_check_of _ mm half hm (by omega) hh
    (by rw [size_encode_uint32, hO]; omega) hs))]
  simp only [Native.store8_val _ _ _ _ _ _ _ _ _ _ _ hs, Native.touchLast, Native.touch_eq]
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
def lastVal (t3 t2 t1 U : Array (FastField p)) (i t : Nat) : FastField p :=
  (Expressions.leaf16Stages t3 t2 t1 U i).getD (i + t) 0

/-- The natural-order word `w` of a fused leaf: line `w / 16` reverses to block column
`r / 16` and coordinate `r % 16`, and position `w % 16` reverses to block `bitrev₄ (w % 16)`. -/
def lastTarget (t3 t2 t1 U : Array (FastField p)) (mm : Nat) (f : FastField p)
    (sc : Bool) (w : Nat) : UInt32 :=
  let r := NTT.Transform.bitRevNat mm (w / 16)
  Native.scaleWord p f.val sc (lastVal t3 t2 t1 U
    (NTT.Transform.bitRevNat 4 (w % 16) * 2 ^ mm + 16 * (r / 16)) (r % 16)).val

/-- The batch loop: after batches `c, …, c + n - 1`, exactly the words whose lines reverse into
them hold their final values. -/
theorem lastRevGo_encodeWords (t3 t2 t1 U : Array (FastField p)) (mm : Nat) (Lw : USize)
    (f : FastField p) (sc : Bool) (hb) (hL : Lw.toNat = 2 ^ mm) (hm : 0 < mm)
    (hm32 : mm < 32) (hu : 64 * 2 ^ mm < USize.size) (hU : U.size = 16 * 2 ^ mm)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    ∀ (n : Nat) (c : USize) (O : Array UInt32), O.size = 16 * 2 ^ mm →
      16 * (c.toNat + n) ≤ 2 ^ mm →
      ∃ O', Native.lastRevGo p (encode t3) (encode t2) (encode t1) (encode U) Lw
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
      (by simp only [USize.reduceToNat]; omega) hc' hu hO hs]
    rw [lastHalf_encodeWords t3 t2 t1 U _ _ _ _ _ _ _ _ c 1 mm f sc _ hm hm32
      (by simp only [USize.reduceToNat]; omega) hc' hu (by rw [size_lineStores, hO])
      (by rw [size_encode_uint32, size_lineStores, hO]; omega)]
    have hc1 : (c + 1).toNat = c.toNat + 1 := Plan.usize_add_one c (by omega)
    let V0 := fun t k ↦ Native.scaleWord p f.val sc ((laneLine t3 t2 t1
      (pick8 (0 * Lw + 16 * c) (8 * Lw + 16 * c) (4 * Lw + 16 * c) (12 * Lw + 16 * c)
          (2 * Lw + 16 * c) (10 * Lw + 16 * c) (6 * Lw + 16 * c) (14 * Lw + 16 * c) k) U).get t).val
    let V1 := fun t k ↦ Native.scaleWord p f.val sc ((laneLine t3 t2 t1
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
        Native.scaleWord p f.val sc ((laneLine t3 t2 t1 i U).get
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
theorem lastRev_encodeWords (t3 t2 t1 U : Array (FastField p)) (m : Nat) (f :
    FastField p)
    (sc : Bool) (hm : 8 ≤ m) (hm36 : m < 36) (hu : 4 * 2 ^ m < USize.size) (hU : U.size = 2 ^ m)
    (ht3 : t3.size = 8) (ht2 : t2.size = 4) (ht1 : t1.size = 2)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.lastRev p (encode t3) (encode t2) (encode t1) (encode U) m f.val sc =
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
  conv_lhs => arg 13; rw [encode_eq_map_val]
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
theorem getD_leaf16Stages_outside (t3 t2 t1 a : Array (FastField p)) (base : Nat)
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
theorem lastVal_congr (t3 t2 t1 a a' : Array (FastField p)) (base : Nat)
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
theorem getD_fold_leafBlocks (t3 t2 t1 U : Array (FastField p)) (B : Nat)
    (hs : U.size = 16 * B) (hu : U.size < USize.size)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    ∀ K ≤ B,
      ((List.range K).foldl (fun b block ↦ Expressions.leaf16Stages t3 t2 t1 b (block * 16))
        U).size = U.size ∧ ∀ k < B, ∀ t < 16,
      ((List.range K).foldl (fun b block ↦ Expressions.leaf16Stages t3 t2 t1 b (block * 16))
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
    refine ⟨by rw [Expressions.size_leaf16Stages, hsz], fun k hk t ht ↦ ?_⟩
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

/-- The fused final layers and reversal of a leaf are the natural-order read of its last two
radix-four passes, as sixteen-word blocks. -/
theorem Native.lastRev_encode (t3 t2 t1 U : Array (FastField p)) (m : Nat)
    (f : FastField p) (sc : Bool) (hm : 8 ≤ m) (hm32 : m ≤ 32)
    (hu : 4 * 2 ^ m < USize.size) (hUs : U.size = 2 ^ m)
    (h3 : t3.size = 8) (h2 : t2.size = 4) (h1 : t1.size = 2)
    (o3 : t3.getD 0 0 = 1) (o2 : t2.getD 0 0 = 1) (o1 : t1.getD 0 0 = 1) :
    Native.lastRev p (encode t3) (encode t2) (encode t1) (encode U) m f.val sc =
      encode (decodedFields m ((List.range (2 ^ m / 16)).foldl (fun b block ↦
        Expressions.leaf16Stages t3 t2 t1 b (block * 16)) U) f sc) := by
  rw [lastRev_encodeWords _ _ _ U m f sc hm (by omega) hu hUs h3 h2 h1 o3 o2 o1]
  let W := (List.range (2 ^ m / 16)).foldl (fun b block ↦
    Expressions.leaf16Stages t3 t2 t1 b (block * 16)) U
  have hp : 2 ^ m = 16 * (2 ^ m / 16) := by
    have : 16 ∣ 2 ^ m := by
      rw [show m = 4 + (m - 4) by omega, Nat.pow_add]; exact Nat.dvd_mul_right _ _
    omega
  have hfold := getD_fold_leafBlocks t3 t2 t1 U
    (2 ^ m / 16) (by rw [hUs]; exact hp) (by omega) o3 o2
    o1 (2 ^ m / 16) le_rfl
  have hWs : W.size = 2 ^ m := by rw [hfold.1, hUs]
  simp only [encode_eq_map_val] at *
  congr 1
  apply array_eq_of_getD _ _ 0 (by
    rw [Array.size_ofFn, Array.size_map, decodedFields, Array.size_ofFn])
  intro w
  by_cases hw : w < 2 ^ m
  · rw [getD_ofFn_bounded _ _ hw, getD_map_val, decodedFields, getD_ofFn_bounded _ _ hw]
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
    cases sc <;> simp only [scaleWord, Bool.false_eq_true, ↓reduceIte, mul_val]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_ofFn]; omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
        rw [Array.size_map, decodedFields, Array.size_ofFn]; omega)]

/-- The block loop packs the ordinary radix-four blocks. -/
theorem Native.radix4Blocks_encode (th tl : Array (FastField p)) (q blocks : Nat)
    (a : Array (FastField p))
    (ha : (encode a).size < USize.size)
    (hth : (encode th).size < USize.size) (htl : (encode tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size) (hbound : blocks * (4 * q) ≤ a.size) :
    Native.radix4Blocks p (encode th) (encode tl) q blocks (encode a) =
      encode (Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks 0 a) := by
  unfold Native.radix4Blocks
  split
  · rename_i h
    rw [Native.blocks16Loop_encode_pass th tl (q / 16) _ (by rw [USize.toNat_ofNatLT]; omega),
      USize.toNat_ofNatLT]
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
      List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
    exact Native.fold_inner16_encode th tl q blocks a ha hth htl hthi htli hbound

/-- The field-array semantics of `leafLayers`. -/
def fieldLayers (tw : Array (Array (FastField p))) (m count : Nat)
    (X : Array (FastField p)) : Array (FastField p) :=
  let X := if m % 2 = 1 then
    Plan.butterflyDIFInner (tw.getD (m - 1) #[]) (2 ^ (m - 1)) 0 0 (2 ^ (m - 1)) X else X
  (List.range count).foldl (fun b pass ↦
    let high := m - 1 - m % 2 - 2 * pass
    let q := 2 ^ (high - 1)
    Plan.butterflyDIFRadix4Blocks (tw.getD high #[]) (tw.getD (high - 1) #[]) (4 * q) q
      (2 ^ m / (4 * q)) 0 b) X

@[simp] theorem size_fieldLayers (tw : Array (Array (FastField p))) (m count : Nat)
    (X : Array (FastField p)) : (fieldLayers tw m count X).size = X.size := by
  unfold fieldLayers
  apply foldl_invariant _ (fun b : Array (FastField p) ↦ b.size = X.size)
  · intro _ _ b hb
    rw [Plan.size_butterflyDIFRadix4Blocks, hb]
  · split <;> simp only [Plan.size_butterflyDIFInner]

/-- The leading leaf layers on packed words agree with their field-array semantics. -/
theorem Native.leafLayers_encode (tw : Array (Array (FastField p))) (m count : Nat)
    (X : Array (FastField p)) (hc : count ≤ m / 2) (htw : TwiddleSizes m tw)
    (hs : X.size = 2 ^ m) (hu : 4 * 2 ^ m < USize.size) :
    Native.leafLayers p (tw.map encode) m count (encode X) = encode (fieldLayers tw m count X) := by
  have hX : (if m % 2 = 1 then
      Native.pairs p ((tw.map encode).getD (m - 1) .empty) (2 ^ (m - 1)) 0 0
      (2 ^ (m - 1)) (encode X) else encode X) = encode (if m % 2 = 1 then
      Plan.butterflyDIFInner (tw.getD (m - 1) #[]) (2 ^ (m - 1)) 0 0 (2 ^ (m - 1)) X else X) := by
    split
    · rename_i ho
      have hm : 2 ^ m = 2 * 2 ^ (m - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [getD_map_encode]
      exact Native.pairs_encode _ X _ 0 0 _ (by rwa [size_encode_fields, hs])
        (by rw [size_encode_fields, htw _ (by omega)]; omega)
        (by rw [htw _ (by omega)]) (Nat.zero_le _) (by omega) (by omega)
    · rfl
  unfold Native.leafLayers fieldLayers
  dsimp only
  rw [hX]
  apply foldl_encode (List.range count) (fun b ↦ b.size = 2 ^ m)
  · intro pass hp b hb
    have hp' := List.mem_range.mp hp
    have hh : 1 ≤ m - 1 - m % 2 - 2 * pass ∧ m - 1 - m % 2 - 2 * pass < m := by omega
    have hq : 2 ^ (m - 1 - m % 2 - 2 * pass) = 2 * 2 ^ (m - 1 - m % 2 - 2 * pass - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hle : 2 ^ (m - 1 - m % 2 - 2 * pass) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    rw [getD_map_encode, getD_map_encode]
    exact Native.radix4Blocks_encode _ _ _ _ b (by rwa [size_encode_fields, hb])
      (by rw [size_encode_fields, htw _ hh.2]; omega)
      (by rw [size_encode_fields, htw _ (by omega)]; omega)
      (by rw [htw _ hh.2]; omega) (by rw [htw _ (by omega)])
      (by rw [hb]; exact Nat.div_mul_le_self _ _)
  · intro _ _ b hb
    rw [Plan.size_butterflyDIFRadix4Blocks, hb]
  · split <;> simp only [Plan.size_butterflyDIFInner, hs]

/-- All leaf layers are the mixed radix-four DIF stages. -/
theorem fieldLayers_eq (D : NTT.Domain (FastField p))
    (tw : Array (Array (FastField p))) (X : Array (FastField p)) (hs : X.size = D.n) :
    fieldLayers tw D.logN (D.logN / 2) X = Plan.runStagesDIFRadix4WithTwiddles D tw X := by
  have hpass (high : Nat) (b : Array (FastField p)) :
      Plan.butterflyDIFRadix4Blocks (tw.getD high #[]) (tw.getD (high - 1) #[])
        (4 * 2 ^ (high - 1)) (2 ^ (high - 1)) (2 ^ D.logN / (4 * 2 ^ (high - 1))) 0 b =
      Plan.butterflyRadix4StageDIFWithTwiddles D (high - 1) (tw.getD high #[])
        (tw.getD (high - 1) #[]) b := by
    unfold Plan.butterflyRadix4StageDIFWithTwiddles
    rw [show 2 ^ (high - 1 + 2) = 4 * 2 ^ (high - 1) by rw [Nat.pow_add]; omega]
    rfl
  unfold fieldLayers
  by_cases ho : D.logN % 2 = 1
  · rw [← Plan.runStagesDIFRadix4WithTwiddles_eq_top D tw X hs ho]
    simp only [ho, ↓reduceIte]
    have htop : Plan.butterflyDIFInner (tw.getD (D.logN - 1) #[]) (2 ^ (D.logN - 1)) 0 0
        (2 ^ (D.logN - 1)) X =
        Plan.butterflyStageDIFWithTwiddles D (D.logN - 1) (tw.getD (D.logN - 1) #[]) X := by
      have h1 : D.n / 2 ^ (D.logN - 1 + 1) = 1 := by
        rw [NTT.Domain.n, show D.logN - 1 + 1 = D.logN by omega, Nat.div_self (Nat.two_pow_pos _)]
      unfold Plan.butterflyStageDIFWithTwiddles
      dsimp only
      rw [h1, Plan.butterflyDIFBlocks]
      simp only [Nat.zero_lt_one, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
      rw [Plan.butterflyDIFBlocks]
      simp only [Nat.lt_irrefl, ↓reduceIte]
    rw [htop]
    apply Plan.foldl_range_congr
    intro pass _ b
    rw [hpass, show D.logN - 1 - 1 - 2 * pass = D.logN - 2 - 2 * pass by omega]
  · simp only [ho, ↓reduceIte, Plan.runStagesDIFRadix4WithTwiddles,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl,
      pure_bind, Id.run_pure]
    apply Plan.foldl_range_congr
    intro pass _ b
    rw [hpass, show D.logN % 2 = 0 by omega, Nat.sub_zero]

/-- A natural-order leaf is the natural-order read of the mixed radix-four DIF stages,
optionally scaled. -/
theorem Native.leafNatural_encode (D : NTT.Domain (FastField p))
    (tw : Array (Array (FastField p))) (X : Array (FastField p))
    (f : FastField p) (sc : Bool) (htw : TwiddleSizes D.logN tw)
    (hone : TwiddleOnes D.logN tw) (hs : X.size = D.n) (hu : 4 * D.n < USize.size)
    (h32 : D.logN ≤ 32) :
    Native.leafNatural p (tw.map encode) D.logN f.val sc (encode X) =
      encode (decodedFields D.logN (Plan.runStagesDIFRadix4WithTwiddles D tw X) f sc) := by
  have hn : X.size = 2 ^ D.logN := hs
  have hu' : 4 * 2 ^ D.logN < USize.size := hu
  rw [← fieldLayers_eq D tw X hs]
  unfold Native.leafNatural
  split
  · rename_i hm
    have hzero : tw.getD 0 #[] = #[1] :=
      twiddle_zero_eq_one _ (by simpa using htw 0 (by omega)) (hone 0 (by omega))
    let U := fieldLayers tw D.logN (D.logN / 2 - 2) X
    have hUs : U.size = 2 ^ D.logN := by simp only [U, size_fieldLayers, hn]
    rw [Native.leafLayers_encode tw _ _ X (by omega) htw hn hu', getD_map_encode,
      getD_map_encode, getD_map_encode,
      Native.lastRev_encode _ _ _ U _ f sc hm h32 hu' hUs (by simpa using htw 3 (by omega))
        (by simpa using htw 2 (by omega)) (by simpa using htw 1 (by omega)) (hone 3 (by omega))
        (hone 2 (by omega)) (hone 1 (by omega)),
      fold_leaf16Stages_eq_radix4 _ _ _ _ U (by rw [hUs]; exact Nat.div_mul_le_self _ _)]
    congr 2
    have hrange : List.range (D.logN / 2) =
        List.range (D.logN / 2 - 2) ++ [D.logN / 2 - 2, D.logN / 2 - 1] := by
      obtain ⟨P, hP⟩ : ∃ P, D.logN / 2 = P + 2 := ⟨D.logN / 2 - 2, by omega⟩
      rw [hP, List.range_succ, List.range_succ, List.append_assoc]
      rfl
    have h3 : D.logN - 1 - D.logN % 2 - 2 * (D.logN / 2 - 2) = 3 := by omega
    have h1 : D.logN - 1 - D.logN % 2 - 2 * (D.logN / 2 - 1) = 1 := by omega
    have hd : 16 ∣ 2 ^ D.logN := by simpa using Nat.pow_dvd_pow 2 (show 4 ≤ D.logN by omega)
    unfold fieldLayers
    rw [hrange, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
    simp only [h3, h1, Nat.reduceSub, Nat.reducePow, hzero]
    rw [show 2 ^ D.logN / 4 = 4 * (2 ^ D.logN / 16) by omega]
    rfl
  · rw [Native.leafLayers_encode tw _ _ X (le_refl _) htw hn hu',
      Native.decode_encode _ _ f sc h32 (by rw [size_fieldLayers, hn])
        (by rw [size_encode_fields, size_fieldLayers, hn]; exact hu'),
      Native.encodeFields_eq]

end CompPoly.CPolynomial.NTTFast.Packed
