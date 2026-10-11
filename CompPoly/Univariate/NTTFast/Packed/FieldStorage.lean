/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all Init.Data.Array.Basic
import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.StorageLemmas
public import CompPoly.Univariate.NTTFast.Packed.Arrays
public import CompPoly.Fields.Montgomery.Native32Bytes

/-! # Packed Montgomery field arrays -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode size_encode_uint32)

/-- Packed field coordinates are their packed Montgomery words. -/
theorem encode_eq_map_val (a : Array KoalaBear.Fast.Field) :
    encode a = encode (a.map Subtype.val) := by
  apply ByteArray.ext
  simp only [encode, Array.toList_map, List.flatMap_map]
  rfl

@[simp] theorem size_encode_fields (a : Array KoalaBear.Fast.Field) :
    (encode a).size = 4 * a.size := by
  rw [encode_eq_map_val, size_encode_uint32, Array.size_map]

/-- Reading a mapped coordinate preserves the field array's zero default. -/
theorem getD_map_val (a : Array KoalaBear.Fast.Field) (i : Nat) :
    (a.map Subtype.val).getD i 0 = (a.getD i 0).val := by
  by_cases hi : i < a.size
  · have hm : i < (a.map Subtype.val).size := by simpa only [Array.size_map] using hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem hm, Option.getD_some, Array.getElem_map]
  · have hm : ¬i < (a.map Subtype.val).size := by simpa only [Array.size_map] using hi
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hi),
      Array.getElem?_eq_none (Nat.le_of_not_lt hm), Option.getD_none]
    rfl

/-- Mapping coordinates commutes with extracting field-array segments. -/
theorem map_val_extract (a : Array KoalaBear.Fast.Field) (first last : Nat) :
    (a.extract first last).map Subtype.val = (a.map Subtype.val).extract first last := by
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Array.toList_extract, List.extract, List.map_take, List.map_drop]

/-- The compiled bounded word read returns the exact field coordinate. -/
theorem Native.readUOffset_encode (a : Array KoalaBear.Fast.Field) (i o : USize) (h) :
    Native.readUOffset (encode a) i o h = (a.getD (i.toNat + o.toNat) 0).val := by
  revert h
  simp only [encode_eq_map_val] at *
  intro h
  exact (Native.readUOffset_encodeWords (a.map Subtype.val) i o h).trans (getD_map_val a _)

/-- A checked ordinary read agrees with the represented field coordinate. -/
theorem Native.read_encode (a : Array KoalaBear.Fast.Field) (i : Nat)
    (hs : (encode a).size < USize.size) (hi : i < a.size) :
    Native.read (encode a) i = (a.getD i 0).val := by
  simp only [encode_eq_map_val] at hs ⊢
  exact (Native.read_encodeWords (a.map Subtype.val) i hs
    (by simpa only [Array.size_map] using hi)).trans (getD_map_val a i)

/-- A field-coordinate batch store realizes the corresponding array splice. -/
theorem Native.write16U_encode (a : Array KoalaBear.Fast.Field) (i : USize)
    (hs : (encode a).size < USize.size) (hi : i.toNat + 16 ≤ a.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : KoalaBear.Fast.Field) :
    Native.write16U (encode a) i x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val
      x8.val x9.val x10.val x11.val x12.val x13.val x14.val x15.val =
      encode (splice a i.toNat #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13,
        x14, x15]) := by
  have hmul : i.toNat * 4 < USize.size := by rw [size_encode_fields] at hs; omega
  have ho : (i * 4).toNat = 4 * i.toNat := by
    rw [USize.toNat_mul, Native.usize_numeral 4 (by decide), Nat.mod_eq_of_lt hmul]
    omega
  have hc : (16 : UInt8).toNat ≤ 16 := by decide
  have hvalues : (#[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val,
    x9.val, x10.val, x11.val, x12.val, x13.val, x14.val, x15.val] : Array UInt32) = (#[x0, x1,
    x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]).map Subtype.val := by
    apply Array.toList_inj.mp
    simp only [Array.toList_map]
    rfl
  unfold Native.write16U
  simp only [encode_eq_map_val] at hs ⊢
  rw [Native.storeWords_replace_encodeWords (a.map Subtype.val) (i * 4) 16 i.toNat hc ho
    (by simpa only [Array.size_map, show (16 : UInt8).toNat = 16 by decide] using hi) hs]
  simp only [show (16 : UInt8).toNat = 16 by decide]
  change encode
    ((a.map Subtype.val).extract 0 i.toNat ++ #[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val,
      x6.val, x7.val, x8.val, x9.val, x10.val, x11.val, x12.val, x13.val, x14.val,
      x15.val].extract 0 16 ++
      (a.map Subtype.val).extract (i.toNat + 16) (a.map Subtype.val).size) = _
  have hv : #[x0.val, x1.val, x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val, x9.val,
    x10.val, x11.val, x12.val, x13.val, x14.val, x15.val].extract 0 16 = #[x0.val, x1.val,
    x2.val, x3.val, x4.val, x5.val, x6.val, x7.val, x8.val, x9.val, x10.val, x11.val, x12.val,
    x13.val, x14.val, x15.val] := Array.extract_size
  rw [hv, hvalues]
  simp only [splice, Array.map_append, map_val_extract, Array.size_map]
  rfl

/-- `n` zero words represent `n` zero coordinates. -/
theorem Native.zeroWords_encode (n : Nat) :
    Native.zeroWords n = encode (Array.replicate n (0 : KoalaBear.Fast.Field)) := by
  rw [Native.zeroWords_eq, encode_eq_map_val, Array.map_replicate]
  rfl

/-- A batch store at the end of a written prefix extends the prefix and consumes the batch's
slots of the rest. -/
theorem Native.write16U_cursor (l Z : Array KoalaBear.Fast.Field) (p : USize)
    (hp : p.toNat = l.size) (hZ : 16 ≤ Z.size) (hs : (encode (l ++ Z)).size < USize.size)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : KoalaBear.Fast.Field) :
    Native.write16U (encode (l ++ Z)) p x0.val x1.val x2.val x3.val x4.val x5.val x6.val
      x7.val x8.val x9.val x10.val x11.val x12.val x13.val x14.val x15.val =
      encode (l ++ #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++
        Z.extract 16 Z.size) := by
  rw [Native.write16U_encode _ _ hs
    (by rw [Array.size_append]; omega), hp,
    splice_cursor l Z #[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] hZ]
  rfl

/-- A bounded single-coordinate write implements the corresponding field-array update. -/
theorem Native.write_encode (a : Array KoalaBear.Fast.Field) (i : Nat)
    (hs : (encode a).size < USize.size) (hi : i < a.size)
    (x : KoalaBear.Fast.Field) :
    Native.write (encode a) i x.val = encode (a.setIfInBounds i x) := by
  have hin : i < USize.size := by rw [size_encode_fields] at hs; omega
  have hmul : i * 4 < USize.size := by rw [size_encode_fields] at hs; omega
  have ho : (i.toUSize * 4).toNat = 4 * i := by
    rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hin,
      Native.usize_numeral 4 (by decide), Nat.mod_eq_of_lt hmul]
    omega
  unfold Native.write
  simp only [encode_eq_map_val] at *
  rw [Native.storeWords_replace_encodeWords (a.map Subtype.val) (i.toUSize * 4) 1 i (by decide) ho
    (by simp only [Array.size_map, show (1 : UInt8).toNat = 1 by decide]; omega) hs]
  simp only [show (1 : UInt8).toNat = 1 by decide]
  change encode ((a.map Subtype.val).extract 0 i ++ #[x.val] ++
    (a.map Subtype.val).extract (i + 1) (a.map Subtype.val).size) = _
  rw [← splice_singleton a i x hi]
  simp only [splice, Array.map_append, map_val_extract, Array.size_map, Array.size_singleton,
    Array.map_singleton]

/-- A word store on a written prefix followed by zeros extends the prefix. -/
theorem Native.write_prefix (P : Array UInt32) (n : Nat) (x : UInt32)
    (hs : 4 * (P.size + n + 1) < USize.size) :
    Native.write (encode (P ++ Array.replicate (n + 1) 0)) P.size x =
      encode (P.push x ++ Array.replicate n 0) := by
  have hin : P.size < USize.size := by omega
  have hmul : P.size * 4 < USize.size := by omega
  have ho : (P.size.toUSize * 4).toNat = 4 * P.size := by
    rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hin,
      Native.usize_numeral 4 (by decide), Nat.mod_eq_of_lt hmul]
    omega
  unfold Native.write
  rw [Native.storeWords_replace_encodeWords _ (P.size.toUSize * 4) 1 P.size (by decide) ho
    (by simp only [Array.size_append, Array.size_replicate, show (1 : UInt8).toNat = 1 by decide]
        omega)
    (by rw [size_encode_uint32, Array.size_append, Array.size_replicate]; omega)]
  simp only [show (1 : UInt8).toNat = 1 by decide]
  change encode ((P ++ Array.replicate (n + 1) 0).extract 0 P.size ++ #[x] ++
    (P ++ Array.replicate (n + 1) 0).extract (P.size + 1)
      (P ++ Array.replicate (n + 1) 0).size) = _
  rw [Array.extract_append, Array.extract_append]
  simp only [Array.extract_size, Nat.zero_sub, Nat.sub_self, Array.extract_zero,
    Array.append_empty, Array.append_singleton, Array.size_append, Array.size_replicate,
    Array.extract_replicate, Nat.add_sub_cancel_left, Nat.min_self, Nat.add_sub_cancel]
  rw [Array.extract_eq_empty_of_le (by omega), Array.empty_append]

private theorem ofFn_push (f : Nat → UInt32) (i : Nat) :
    (Array.ofFn fun k : Fin i ↦ f k.val).push (f i) = Array.ofFn fun k : Fin (i + 1) ↦ f k.val := by
  rw [Array.ofFn_succ]
  rfl

/-- Generating the remaining words of a buffer whose prefix is already written. -/
theorem Native.generateGo_encodeWords (f : Nat → UInt32) (n : Nat) : ∀ (i : Nat),
    4 * (i + n) < USize.size →
    Native.generateGo f n i
        (encode (Array.ofFn (fun k : Fin i ↦ f k.val) ++ Array.replicate n 0)) =
      encode (Array.ofFn (fun k : Fin (i + n) ↦ f k.val)) := by
  induction n with
  | zero =>
    intro i _
    simp only [Native.generateGo, Array.replicate_zero, Array.append_empty, Nat.add_zero]
  | succ n ih =>
    intro i hs
    have hP := Native.write_prefix (Array.ofFn (fun k : Fin i ↦ f k.val)) n (f i)
      (by rw [Array.size_ofFn]; omega)
    rw [Array.size_ofFn] at hP
    rw [Native.generateGo, hP, ofFn_push, ih (i + 1) (by omega),
      show i + 1 + n = i + (n + 1) by omega]

/-- The packed generator is the encoding of its indexed array. -/
theorem Native.generate_eq (n : Nat) (f : Nat → UInt32) :
    Native.generate n f = encode (Array.ofFn (fun i : Fin n ↦ f i.val)) := by
  unfold Native.generate
  split
  · rename_i hs
    have h := Native.generateGo_encodeWords f n 0 (by omega)
    rw [Array.ofFn_zero, Array.empty_append, Nat.zero_add] at h
    rw [Native.zeroWords_eq, h]
  · rfl

/-- The executable encoder realizes the packed field-array representation. -/
theorem Native.encodeFields_eq (a : Array KoalaBear.Fast.Field) :
    Native.encodeFields a = encode a := by
  rw [Native.encodeFields, Native.generate_eq, encode_eq_map_val]
  congr 1
  apply Array.ext
  · simp only [Array.size_ofFn, Array.size_map]
  · intro j h1 h2
    simp only [Array.getElem_ofFn, Array.getElem_map, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show j < a.size by simpa only [Array.size_ofFn] using h1),
      Option.getD_some]

end CompPoly.CPolynomial.NTTFast.Packed
