/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.Native

/-! # Word-storage refinement lemmas for the native FFT -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open CompPoly.PackedRepr (encode size_encode_uint32)

theorem ugetUInt32LE_eq (a : ByteArray) (i : USize) (h) :
    a.ugetUInt32LE i h = a.getUInt32LE! i.toNat := rfl

theorem usetUInt32LE_eq (a : ByteArray) (i : USize) (v : UInt32) (h) :
    a.usetUInt32LE i v h = a.setUInt32LE! i.toNat v := rfl

/-- A bounded offset read preserves the represented word array. -/
theorem readUOffset_encodeWords (words : Array UInt32) (i o : USize) (h) :
    readUOffset (encode words) i o h = words.getD (i.toNat + o.toNat) 0 := by
  have hb : 4 * (i.toNat + o.toNat) + 3 < USize.size := h.1.trans h.2
  rw [readUOffset, ugetUInt32LE_eq, wordOffset_toNat i o hb, PackedRepr.getUInt32LE!_encode]

/-- Checked reads agree with the same array entry whenever the slot is in bounds. -/
theorem readAt_encodeWords (words : Array UInt32) (i o : USize)
    (h : 4 * (i.toNat + o.toNat) + 3 < (encode words).size ∧
      (encode words).size < USize.size) :
    readAt (encode words) i o = words.getD (i.toNat + o.toNat) 0 := by
  have hb : 4 * (i.toNat + o.toNat) + 3 < USize.size := h.1.trans h.2
  have hu : (encode words).usize.toNat = (encode words).size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' h.2]
  have h4 := usize_numeral 4 (by decide)
  have hc : 4 ≤ (encode words).usize ∧ (i + o) * 4 ≤ (encode words).usize - 4 := by
    have h4' : 4 ≤ (encode words).usize := by
      rw [USize.le_iff_toNat_le, hu, h4]; omega
    refine ⟨h4', ?_⟩
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h4', hu, h4, wordOffset_toNat i o hb]
    omega
  rw [readAt, dite_eq_left_of_eq_true (eq_true hc), ugetUInt32LE_eq, wordOffset_toNat i o hb,
    PackedRepr.getUInt32LE!_encode]

/-- Ordinary checked reads preserve valid packed word coordinates. -/
theorem read_encodeWords (words : Array UInt32) (index : Nat)
    (hs : (encode words).size < USize.size) (hi : index < words.size) :
    read (encode words) index = words.getD index 0 := by
  have hk : 4 * index + 3 < (encode words).size := by rw [size_encode_uint32]; omega
  have hin : index < USize.size := by rw [size_encode_uint32] at hs; omega
  have hu : index.toUSize.toNat = index := USize.toNat_ofNat_of_lt' hin
  have hzero : (0 : USize).toNat = 0 := rfl
  unfold read
  have h := readAt_encodeWords words index.toUSize 0
    (by simp only [hu, hzero, Nat.add_zero]; exact ⟨hk, hs⟩)
  simpa only [hu, hzero, Nat.add_zero] using h

/-! ### Batch stores -/

/-- The words of a batch. -/
abbrev batch (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) : Array UInt32 :=
  #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem extract_push_getElem (V : Array UInt32) (k : Nat) (hk : k < V.size) :
    V.extract 0 k ++ #[V[k]] = V.extract 0 (k + 1) := by
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract, List.size_toArray, List.length_cons,
      List.length_nil]
    omega
  · intro j h1 h2
    simp only [Array.getElem_append, Array.getElem_extract, Array.size_extract]
    split_ifs <;> first | omega | rfl |
      (simp only [Array.getElem_singleton]; congr 1; simp only [Array.size_extract] at *; omega)

/-- One word of a batch store, as a step of a growing byte-range replacement. -/
theorem putWord_eq {n : Nat} (s : {x : ByteArray // x.size = n}) (off : USize) (c k : Nat)
    (d : USize) (hd : d.toNat = 4 * k)
    (V : Array UInt32) (hk : k < V.size) (h) (b : ByteArray) (hb : b.size = n)
    (hs : s.1 = ByteArray.replaceAt b off.toNat (encode (V.extract 0 (min k c)))) :
    (putWord s off c k d hd V[k] h).1 =
      ByteArray.replaceAt b off.toNat (encode (V.extract 0 (min (k + 1) c))) := by
  unfold putWord
  split
  · rename_i hkc
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    have hu : (off + d).toNat = off.toNat + 4 * k := by
      rw [USize.toNat_add, hd, hsize, Nat.mod_eq_of_lt (by omega)]
    have hp : (encode (V.extract 0 k)).size = 4 * k := by
      rw [size_encode_uint32, Array.size_extract]; omega
    simp only [usetUInt32LE_eq, hu, hs, Nat.min_eq_left (show k ≤ c by omega),
      Nat.min_eq_left (show k + 1 ≤ c by omega)]
    rw [PackedRepr.setUInt32LE!_eq_replaceAt_encode _ _ _ (by
        rw [ByteArray.size_replaceAt _ _ _ (by rw [hp]; omega)]; omega),
      ← hp, ByteArray.replaceAt_replaceAt _ _ _ _ (by rw [hp, size_encode_uint32]; simp only
        [List.size_toArray, List.length_cons, List.length_nil]; omega),
      ← PackedRepr.encode_append, extract_push_getElem V k hk]
  · rename_i hkc
    rw [hs, Nat.min_eq_right (show c ≤ k by omega), Nat.min_eq_right (show c ≤ k + 1 by omega)]

/-- A batch store replaces the batch's byte range. -/
theorem putWords_eq (b : ByteArray) (off : USize) (c : Nat) (hc : c ≤ 16)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) (h) :
    putWords ⟨b, rfl⟩ off c v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 h =
      ByteArray.replaceAt b off.toNat (encode
        ((batch v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).extract 0 c)) := by
  let V := batch v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
  have e : (⟨b, rfl⟩ : {x : ByteArray // x.size = b.size}).1 =
      ByteArray.replaceAt b off.toNat (encode (V.extract 0 (min 0 c))) := by
    rw [Nat.min_eq_left (Nat.zero_le _), Array.extract_zero]
    exact (ByteArray.replaceAt_empty b _ (by omega)).symm
  have e0 := putWord_eq _ off c 0 0 (by rw [usize_numeral _ (by decide)]) V
    (show 0 < 16 by decide) h b rfl e
  have e1 := putWord_eq _ off c 1 4 (by rw [usize_numeral _ (by decide)]) V
    (show 1 < 16 by decide) h b rfl e0
  have e2 := putWord_eq _ off c 2 8 (by rw [usize_numeral _ (by decide)]) V
    (show 2 < 16 by decide) h b rfl e1
  have e3 := putWord_eq _ off c 3 12 (by rw [usize_numeral _ (by decide)]) V
    (show 3 < 16 by decide) h b rfl e2
  have e4 := putWord_eq _ off c 4 16 (by rw [usize_numeral _ (by decide)]) V
    (show 4 < 16 by decide) h b rfl e3
  have e5 := putWord_eq _ off c 5 20 (by rw [usize_numeral _ (by decide)]) V
    (show 5 < 16 by decide) h b rfl e4
  have e6 := putWord_eq _ off c 6 24 (by rw [usize_numeral _ (by decide)]) V
    (show 6 < 16 by decide) h b rfl e5
  have e7 := putWord_eq _ off c 7 28 (by rw [usize_numeral _ (by decide)]) V
    (show 7 < 16 by decide) h b rfl e6
  have e8 := putWord_eq _ off c 8 32 (by rw [usize_numeral _ (by decide)]) V
    (show 8 < 16 by decide) h b rfl e7
  have e9 := putWord_eq _ off c 9 36 (by rw [usize_numeral _ (by decide)]) V
    (show 9 < 16 by decide) h b rfl e8
  have e10 := putWord_eq _ off c 10 40 (by rw [usize_numeral _ (by decide)]) V
    (show 10 < 16 by decide) h b rfl e9
  have e11 := putWord_eq _ off c 11 44 (by rw [usize_numeral _ (by decide)]) V
    (show 11 < 16 by decide) h b rfl e10
  have e12 := putWord_eq _ off c 12 48 (by rw [usize_numeral _ (by decide)]) V
    (show 12 < 16 by decide) h b rfl e11
  have e13 := putWord_eq _ off c 13 52 (by rw [usize_numeral _ (by decide)]) V
    (show 13 < 16 by decide) h b rfl e12
  have e14 := putWord_eq _ off c 14 56 (by rw [usize_numeral _ (by decide)]) V
    (show 14 < 16 by decide) h b rfl e13
  have e15 := putWord_eq _ off c 15 60 (by rw [usize_numeral _ (by decide)]) V
    (show 15 < 16 by decide) h b rfl e14
  rw [Nat.min_eq_right (show c ≤ 15 + 1 by omega)] at e15
  exact e15

/-- The batch store is a byte-range replacement by the batch's first `count` words. -/
theorem storeWords_eq (b : ByteArray) (offset : USize) (count : UInt8)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    storeWords b offset count v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      if count.toNat > 16 then b else
      if offset ≤ offset + (4 * count.toNat).toUSize ∧
          offset + (4 * count.toNat).toUSize ≤ b.usize then
        ByteArray.replaceAt b offset.toNat (encode
          ((batch v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).extract 0 count.toNat))
      else b := by
  unfold storeWords
  split
  · rfl
  · rename_i hc
    split
    · rw [putWords_eq _ _ count.toNat (by omega)]
    · rfl

/-- In a packed buffer that fits machine indices, a batch's range check is its slot bound. -/
theorem storeWords_fits (words : Array UInt32) (offset : USize) (count : UInt8) (index : Nat)
    (hc : count.toNat ≤ 16) (ho : offset.toNat = 4 * index)
    (hs : (encode words).size < USize.size) :
    (offset ≤ offset + (4 * count.toNat).toUSize ∧
      offset + (4 * count.toNat).toUSize ≤ (encode words).usize) ↔
      index + count.toNat ≤ words.size := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [size_encode_uint32] at hs
  have hu : (encode words).usize.toNat = 4 * words.size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' (by rw [size_encode_uint32]; omega),
      size_encode_uint32]
  have h4 : (4 * count.toNat).toUSize.toNat = 4 * count.toNat :=
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)
  rw [USize.le_iff_toNat_le, USize.le_iff_toNat_le, hu, USize.toNat_add, h4, hsize, ho]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hw : 4 * index + 4 * count.toNat < USize.size
    · rw [Nat.mod_eq_of_lt hw] at h2; omega
    · have ho' := offset.toNat_lt_size
      have hle := USize.le_size
      rw [ho] at ho'
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt
        (show 4 * index + 4 * count.toNat - USize.size < USize.size by omega)] at h1
      omega
  · intro h
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The overwrite primitive changes precisely the specified word slots. -/
theorem storeWords_replace_encodeWords (words : Array UInt32) (offset : USize)
    (count : UInt8) (index : Nat) (hc : count.toNat ≤ 16)
    (ho : offset.toNat = 4 * index) (hi : index + count.toNat ≤ words.size)
    (hs : (encode words).size < USize.size)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    storeWords (encode words) offset count
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
    encode (words.extract 0 index ++
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].extract
        0 count.toNat ++ words.extract (index + count.toNat) words.size) := by
  have hf := (storeWords_fits words offset count index hc ho hs).mpr hi
  have hv : (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].extract
      0 count.toNat).size = count.toNat := by
    rw [Array.size_extract]
    change min count.toNat 16 - 0 = count.toNat
    omega
  simp only [storeWords_eq, Nat.not_lt.mpr hc, ↓reduceIte, hf, ho,
    PackedRepr.replaceAt_encode_uint32, hv, and_self]

/-! ### Zero buffers -/

/-- `m` zero bytes. -/
abbrev zeroBuffer (m : Nat) : ByteArray := ⟨Array.replicate m 0⟩

theorem zeroBuffer_eq_encodeWords (n : Nat) :
    zeroBuffer (4 * n) = encode (Array.replicate n (0 : UInt32)) := by
  apply ByteArray.ext
  simp only [encode, ← List.toArray_replicate]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ← ih,
      show 4 * (n + 1) = 4 + 4 * n by ring, List.replicate_add]
    rfl

/-- `n` zero words are the packing of `n` zeros. -/
theorem zeroWords_eq (n : Nat) :
    zeroWords n = encode (Array.replicate n (0 : UInt32)) := by
  rw [← zeroBuffer_eq_encodeWords, zeroWords, ByteArray.zeros_eq]

/-- Extending a packed buffer by one zero block appends 256 zero words. -/
theorem extendZeros_encodeWords (o : Array UInt32) :
    ByteArray.zeroBlock.copySlice 0 (encode o) (encode o).size 1024 false =
      encode (o ++ Array.replicate 256 0) := by
  have hz : ByteArray.zeroBlock.data.size = 4096 := Array.size_replicate
  have hb : ByteArray.zeroBlock.extract 0 (0 + 1024) = zeroBuffer (4 * 256) := by
    apply ByteArray.ext
    simp only [ByteArray.data_extract, ByteArray.zeroBlock, Array.extract_replicate]
    rfl
  rw [ByteArray.copySlice_eq_append, ByteArray.extract_zero_size, hb,
    (ByteArray.extract_eq_empty_iff).mpr (by simp only [ByteArray.size, hz]; omega),
    ByteArray.append_empty, PackedRepr.encode_append, zeroBuffer_eq_encodeWords]

end CompPoly.CPolynomial.NTTFast.Packed.Native
