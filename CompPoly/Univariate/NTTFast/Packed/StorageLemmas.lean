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

/-- A proved byte range rules out wrapping in the machine-sized byte offset. -/
theorem wordOffset_toNat (i o : USize) (h : 4 * (i.toNat + o.toNat) + 3 < USize.size) :
    ((i + o) * 4).toNat = 4 * (i.toNat + o.toNat) := by
  have hn : i.toNat + o.toNat < USize.size := by omega
  rw [USize.toNat_mul, USize.toNat_add, Nat.mod_eq_of_lt hn,
    usize_numeral 4 (by decide), Nat.mod_eq_of_lt (show (i.toNat + o.toNat) * 4 < USize.size by
      omega)]
  omega

/-- The bounded read primitive reads the corresponding packed array entry. -/
theorem readRaw_pack_false (words : Array UInt32) (i o : USize)
    (h : 4 * (i.toNat + o.toNat) + 3 < (Storage.pack words).size ∧
      (Storage.pack words).size < USize.size) :
    readRaw (Storage.pack words) i o false (fun _ ↦ h) =
      words.getD (i.toNat + o.toNat) 0 := by
  have hb : 4 * (i.toNat + o.toNat) + 3 < USize.size := h.1.trans h.2
  simp only [readRaw, Bool.false_and, Bool.false_eq_true, ↓reduceIte, wordOffset_toNat i o hb]
  exact Storage.wordAt_pack words (i.toNat + o.toNat)

/-- Checked reads agree with the same array entry whenever the slot is in bounds. -/
theorem readRaw_pack_true (words : Array UInt32) (i o : USize)
    (h : 4 * (i.toNat + o.toNat) + 3 < (Storage.pack words).size ∧
      (Storage.pack words).size < USize.size) :
    readRaw (Storage.pack words) i o true (by intro h; cases h) =
      words.getD (i.toNat + o.toNat) 0 := by
  have hb : 4 * (i.toNat + o.toNat) + 3 < USize.size := h.1.trans h.2
  simp only [readRaw, wordOffset_toNat i o hb, h.1, hb, and_self, decide_true,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  exact Storage.wordAt_pack words (i.toNat + o.toNat)

/-- Ordinary checked reads preserve valid packed word coordinates. -/
theorem read_pack (words : Array UInt32) (index : Nat)
    (hs : (Storage.pack words).size < USize.size) (hi : index < words.size) :
    read (Storage.pack words) index = words.getD index 0 := by
  have hk : 4 * index + 3 < (Storage.pack words).size := by rw [Storage.size_pack]; omega
  have hin : index < USize.size := by rw [Storage.size_pack] at hs; omega
  have hu : index.toUSize.toNat = index := USize.toNat_ofNat_of_lt' hin
  have hzero : (0 : USize).toNat = 0 := rfl
  unfold read
  have h := readRaw_pack_true words index.toUSize 0
    (by simp only [hu, hzero, Nat.add_zero]; exact ⟨hk, hs⟩)
  simpa only [hu, hzero, Nat.add_zero] using h

/-- A bounded offset read preserves the represented word array. -/
theorem readUOffset_pack (words : Array UInt32) (i o : USize) (h) :
    readUOffset (Storage.pack words) i o h = words.getD (i.toNat + o.toNat) 0 :=
  readRaw_pack_false words i o h

/-- The append primitive appends the given canonical word slots. -/
theorem storeWords_append_pack (words : Array UInt32) (offset : USize) (count : UInt8)
    (hc : count.toNat ≤ 16)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    storeWords (Storage.pack words) offset count true
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
    Storage.pack (words ++
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].extract
        0 count.toNat) := by
  simp only [storeWords, Nat.not_lt.mpr hc, ↓reduceIte,
    ← Storage.pack_append]

/-- The overwrite primitive changes precisely the specified word slots. -/
theorem storeWords_replace_pack (words : Array UInt32) (offset : USize)
    (count : UInt8) (index : Nat) (hc : count.toNat ≤ 16)
    (ho : offset.toNat = 4 * index) (hi : index + count.toNat ≤ words.size)
    (hs : (Storage.pack words).size < USize.size)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    storeWords (Storage.pack words) offset count false
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
    Storage.pack (words.extract 0 index ++
      #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].extract
        0 count.toNat ++ words.extract (index + count.toNat) words.size) := by
  have hb : offset.toNat + 4 * count.toNat ≤ (Storage.pack words).size := by
    rw [ho, Storage.size_pack]; omega
  have hu : offset.toNat + 4 * count.toNat < USize.size := hb.trans_lt hs
  simp only [ho] at hb hu
  have hv : (#[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].extract
      0 count.toNat).size = count.toNat := by
    rw [Array.size_extract]
    change min count.toNat 16 - 0 = count.toNat
    omega
  simp only [storeWords, Nat.not_lt.mpr hc, ↓reduceIte, Bool.false_eq_true, ho, hb, hu,
    and_self, Storage.replace_pack, hv]

end CompPoly.CPolynomial.NTTFast.Packed.Native
