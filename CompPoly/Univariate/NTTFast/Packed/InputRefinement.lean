/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.SplitRefinement
public import CompPoly.Univariate.NTTFast.Packed.SplitRefinement

/-! # Refinement of the fused public-array input split -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- Fusing the input read computes the same first-layer partition coordinates. -/
theorem Native.splitInputLeft_encode (a : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (encode a).size < USize.size) (hs : 2 * half ≤ a.size) :
      Native.splitInputLeft a half = encode (Array.ofFn (fun i : Fin half ↦ a.getD i.val 0 +
      a.getD (i.val + half) 0)) := by
  have haN : 4 * a.size < USize.size := by simpa only [size_encode_fields] using ha
  have hloop (block : Nat) (hb : block ∈ List.range' 0 (half / 16)) :
      16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size := by
    have hbn : block < half / 16 := by
      obtain ⟨b, hb, he⟩ := List.mem_range'.mp hb
      have heb : block = b := by simpa only [Nat.zero_add, Nat.one_mul] using he
      rw [heb]
      exact hb
    have hbl : 16 * block + 16 ≤ half := by omega
    omega
  unfold Native.splitInputLeft
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  split
  · change Native.splitLeft (Native.encodeFields a) ByteArray.empty half = _
    rw [Native.encodeFields_eq, Native.splitLeft_empty]
    exact left_generate a half ha hs
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    have he : 16 * (half / 16) = half := by omega
    have hfor := forIn_encode 0 (half / 16)
      (fun block state ↦
        if h : 16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size then
          pure (.yield (none, Native.splitInputStepLeft a
            (USize.ofNatLT (16 * block) (by omega))
            (USize.ofNatLT (16 * block + half) (by omega)) state.2
            (USize.ofNatLT (16 * block) (by omega)) (by simpa only [USize.toNat_ofNatLT] using h)))
        else pure (.done (some (Native.splitLeft (Native.encodeFields a) ByteArray.empty half),
            state.2)))
      (fun block out ↦ out ++ Array.ofFn (fun k : Fin 16 ↦ a.getD (16 * block + k.val) 0 + a.getD
        (16 * block + k.val + half) 0))
      (by
        intro block hb l Z hl hZ hs'
        rw [dite_eq_left (hloop block hb),
          Native.splitInputStepLeft_encode a #[] l Z _ _ _ ?hp hZ hs',
          splitInputStepLeftField_eq]
        simp only [USize.toNat_ofNatLT, PackedRepr.encode_append, Nat.add_assoc, Nat.add_comm half]
        rfl
        simp only [USize.toNat_ofNatLT]
        omega)
      (fun _ _ ↦ by simp only [Array.size_append, Array.size_ofFn])
      #[] (Array.replicate half 0) rfl (by simp only [Array.size_replicate]; omega)
      (by simp only [size_encode_fields, Array.size_append, Array.size_replicate, Array.size_empty]
          omega)
    rw [Native.zeroWords_encode, show Array.replicate half (0 : KoalaBear.Fast.Field) =
      #[] ++ Array.replicate half 0 from Array.empty_append.symm, hfor]
    simp only [bind, pure, Id.run]
    rw [fold_append_batches (fun i ↦ a.getD i 0 + a.getD (i + half) 0) 0 (half / 16) #[]]
    simp only [Nat.mul_zero, Nat.zero_add, Array.empty_append]
    rw [he, Array.extract_eq_empty_of_le (by simp only [Array.size_replicate]; omega),
      Array.append_empty]

/-- Fusing the input read computes the same first-layer partition coordinates. -/
theorem Native.splitInputRight_encode (a w : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (encode a).size < USize.size) (hs : 2 * half ≤ a.size)
    (hw : (encode w).size < USize.size) (hws : half ≤ w.size) :
    Native.splitInputRight a (encode w) half = encode (Array.ofFn (fun i : Fin half ↦
      w.getD i.val 0 * (a.getD i.val 0 - a.getD (i.val + half) 0))) := by
  have haN : 4 * a.size < USize.size := by simpa only [size_encode_fields] using ha
  have hwN : 4 * w.size < USize.size := by simpa only [size_encode_fields] using hw
  have hloop (block : Nat) (hb : block ∈ List.range' 0 (half / 16)) :
      16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size ∧ 4 * (16
        * block + 15) + 3 < (encode w).size ∧ (encode w).size < USize.size := by
    have hbn : block < half / 16 := by
      obtain ⟨b, hb, he⟩ := List.mem_range'.mp hb
      have heb : block = b := by simpa only [Nat.zero_add, Nat.one_mul] using he
      rw [heb]
      exact hb
    have hbl : 16 * block + 16 ≤ half := by omega
    simp only [size_encode_fields]
    omega
  unfold Native.splitInputRight
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  split
  · change Native.splitRight (Native.encodeFields a) (encode w) half = _
    rw [Native.encodeFields_eq]
    exact Native.splitRight_encode a w half ha hw hs hws
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    have he : 16 * (half / 16) = half := by omega
    have hfor := forIn_encode 0 (half / 16)
      (fun block state ↦
        if h : 16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size ∧
          4 * (16 * block + 15) + 3 < (encode w).size ∧ (encode w).size < USize.size then
          pure (.yield (none, Native.splitInputStepRight a (encode w)
            (USize.ofNatLT (16 * block) (by omega))
            (USize.ofNatLT (16 * block + half) (by omega)) state.2
            (USize.ofNatLT (16 * block) (by omega)) (by simpa only [USize.toNat_ofNatLT] using h)))
        else pure (.done (some (Native.splitRight (Native.encodeFields a) (encode w) half),
            state.2)))
      (fun block out ↦ out ++ Array.ofFn (fun k : Fin 16 ↦ w.getD (16 * block + k.val) 0 *
        (a.getD (16 * block + k.val) 0 - a.getD (16 * block + k.val + half) 0)))
      (by
        intro block hb l Z hl hZ hs'
        rw [dite_eq_left (hloop block hb),
          Native.splitInputStepRight_encode a w l Z _ _ _ ?hp hZ hs',
          splitInputStepRightField_eq]
        simp only [USize.toNat_ofNatLT, PackedRepr.encode_append, Nat.add_assoc, Nat.add_comm half]
        rfl
        simp only [USize.toNat_ofNatLT]
        omega)
      (fun _ _ ↦ by simp only [Array.size_append, Array.size_ofFn])
      #[] (Array.replicate half 0) rfl (by simp only [Array.size_replicate]; omega)
      (by simp only [size_encode_fields, Array.size_append, Array.size_replicate, Array.size_empty]
          omega)
    rw [Native.zeroWords_encode, show Array.replicate half (0 : KoalaBear.Fast.Field) =
      #[] ++ Array.replicate half 0 from Array.empty_append.symm, hfor]
    simp only [bind, pure, Id.run]
    rw [fold_append_batches (fun i ↦ w.getD i 0 * (a.getD i 0 - a.getD (i + half) 0)) 0 (half /
      16) #[]]
    simp only [Nat.mul_zero, Nat.zero_add, Array.empty_append]
    rw [he, Array.extract_eq_empty_of_le (by simp only [Array.size_replicate]; omega),
      Array.append_empty]

end CompPoly.CPolynomial.NTTFast.Packed
