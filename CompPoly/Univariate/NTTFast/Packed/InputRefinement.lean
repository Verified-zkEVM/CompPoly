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

/-- Fusing the input read computes the same first-layer partition coordinates. -/
theorem Native.splitInputLeft_packFields (a : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (packFields a).size < USize.size) (hs : 2 * half ≤ a.size) :
      Native.splitInputLeft a half = packFields (Array.ofFn (fun i : Fin half ↦ a.getD i.val 0 +
      a.getD (i.val + half) 0)) := by
  have haN : 4 * a.size < USize.size := by simpa only [size_packFields] using ha
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
  · change Native.splitLeft (Native.encode a) ByteArray.empty half = _
    rw [Native.encode_eq, Native.splitLeft_empty]
    exact left_generate a half ha hs
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    have he : 16 * (half / 16) = half := by omega
    have hfor := forIn_packFields (List.range' 0 (half / 16))
      (fun block state ↦
        if h : 16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size then
          pure (.yield (none, Native.splitInputStepLeft a
            (USize.ofNatLT (16 * block) (by omega))
            (USize.ofNatLT (16 * block + half) (by omega)) state.2
            (by simpa only [USize.toNat_ofNatLT] using h)))
        else pure (.done (some (Native.splitLeft (Native.encode a) ByteArray.empty half), state.2)))
      (fun block out ↦ out ++ Array.ofFn (fun k : Fin 16 ↦ a.getD (16 * block + k.val) 0 + a.getD
        (16 * block + k.val + half) 0))
      (by
        intro block hb out
        rw [dite_eq_left (hloop block hb), Native.splitInputStepLeft_packFields a #[],
          splitInputStepLeftField_eq]
        simp only [USize.toNat_ofNatLT, packFields_append, Nat.add_assoc, Nat.add_comm half]
        rfl)
      #[]
    rw [show ByteArray.emptyWithCapacity (4 * half) = packFields (#[] : Array
      KoalaBear.Fast.Field) by rw [packFields_empty]; rfl]
    rw [hfor]
    simp only [bind, pure, Id.run]
    rw [fold_append_batches (fun i ↦ a.getD i 0 + a.getD (i + half) 0) 0 (half / 16) #[]]
    simp only [Nat.mul_zero, Nat.zero_add, Array.empty_append]
    rw [he]

/-- Fusing the input read computes the same first-layer partition coordinates. -/
theorem Native.splitInputRight_packFields (a w : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (packFields a).size < USize.size) (hs : 2 * half ≤ a.size)
    (hw : (packFields w).size < USize.size) (hws : half ≤ w.size) :
    Native.splitInputRight a (packFields w) half = packFields (Array.ofFn (fun i : Fin half ↦
      w.getD i.val 0 * (a.getD i.val 0 - a.getD (i.val + half) 0))) := by
  have haN : 4 * a.size < USize.size := by simpa only [size_packFields] using ha
  have hwN : 4 * w.size < USize.size := by simpa only [size_packFields] using hw
  have hloop (block : Nat) (hb : block ∈ List.range' 0 (half / 16)) :
      16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size ∧ 4 * (16
        * block + 15) + 3 < (packFields w).size ∧ (packFields w).size < USize.size := by
    have hbn : block < half / 16 := by
      obtain ⟨b, hb, he⟩ := List.mem_range'.mp hb
      have heb : block = b := by simpa only [Nat.zero_add, Nat.one_mul] using he
      rw [heb]
      exact hb
    have hbl : 16 * block + 16 ≤ half := by omega
    simp only [size_packFields]
    omega
  unfold Native.splitInputRight
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  split
  · change Native.splitRight (Native.encode a) (packFields w) half = _
    rw [Native.encode_eq]
    exact Native.splitRight_packFields a w half ha hw hs hws
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    have he : 16 * (half / 16) = half := by omega
    have hfor := forIn_packFields (List.range' 0 (half / 16))
      (fun block state ↦
        if h : 16 * block + 15 < a.size ∧ 16 * block + half + 15 < a.size ∧ a.size < USize.size ∧
          4 * (16 * block + 15) + 3 < (packFields w).size ∧ (packFields w).size < USize.size then
          pure (.yield (none, Native.splitInputStepRight a (packFields w)
            (USize.ofNatLT (16 * block) (by omega))
            (USize.ofNatLT (16 * block + half) (by omega)) state.2
            (by simpa only [USize.toNat_ofNatLT] using h)))
        else pure (.done (some (Native.splitRight (Native.encode a) (packFields w) half), state.2)))
      (fun block out ↦ out ++ Array.ofFn (fun k : Fin 16 ↦ w.getD (16 * block + k.val) 0 *
        (a.getD (16 * block + k.val) 0 - a.getD (16 * block + k.val + half) 0)))
      (by
        intro block hb out
        rw [dite_eq_left (hloop block hb), Native.splitInputStepRight_packFields a w,
          splitInputStepRightField_eq]
        simp only [USize.toNat_ofNatLT, packFields_append, Nat.add_assoc, Nat.add_comm half]
        rfl)
      #[]
    rw [show ByteArray.emptyWithCapacity (4 * half) = packFields (#[] : Array
      KoalaBear.Fast.Field) by rw [packFields_empty]; rfl]
    rw [hfor]
    simp only [bind, pure, Id.run]
    rw [fold_append_batches (fun i ↦ w.getD i 0 * (a.getD i 0 - a.getD (i + half) 0)) 0 (half /
      16) #[]]
    simp only [Nat.mul_zero, Nat.zero_add, Array.empty_append]
    rw [he]

end CompPoly.CPolynomial.NTTFast.Packed
