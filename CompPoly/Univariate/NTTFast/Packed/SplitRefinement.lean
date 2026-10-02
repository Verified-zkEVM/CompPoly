/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.BatchBuilders

/-! # Refinement of packed parallel partition builders -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

private theorem left_generate (a : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (packFields a).size < USize.size) (hs : 2 * half ≤ a.size) :
    Native.generate half (fun i ↦ add (Native.read (packFields a) i)
      (Native.read (packFields a) (i + half))) =
      packFields (Array.ofFn (fun i : Fin half ↦ a.getD i.val 0 + a.getD (i.val + half) 0)) := by
  rw [Native.generate_eq]
  change _ = Storage.pack ((Array.ofFn (fun i : Fin half ↦ a.getD i.val 0 + a.getD (i.val + half)
    0)).map Subtype.val)
  rw [Array.map_ofFn]
  apply congrArg Storage.pack
  apply congrArg Array.ofFn
  funext i
  simp (disch := omega) only [Native.read_packFields, add_val, Function.comp_apply]

/-- The packed left partition has the ordinary first-layer sum coordinates. -/
theorem Native.splitLeft_packFields (a w : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (packFields a).size < USize.size) (hw : (packFields w).size < USize.size)
    (hs : 2 * half ≤ a.size) (hws : half ≤ w.size) :
    Native.splitLeft (packFields a) (packFields w) half =
      packFields (Array.ofFn (fun i : Fin half ↦ a.getD i.val 0 + a.getD (i.val + half) 0)) := by
  have haN : 4 * a.size < USize.size := by simpa only [size_packFields] using ha
  have hwN : 4 * w.size < USize.size := by simpa only [size_packFields] using hw
  have hloop (block : Nat) (hb : block ∈ List.range' 0 (half / 16)) :
      4 * (16 * block + 15) + 3 < (packFields a).size ∧
      4 * (16 * block + half + 15) + 3 < (packFields a).size ∧
      4 * (16 * block + 15) + 3 < (packFields w).size ∧
      (packFields a).size < USize.size ∧ (packFields w).size < USize.size := by
    have hbn : block < half / 16 := by
      obtain ⟨b, hb, he⟩ := List.mem_range'.mp hb
      have heb : block = b := by simpa only [Nat.zero_add, Nat.one_mul] using he
      rw [heb]
      exact hb
    have hbl : 16 * block + 16 ≤ half := by omega
    simp only [size_packFields]
    omega
  unfold Native.splitLeft
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  split
  · simpa only [Id.run_pure] using left_generate a half ha hs
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    have he : 16 * (half / 16) = half := by omega
    have hfor := forIn_packFields (List.range' 0 (half / 16))
      (fun block state ↦
        if h : 4 * (16 * block + 15) + 3 < (packFields a).size ∧
          4 * (16 * block + half + 15) + 3 < (packFields a).size ∧
          4 * (16 * block + 15) + 3 < (packFields w).size ∧
          (packFields a).size < USize.size ∧ (packFields w).size < USize.size then
          pure (.yield (none, Native.splitStepLeft (packFields a) (packFields w)
            (USize.ofNatLT (16 * block) (by omega))
            (USize.ofNatLT (16 * block + half) (by omega)) state.2
            (by simpa only [USize.toNat_ofNatLT] using h)))
        else pure (.done (some (Native.generate half (fun i ↦ add (Native.read (packFields a) i)
          (Native.read (packFields a) (i + half)))), state.2)))
      (fun block out ↦ out ++ Array.ofFn (fun k : Fin 16 ↦
        a.getD (16 * block + k.val) 0 + a.getD (16 * block + k.val + half) 0))
      (by
        intro block hb out
        rw [dite_eq_left (hloop block hb), Native.splitStepLeft_packFields, splitStepLeftField_eq]
        simp only [USize.toNat_ofNatLT, packFields_append]
        simp only [Nat.add_assoc, Nat.add_comm half]
        rfl)
      #[]
    rw [show ByteArray.emptyWithCapacity (4 * half) = packFields (#[] : Array
      KoalaBear.Fast.Field) by rw [packFields_empty]; rfl]
    rw [hfor]
    simp only [bind, pure, Id.run]
    rw [fold_append_batches (fun i ↦ a.getD i 0 + a.getD (i + half) 0) 0 (half / 16) #[]]
    simp only [Nat.mul_zero, Nat.zero_add, Array.empty_append]
    rw [he]

private theorem right_generate (a w : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (packFields a).size < USize.size) (hw : (packFields w).size < USize.size)
    (hs : 2 * half ≤ a.size) (hws : half ≤ w.size) :
    Native.generate half (fun i ↦ mul (Native.read (packFields w) i)
      (sub (Native.read (packFields a) i) (Native.read (packFields a) (i + half)))) =
      packFields (Array.ofFn (fun i : Fin half ↦
        w.getD i.val 0 * (a.getD i.val 0 - a.getD (i.val + half) 0))) := by
  calc
    _ = Native.generate half (fun i ↦
        (w.getD i 0 * (a.getD i 0 - a.getD (i + half) 0)).val) := by
      apply Native.generate_congr
      intro i hi
      rw [Native.read_packFields w i hw (by omega),
        Native.read_packFields a i ha (by omega),
        Native.read_packFields a (i + half) ha (by omega)]
      exact mul_sub_val _ _ _
    _ = _ := Native.generate_fields half (fun i ↦
      w.getD i 0 * (a.getD i 0 - a.getD (i + half) 0))

/-- The packed right partition has the ordinary first-layer twiddle-scaled difference
  coordinates. -/
theorem Native.splitRight_packFields (a w : Array KoalaBear.Fast.Field) (half : Nat)
    (ha : (packFields a).size < USize.size) (hw : (packFields w).size < USize.size)
    (hs : 2 * half ≤ a.size) (hws : half ≤ w.size) :
    Native.splitRight (packFields a) (packFields w) half =
      packFields (Array.ofFn (fun i : Fin half ↦ w.getD i.val 0 * (a.getD i.val 0 - a.getD (i.val
        + half) 0))) := by
  have haN : 4 * a.size < USize.size := by simpa only [size_packFields] using ha
  have hwN : 4 * w.size < USize.size := by simpa only [size_packFields] using hw
  have hloop (block : Nat) (hb : block ∈ List.range' 0 (half / 16)) :
      4 * (16 * block + 15) + 3 < (packFields a).size ∧
      4 * (16 * block + half + 15) + 3 < (packFields a).size ∧
      4 * (16 * block + 15) + 3 < (packFields w).size ∧
      (packFields a).size < USize.size ∧ (packFields w).size < USize.size := by
    have hbn : block < half / 16 := by
      obtain ⟨b, hb, he⟩ := List.mem_range'.mp hb
      have heb : block = b := by simpa only [Nat.zero_add, Nat.one_mul] using he
      rw [heb]
      exact hb
    have hbl : 16 * block + 16 ≤ half := by omega
    simp only [size_packFields]
    omega
  unfold Native.splitRight
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  split
  · simpa only [Id.run_pure] using right_generate a w half ha hw hs hws
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    have he : 16 * (half / 16) = half := by omega
    have hfor := forIn_packFields (List.range' 0 (half / 16))
      (fun block state ↦
        if h : 4 * (16 * block + 15) + 3 < (packFields a).size ∧
          4 * (16 * block + half + 15) + 3 < (packFields a).size ∧
          4 * (16 * block + 15) + 3 < (packFields w).size ∧
          (packFields a).size < USize.size ∧ (packFields w).size < USize.size then
          pure (.yield (none, Native.splitStepRight (packFields a) (packFields w)
            (USize.ofNatLT (16 * block) (by omega))
            (USize.ofNatLT (16 * block + half) (by omega)) state.2
            (by simpa only [USize.toNat_ofNatLT] using h)))
        else pure (.done (some (Native.generate half (fun i ↦ mul (Native.read (packFields w) i)
          (sub (Native.read (packFields a) i)
          (Native.read (packFields a) (i + half))))), state.2)))
      (fun block out ↦ out ++ Array.ofFn (fun k : Fin 16 ↦
        w.getD (16 * block + k.val) 0 * (a.getD (16 * block + k.val) 0 - a.getD (16 * block +
          k.val + half) 0)))
      (by
        intro block hb out
        rw [dite_eq_left (hloop block hb), Native.splitStepRight_packFields, splitStepRightField_eq]
        simp only [USize.toNat_ofNatLT, packFields_append]
        simp only [Nat.add_assoc, Nat.add_comm half]
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

/-- Without a twiddle buffer, the left splitter uses its scalar builder. -/
theorem Native.splitLeft_empty (a : ByteArray) (half : Nat) :
    Native.splitLeft a ByteArray.empty half =
      Native.generate half (fun i ↦ add (Native.read a i) (Native.read a (i + half))) := by
  unfold Native.splitLeft
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  split
  · rfl
  · rename_i hmod
    have hm : half % 16 = 0 := by simpa using hmod
    by_cases hn : half / 16 = 0
    · have hz : half = 0 := by omega
      subst half
      simp only [Nat.zero_div, List.range'_zero, List.forIn_nil, bind, pure, Id.run,
        Native.generate, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
        Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    · obtain ⟨count, hc⟩ : ∃ count, half / 16 = count + 1 := ⟨half / 16 - 1, by omega⟩
      rw [hc, List.range'_succ, List.forIn_cons]
      simp only [ByteArray.size_empty, Nat.mul_zero, Nat.zero_add, Nat.not_lt_zero,
        and_false, false_and, dite_false, bind, pure, Id.run]

end CompPoly.CPolynomial.NTTFast.Packed
