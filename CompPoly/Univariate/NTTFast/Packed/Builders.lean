/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.FieldStorage

/-! # Packed array construction and partition builders -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

private theorem fold_push_words (xs : List Nat) (f : Nat → UInt32) (b : ByteArray) :
    xs.foldl (fun acc i ↦ Native.push acc (f i)) b =
      b ++ Storage.pack (xs.map f).toArray := by
  induction xs generalizing b with
  | nil =>
    simp only [List.foldl_nil, List.map_nil]
    change b = b ++ ByteArray.empty
    exact ByteArray.append_empty.symm
  | cons i xs ih =>
    rw [List.foldl_cons, Native.push_eq, ih]
    have he : ((i :: xs).map f).toArray = #[f i] ++ (xs.map f).toArray := by
      apply Array.toList_inj.mp
      simp only [Array.toList_append, List.map_cons]
      rfl
    rw [he, Storage.pack_append, ByteArray.append_assoc]

/-- The packed generator is the encoding of its indexed array. -/
theorem Native.generate_eq (n : Nat) (f : Nat → UInt32) :
    Native.generate n f = Storage.pack (Array.ofFn (fun i : Fin n ↦ f i.val)) := by
  unfold Native.generate
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    bind_pure, Id.run_pure]
  rw [fold_push_words]
  rw [show ByteArray.emptyWithCapacity (4 * n) = ByteArray.empty from rfl,
    ByteArray.empty_append]
  congr 1
  apply Array.ext
  · simp only [List.size_toArray, List.length_map, List.length_range', Array.size_ofFn]
  · intro k hk hj
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range',
      Array.getElem_ofFn, Nat.zero_add, Nat.one_mul]

/-- Generators agree when their callbacks agree on the generated index range. -/
theorem Native.generate_congr (n : Nat) (f g : Nat → UInt32) (h : ∀ i < n, f i = g i) :
    Native.generate n f = Native.generate n g := by
  rw [Native.generate_eq, Native.generate_eq]
  apply congrArg Storage.pack
  apply congrArg Array.ofFn
  funext i
  exact h i.val i.isLt

/-- Generating canonical field words gives the packed field-array encoding. -/
theorem Native.generate_fields (n : Nat) (f : Nat → KoalaBear.Fast.Field) :
    Native.generate n (fun i ↦ (f i).val) =
      packFields (Array.ofFn (fun i : Fin n ↦ f i.val)) := by
  rw [Native.generate_eq]
  unfold packFields
  rw [Array.map_ofFn]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
