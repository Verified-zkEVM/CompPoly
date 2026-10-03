/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.FieldStorage

/-! # Representation-preserving packed folds -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Reading a packed twiddle table agrees with packing the corresponding field table entry. -/
theorem getD_map_packFields (tw : Array (Array KoalaBear.Fast.Field)) (stage : Nat) :
    (tw.map packFields).getD stage ByteArray.empty = packFields (tw.getD stage #[]) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases he : tw[stage]? with
  | none => simp only [Option.map_none, Option.getD_none, packFields_empty]
  | some values => rfl

/-- A fold transports through packing while its field-array invariant is preserved. -/
theorem foldl_packFields (xs : List Nat)
    (p : Array KoalaBear.Fast.Field → Prop)
    (raw : ByteArray → Nat → ByteArray)
    (field : Array KoalaBear.Fast.Field → Nat → Array KoalaBear.Fast.Field)
    (hf : ∀ i ∈ xs, ∀ a, p a → raw (packFields a) i = packFields (field a i))
    (hp : ∀ i ∈ xs, ∀ a, p a → p (field a i))
    (a : Array KoalaBear.Fast.Field) (ha : p a) :
    xs.foldl raw (packFields a) = packFields (xs.foldl field a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    rw [List.foldl_cons, List.foldl_cons, hf i (List.mem_cons_self ..) a ha]
    exact ih (fun j hj b hb ↦ hf j (List.mem_cons_of_mem i hj) b hb)
      (fun j hj b hb ↦ hp j (List.mem_cons_of_mem i hj) b hb)
      _ (hp i (List.mem_cons_self ..) a ha)

/-- A sequential fold preserves any invariant maintained by each visited step. -/
theorem foldl_invariant (xs : List ι) (p : α → Prop) (f : α → ι → α)
    (hf : ∀ i ∈ xs, ∀ a, p a → p (f a i)) (a : α) (ha : p a) :
    p (xs.foldl f a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons i xs ih =>
    exact ih (fun j hj b hb ↦ hf j (List.mem_cons_of_mem i hj) b hb)
      _ (hf i (List.mem_cons_self ..) a ha)

end CompPoly.CPolynomial.NTTFast.Packed
