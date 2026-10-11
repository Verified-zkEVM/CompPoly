/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Builders
public import CompPoly.Univariate.NTTFast.Packed.PartitionKernels

/-! # Transport of packed partition-builder loops -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- A loop whose iterations write one 16-word batch at the end of a written prefix has a
field-array fold model: the prefix grows by the fold and the rest of the buffer shrinks by the
batches written. -/
theorem forIn_encode (off n : Nat)
    (step : Nat → Option ByteArray × ByteArray → Id (ForInStep (Option ByteArray × ByteArray)))
    (f : Nat → Array KoalaBear.Fast.Field → Array KoalaBear.Fast.Field)
    (hstep : ∀ i ∈ List.range' off n, ∀ l Z, l.size = 16 * i → 16 ≤ Z.size →
      (encode (l ++ Z)).size < USize.size →
      step i (none, encode (l ++ Z)) = .yield (none, encode (f i l ++ Z.extract 16 Z.size)))
    (hf : ∀ i l, (f i l).size = l.size + 16)
    (l Z : Array KoalaBear.Fast.Field) (hl : l.size = 16 * off) (hZ : 16 * n ≤ Z.size)
    (hs : (encode (l ++ Z)).size < USize.size) :
    forIn (List.range' off n) (none, encode (l ++ Z)) step =
      (none, encode ((List.range' off n).foldl (fun acc i ↦ f i acc) l ++
        Z.extract (16 * n) Z.size)) := by
  induction n generalizing off l Z with
  | zero => simp only [List.range'_zero, List.forIn_nil, List.foldl_nil, Nat.mul_zero,
    Array.extract_size]; rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons,
      hstep off (List.mem_range'.mpr ⟨0, by omega, by omega⟩) l Z hl (by omega) hs]
    simp only [List.foldl_cons]
    change forIn (List.range' (off + 1) n) (none, encode (f off l ++ Z.extract 16 Z.size))
      step = _
    have hs' : (encode (f off l ++ Z.extract 16 Z.size)).size < USize.size := by
      simp only [size_encode_fields, Array.size_append, Array.size_extract, hf] at hs ⊢
      omega
    rw [ih (off + 1) (fun j hj ↦ hstep j (List.mem_range'_1.mpr (by
        have := List.mem_range'_1.mp hj
        omega))) (f off l) (Z.extract 16 Z.size) (by rw [hf]; omega)
      (by simp only [Array.size_extract]; omega) hs',
      extract_extract_tail]
    congr 4
    omega

/-- Consecutive batches concatenate to one indexed array. -/
theorem fold_append_batches (f : Nat → α) (offset count : Nat) (a : Array α) :
    (List.range' offset count).foldl
      (fun acc block ↦ acc ++ Array.ofFn (fun k : Fin 16 ↦ f (16 * block + k.val))) a =
      a ++ Array.ofFn (fun k : Fin (16 * count) ↦ f (16 * offset + k.val)) := by
  induction count generalizing offset a with
  | zero => simp only [List.range'_zero, List.foldl_nil, Nat.mul_zero, Array.ofFn_zero,
    Array.append_empty]
  | succ count ih =>
    rw [List.range'_succ, List.foldl_cons, ih, Array.append_assoc]
    congr 1
    apply Array.ext
    · simp only [Array.size_append, Array.size_ofFn]
      omega
    · intro k hk hj
      simp only [Array.getElem_append, Array.size_ofFn, Array.getElem_ofFn]
      split
      · rename_i hlt
        congr 1
      · rename_i hge
        congr 1
        omega

end CompPoly.CPolynomial.NTTFast.Packed
