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

/-- A loop whose iterations preserve the packed representation has a field-array fold model. -/
theorem forIn_packFields (xs : List Nat)
    (step : Nat → Option ByteArray × ByteArray → Id (ForInStep (Option ByteArray × ByteArray)))
    (f : Nat → Array KoalaBear.Fast.Field → Array KoalaBear.Fast.Field)
    (hstep : ∀ i ∈ xs, ∀ a, step i (none, packFields a) = .yield (none, packFields (f i a)))
    (a : Array KoalaBear.Fast.Field) :
    forIn xs (none, packFields a) step =
      (none, packFields (xs.foldl (fun acc i ↦ f i acc) a)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.forIn_cons, hstep i (by simp only [List.mem_cons, true_or]) a,
      List.foldl_cons]
    exact ih (fun j hj b ↦ hstep j (List.mem_cons_of_mem i hj) b) _

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
