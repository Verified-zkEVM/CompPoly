/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Packed.StageSpec
public import CompPoly.Univariate.NTTFast.Packed.InputRefinement

/-! # Packed first-layer partitions refine the recursive DFT inputs -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The top DIF stage's twiddle at coordinate `i` is exactly the domain root raised to `i`. -/
theorem top_twiddle_getD (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (ht : TwiddlesFor D tw)
    (i : Nat) (hi : i < 2 ^ (D.logN - 1)) :
    (tw.getD (D.logN - 1) #[]).getD i 0 = D.omega ^ i := by
  rw [ht _ (by omega), Plan.twiddleTable_getD_eq_twiddlePowers D _ (by omega),
    Plan.twiddlePowers_getD_eq_pow D _ i hi]
  have he : D.logN - 1 + 1 = D.logN := by omega
  rw [he, NTT.Domain.n, Nat.div_self (Nat.two_pow_pos _), pow_one]

private theorem split_bounds (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    (packFields a).size < USize.size ∧
      (packFields (tw.getD (D.logN - 1) #[])).size < USize.size ∧
      2 * 2 ^ (D.logN - 1) ≤ a.size ∧
      2 ^ (D.logN - 1) ≤ (tw.getD (D.logN - 1) #[]).size := by
  obtain ⟨hsize, hone⟩ := ht.invariants D tw
  have hw := hsize (D.logN - 1) (by omega)
  have hn := halfDomain_size D hlog
  change D.n = 2 * 2 ^ (D.logN - 1) at hn
  simp only [size_packFields, hs, hw]
  omega

/-- Packed left partitioning computes the sum input used by the even-point child. -/
theorem Native.splitLeft_correct (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.splitLeft (packFields a) ((tw.map packFields).getD (D.logN - 1) ByteArray.empty)
      (2 ^ (D.logN - 1)) = packFields (splitFieldsLeft D a) := by
  obtain ⟨ha, hw, hshape, htw⟩ := split_bounds D hlog tw a ht hs hu
  rw [getD_map_packFields, Native.splitLeft_packFields a _ _ ha hw hshape htw]
  rfl

/-- Packed right partitioning computes the scaled difference input used by the odd-point child. -/
theorem Native.splitRight_correct (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.splitRight (packFields a) ((tw.map packFields).getD (D.logN - 1) ByteArray.empty)
      (2 ^ (D.logN - 1)) = packFields (splitFieldsRight D a) := by
  obtain ⟨ha, hw, hshape, htw⟩ := split_bounds D hlog tw a ht hs hu
  rw [getD_map_packFields, Native.splitRight_packFields a _ _ ha hw hshape htw]
  unfold splitFieldsRight
  apply congrArg packFields
  apply congrArg Array.ofFn
  funext i
  rw [top_twiddle_getD D hlog tw ht i.val i.isLt]

/-- Fusing the initial boxed-array read preserves the even-point child's input. -/
theorem Native.splitInputLeft_correct (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.splitInputLeft a (2 ^ (D.logN - 1)) = packFields (splitFieldsLeft D a) := by
  obtain ⟨ha, hw, hshape, htw⟩ := split_bounds D hlog tw a ht hs hu
  exact Native.splitInputLeft_packFields a _ ha hshape

/-- Fusing the initial boxed-array read preserves the odd-point child's input. -/
theorem Native.splitInputRight_correct (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.splitInputRight a ((tw.map packFields).getD (D.logN - 1) ByteArray.empty)
      (2 ^ (D.logN - 1)) = packFields (splitFieldsRight D a) := by
  obtain ⟨ha, hw, hshape, htw⟩ := split_bounds D hlog tw a ht hs hu
  rw [getD_map_packFields, Native.splitInputRight_packFields a _ _ ha hshape hw htw]
  unfold splitFieldsRight
  apply congrArg packFields
  apply congrArg Array.ofFn
  funext i
  rw [top_twiddle_getD D hlog tw ht i.val i.isLt]

end CompPoly.CPolynomial.NTTFast.Packed
