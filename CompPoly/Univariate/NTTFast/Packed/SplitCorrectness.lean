/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Packed.StageSpec
public import CompPoly.Univariate.NTTFast.Packed.SplitRefinement

/-! # Packed first-layer partitions refine the recursive DFT inputs -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

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
    (encode a).size < USize.size ∧
      (encode (tw.getD (D.logN - 1) #[])).size < USize.size ∧
      2 * 2 ^ (D.logN - 1) ≤ a.size ∧
      2 ^ (D.logN - 1) ≤ (tw.getD (D.logN - 1) #[]).size := by
  obtain ⟨hsize, hone⟩ := ht.invariants D tw
  have hw := hsize (D.logN - 1) (by omega)
  have hn := halfDomain_size D hlog
  change D.n = 2 * 2 ^ (D.logN - 1) at hn
  simp only [size_encode_fields, hs, hw]
  omega

/-- Packed left partitioning computes the sum input used by the even-point child. -/
theorem Native.splitLeft_correct (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.splitLeft (encode a) ((tw.map encode).getD (D.logN - 1) ByteArray.empty)
      (2 ^ (D.logN - 1)) = encode (splitFieldsLeft D a) := by
  obtain ⟨ha, hw, hshape, htw⟩ := split_bounds D hlog tw a ht hs hu
  rw [getD_map_encode, Native.splitLeft_encode a _ _ ha hw hshape htw]
  rfl

/-- Packed right partitioning computes the scaled difference input used by the odd-point child. -/
theorem Native.splitRight_correct (D : NTT.Domain KoalaBear.Fast.Field) (hlog : 0 < D.logN)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size) :
    Native.splitRight (encode a) ((tw.map encode).getD (D.logN - 1) ByteArray.empty)
      (2 ^ (D.logN - 1)) = encode (splitFieldsRight D a) := by
  obtain ⟨ha, hw, hshape, htw⟩ := split_bounds D hlog tw a ht hs hu
  rw [getD_map_encode, Native.splitRight_encode a _ _ ha hw hshape htw]
  unfold splitFieldsRight
  apply congrArg encode
  apply congrArg Array.ofFn
  funext i
  rw [top_twiddle_getD D hlog tw ht i.val i.isLt]

end CompPoly.CPolynomial.NTTFast.Packed
