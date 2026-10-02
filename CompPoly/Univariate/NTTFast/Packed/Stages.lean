/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.PassRefinement
public import CompPoly.Univariate.NTTFast.Packed.Folds

/-! # Shape and twiddle invariants of packed FFT passes -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Every stored twiddle table has its stage's butterfly width. -/
def TwiddleSizes (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field)) : Prop :=
  ∀ stage < logN, (tw.getD stage #[]).size = 2 ^ stage

/-- The field-array semantics of one paired DIF pass. -/
def fieldPass (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field)) (pass : Nat)
    (a : Array KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  let high := logN - 1 - 2 * pass
  let low := high - 1
  let q := 2 ^ low
  Plan.butterflyDIFRadix4Blocks (tw.getD high #[]) (tw.getD low #[])
    (4 * q) q (2 ^ logN / (4 * q)) 0 a

/-- The paired-pass counters identify two adjacent stages within the transform. -/
theorem pass_indices (logN pass : Nat) (hp : pass < logN / 2) :
    let high := logN - 1 - 2 * pass
    let low := high - 1
    high = low + 1 ∧ high < logN ∧ low < logN := by
  dsimp only
  omega

/-- One complete packed pass agrees with its field-array block-loop semantics. -/
theorem Native.pass_packFields (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (pass : Nat) (a : Array KoalaBear.Fast.Field) (hp : pass < logN / 2)
    (htw : TwiddleSizes logN tw) (hs : a.size = 2 ^ logN)
    (hu : 4 * 2 ^ logN < USize.size) :
    let high := logN - 1 - 2 * pass
    let low := high - 1
    let q := 2 ^ low
    (List.range (2 ^ logN / (4 * q))).foldl (fun acc block ↦
      Native.inner16 ((tw.map packFields).getD high ByteArray.empty)
        ((tw.map packFields).getD low ByteArray.empty) q 0
        (block * (4 * q)) (block * (4 * q) + q)
        (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) acc)
      (packFields a) = packFields (fieldPass logN tw pass a) := by
  dsimp only
  rw [getD_map_packFields, getD_map_packFields]
  unfold fieldPass
  obtain ⟨hhl, hh, hl⟩ := pass_indices logN pass hp
  have hhigh := htw _ hh
  have hlow := htw _ hl
  apply Native.fold_inner16_packFields
  · simpa only [size_packFields, hs] using hu
  · rw [size_packFields, hhigh]
    have he : 2 ^ (logN - 1 - 2 * pass) ≤ 2 ^ logN :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · rw [size_packFields, hlow]
    have he : 2 ^ (logN - 1 - 2 * pass - 1) ≤ 2 ^ logN :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have he := congrArg (fun n : Nat ↦ (2 : Nat) ^ n) hhl
    have hp := Nat.pow_succ 2 (logN - 1 - 2 * pass - 1)
    omega
  · rw [hlow]
  · rw [hs]
    exact Nat.div_mul_le_self _ _

/-- Every paired pass preserves the working field array's length. -/
@[simp] theorem size_fieldPass (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (pass : Nat) (a : Array KoalaBear.Fast.Field) : (fieldPass logN tw pass a).size = a.size := by
  unfold fieldPass
  exact Plan.size_butterflyDIFRadix4Blocks _ _ _ _ _ _ _

/-- A prefix of complete paired passes transports through the packed representation. -/
theorem Native.passes_packFields (logN count : Nat)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (hc : count ≤ logN / 2) (htw : TwiddleSizes logN tw)
    (hs : a.size = 2 ^ logN) (hu : 4 * 2 ^ logN < USize.size) :
    (List.range count).foldl (fun acc pass ↦
      let high := logN - 1 - 2 * pass
      let low := high - 1
      let q := 2 ^ low
      (List.range (2 ^ logN / (4 * q))).foldl (fun b block ↦
        Native.inner16 ((tw.map packFields).getD high ByteArray.empty)
          ((tw.map packFields).getD low ByteArray.empty) q 0
          (block * (4 * q)) (block * (4 * q) + q)
          (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) b) acc)
      (packFields a) =
      packFields ((List.range count).foldl (fun b pass ↦ fieldPass logN tw pass b) a) := by
  apply foldl_packFields (List.range count) (fun b ↦ b.size = 2 ^ logN)
  · intro pass hp b hb
    exact Native.pass_packFields logN tw pass b (by
      have := List.mem_range.mp hp
      omega) htw hb hu
  · intro pass hp b hb
    simpa only [size_fieldPass] using hb
  · exact hs

end CompPoly.CPolynomial.NTTFast.Packed
