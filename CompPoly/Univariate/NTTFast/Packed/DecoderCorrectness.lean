/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Packed.DecoderGeometry

/-! # Complete tiled output decoder refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The native output decoder traverses its rows and low-bit tiles as two ordinary folds. -/
theorem Native.decodeTiled_eq_folds (logN : Nat) (b : ByteArray) (factor : UInt32)
    (inverse : Bool) :
    Native.decodeTiled logN b factor inverse =
      if logN < 6 then Native.decode logN b factor inverse else
        (List.range (2 ^ logN / 64)).foldl (fun out m ↦
          (List.range 16).foldl (fun out d ↦ rawDecoderTile logN b factor inverse m d out) out)
          (Array.replicate (2 ^ logN) (0 : KoalaBear.Fast.Field)) := by
  simp only [Native.decodeTiled, rawDecoderTile,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, ← apply_ite]

/-- Every tiled output conversion agrees with scalar bit-reversed indexing and normalization. -/
theorem Native.decodeTiled_packFields (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (h32 : logN ≤ 32)
    (hs : a.size = 2 ^ logN) (hu : (packFields a).size < USize.size) :
    Native.decodeTiled logN (packFields a) factor.val inverse = decodedFields logN a factor
      inverse := by
  rw [Native.decodeTiled_eq_folds]
  split
  · exact Native.decode_packFields logN a factor inverse h32 hs hu
  · rename_i hsmall
    have hlog : 6 ≤ logN := by omega
    let target := decodedFields logN a factor inverse
    let out := Array.replicate (2 ^ logN) (0 : KoalaBear.Fast.Field)
    have hinner (m : Nat) (hm : m < 2 ^ logN / 64)
        (b : Array KoalaBear.Fast.Field) (hb : b.size = 2 ^ logN) :
        (List.range 16).foldl (fun b d ↦ rawDecoderTile logN (packFields a) factor.val inverse m
          d b) b =
          (List.range 16).foldl (fun b d ↦
            scatterTile target (NTT.Transform.bitRevNat (logN - 2) (m * 16 + d)) b) b := by
      apply Plan.foldl_range_congr_inv (fun b : Array KoalaBear.Fast.Field ↦ b.size = 2 ^ logN)
      · intro d hd b hb
        exact rawDecoderTile_scatter logN a factor inverse m d b hlog h32 hm hd hs hb hu
      · intro d hd b hb
        rw [rawDecoderTile_scatter logN a factor inverse m d b hlog h32 hm hd hs hb hu,
          size_scatterTile, hb]
      · exact hb
    have houter :
        (List.range (2 ^ logN / 64)).foldl (fun b m ↦
          (List.range 16).foldl (fun b d ↦ rawDecoderTile logN (packFields a) factor.val inverse
            m d b) b) out =
          (List.range (2 ^ logN / 64)).foldl (fun b m ↦
            (List.range 16).foldl (fun b d ↦
              scatterTile target (NTT.Transform.bitRevNat (logN - 2) (m * 16 + d)) b) b) out := by
      apply Plan.foldl_range_congr_inv (fun b : Array KoalaBear.Fast.Field ↦ b.size = 2 ^ logN)
      · intro m hm b hb
        exact hinner m hm b hb
      · intro m hm b hb
        rw [hinner m hm b hb]
        exact foldl_invariant (List.range 16) (fun b : Array KoalaBear.Fast.Field ↦ b.size = 2 ^
          logN)
          _ (fun d hd c hc ↦ by simpa only [size_scatterTile] using hc) b hb
      · exact Array.size_replicate
    change (List.range (2 ^ logN / 64)).foldl (fun b m ↦
      (List.range 16).foldl (fun b d ↦ rawDecoderTile logN (packFields a) factor.val inverse m d
        b) b) out = target
    rw [houter]
    have hg := foldl_range_groups (fun b tile ↦
      scatterTile target (NTT.Transform.bitRevNat (logN - 2) tile) b) 16 (2 ^ logN / 64) out
    have hg' :
        (List.range (2 ^ logN / 64)).foldl (fun b m ↦
          (List.range 16).foldl (fun b d ↦
            scatterTile target (NTT.Transform.bitRevNat (logN - 2) (m * 16 + d)) b) b) out =
          (List.range (16 * (2 ^ logN / 64))).foldl (fun b tile ↦
            scatterTile target (NTT.Transform.bitRevNat (logN - 2) tile) b) out := by
      simpa only [Nat.mul_comm 16] using hg
    rw [hg']
    have hcount : 16 * (2 ^ logN / 64) = 2 ^ (logN - 2) := by
      rw [Nat.pow_div (x := 2) (m := logN) (n := 6) hlog (by decide)]
      have he : logN - 2 = (logN - 6) + 4 := by omega
      rw [he, Nat.pow_add]
      ring
    rw [hcount]
    apply fold_scatterTile_bitRev target out (logN - 2)
    · simp only [target, decodedFields, Array.size_ofFn]
      exact tiled_size logN (by omega)
    · simp only [out, target, Array.size_replicate, decodedFields, Array.size_ofFn]

end CompPoly.CPolynomial.NTTFast.Packed
