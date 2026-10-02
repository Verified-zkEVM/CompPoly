/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.DecoderTile
public import CompPoly.Univariate.NTTFast.Packed.TiledIndices
public import CompPoly.Univariate.NTTFast.Packed.Scatter

/-! # Tiled output conversion refines natural-order decoding -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- A tile writes exactly the final natural-order values in its reversed four-coordinate group. -/
theorem Native.decodeTile_scatter (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (tile : Nat)
    (out : Array KoalaBear.Fast.Field) (hlog : 2 ≤ logN) (ht : tile < 2 ^ (logN - 2))
    (hs : a.size = 2 ^ logN) (ho : out.size = 2 ^ logN)
    (hu : (packFields a).size < USize.size) :
    Native.decodeTile (packFields a) tile.toUSize (2 ^ (logN - 2)).toUSize
      (4 * NTT.Transform.bitRevNat (logN - 2) tile).toUSize factor.val inverse out =
      scatterTile (decodedFields logN a factor inverse)
        (NTT.Transform.bitRevNat (logN - 2) tile) out := by
  have hn := tiled_size logN hlog
  have hgroup := scattered_group_bound logN tile hlog
  have huN : 2 ^ logN < USize.size := by rw [size_packFields, hs] at hu; omega
  have htileU : tile < USize.size := by omega
  have hstrideU : 2 ^ (logN - 2) < USize.size := by omega
  have hbaseU : 4 * NTT.Transform.bitRevNat (logN - 2) tile < USize.size := by omega
  have htc : tile.toUSize.toNat = tile := USize.toNat_ofNat_of_lt' htileU
  have hsc : (2 ^ (logN - 2)).toUSize.toNat = 2 ^ (logN - 2) :=
    USize.toNat_ofNat_of_lt' hstrideU
  have hbc : (4 * NTT.Transform.bitRevNat (logN - 2) tile).toUSize.toNat =
      4 * NTT.Transform.bitRevNat (logN - 2) tile := USize.toNat_ofNat_of_lt' hbaseU
  rw [Native.decodeTile_spec _ _ _ _ _ _ _ hu
    (by rw [htc, hsc, hs]; omega) (by omega) (by rw [hbc, ho]; exact hgroup)]
  simp only [htc, hsc, hbc]
  have h0 := getD_decodedFields_lane logN a factor inverse tile 0 hlog ht (by decide)
  have h1 := getD_decodedFields_lane logN a factor inverse tile 2 hlog ht (by decide)
  have h2 := getD_decodedFields_lane logN a factor inverse tile 1 hlog ht (by decide)
  have h3 := getD_decodedFields_lane logN a factor inverse tile 3 hlog ht (by decide)
  have hb0 : NTT.Transform.bitRevNat 2 0 = 0 := by decide
  have hb1 : NTT.Transform.bitRevNat 2 2 = 1 := by decide
  have hb2 : NTT.Transform.bitRevNat 2 1 = 2 := by decide
  have hb3 : NTT.Transform.bitRevNat 2 3 = 3 := by decide
  simp only [hb0, Nat.zero_mul, Nat.add_zero] at h0
  simp only [hb1] at h1
  simp only [hb2, Nat.one_mul] at h2
  simp only [hb3] at h3
  unfold scatterTile laneValue
  rw [h0, h1, h2, h3]

end CompPoly.CPolynomial.NTTFast.Packed
