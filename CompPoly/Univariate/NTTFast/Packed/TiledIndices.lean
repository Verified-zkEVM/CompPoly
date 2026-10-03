/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.TiledPermutation
public import CompPoly.Univariate.NTTFast.Packed.Decoder
import Mathlib.Tactic.Ring

/-! # Bounds and coordinate identities of tiled decoding -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The transform is four times its decoder's tile count. -/
theorem tiled_size (logN : Nat) (hlog : 2 ≤ logN) :
    2 ^ logN = 4 * 2 ^ (logN - 2) := by
  have he : logN = 2 + (logN - 2) := by omega
  conv_lhs => rw [he, Nat.pow_add]

/-- The complete reversed output index decomposes into a reversed tile and two reversed lane
  bits. -/
theorem bitRevNat_tile_lane (logN tile lane : Nat) (hlog : 2 ≤ logN)
    (ht : tile < 2 ^ (logN - 2)) :
    NTT.Transform.bitRevNat logN (tile + lane * 2 ^ (logN - 2)) =
      4 * NTT.Transform.bitRevNat (logN - 2) tile + NTT.Transform.bitRevNat 2 lane := by
  have he : logN = 2 + (logN - 2) := by omega
  have hinput : tile + lane * 2 ^ (logN - 2) = 2 ^ (logN - 2) * lane + tile := by ring
  conv_lhs =>
    rw [hinput]
    arg 1
    rw [he]
  exact bitRevNat_concat 2 (logN - 2) lane tile ht

/-- Each input lane is recovered by reversing its scattered output coordinate. -/
theorem bitRevNat_scattered_lane (logN tile lane : Nat) (hlog : 2 ≤ logN)
    (ht : tile < 2 ^ (logN - 2)) (hl : lane < 4) :
    NTT.Transform.bitRevNat logN
      (4 * NTT.Transform.bitRevNat (logN - 2) tile + NTT.Transform.bitRevNat 2 lane) =
      tile + lane * 2 ^ (logN - 2) := by
  have hs := tiled_size logN hlog
  have hi : tile + lane * 2 ^ (logN - 2) < 2 ^ logN := by
    rw [hs]
    nlinarith
  have h := congrArg (NTT.Transform.bitRevNat logN) (bitRevNat_tile_lane logN tile lane hlog ht)
  rw [NTT.Transform.bitRevNat_involutive logN _ hi] at h
  exact h.symm

/-- A scattered group of four coordinates is wholly inside the transform output. -/
theorem scattered_group_bound (logN tile : Nat) (hlog : 2 ≤ logN) :
    4 * NTT.Transform.bitRevNat (logN - 2) tile + 4 ≤ 2 ^ logN := by
  have hb := NTT.Transform.bitRevNat_lt (logN - 2) tile
  rw [tiled_size logN hlog]
  omega

/-- Reading the decoder's mathematical array is reversed indexing with optional normalization. -/
theorem getD_decodedFields (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (k : Nat) (hk : k < 2 ^ logN) :
    (decodedFields logN a factor inverse).getD k 0 =
      if inverse then factor * a.getD (NTT.Transform.bitRevNat logN k) 0
      else a.getD (NTT.Transform.bitRevNat logN k) 0 := by
  unfold decodedFields
  rw [getD_ofFn_bounded _ k hk 0]

/-- The final decoder coordinate in one scattered group reads its original packed input lane. -/
theorem getD_decodedFields_lane (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (tile lane : Nat)
    (hlog : 2 ≤ logN) (ht : tile < 2 ^ (logN - 2)) (hl : lane < 4) :
    (decodedFields logN a factor inverse).getD
      (4 * NTT.Transform.bitRevNat (logN - 2) tile + NTT.Transform.bitRevNat 2 lane) 0 =
      if inverse then factor * a.getD (tile + lane * 2 ^ (logN - 2)) 0
      else a.getD (tile + lane * 2 ^ (logN - 2)) 0 := by
  have hb := scattered_group_bound logN tile hlog
  have hr := NTT.Transform.bitRevNat_lt 2 lane
  rw [getD_decodedFields _ _ _ _ _ (by omega), bitRevNat_scattered_lane _ _ _ hlog ht hl]

end CompPoly.CPolynomial.NTTFast.Packed
