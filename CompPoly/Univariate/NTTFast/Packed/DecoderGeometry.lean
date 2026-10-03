/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.TiledDecoder
import Mathlib.Tactic.Ring

/-! # The native tiled decoder's arithmetic index calculation -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Splitting a tile index into its four low bits reproduces the native output-base calculation. -/
theorem tile_group_geometry (logN m d : Nat) (hlog : 6 ≤ logN) (hd : d < 16) :
    NTT.Transform.bitRevNat 4 d * 2 ^ (logN - 4) +
        NTT.Transform.bitRevNat (logN - 6) m * 4 =
      4 * NTT.Transform.bitRevNat (logN - 2) (m * 16 + d) := by
  have h := bitRevNat_concat (logN - 6) 4 m d hd
  have hbits : logN - 6 + 4 = logN - 2 := by omega
  rw [hbits] at h
  have hexp : logN - 4 = (logN - 6) + 2 := by omega
  rw [hexp, Nat.pow_add]
  simp only [Nat.reducePow, Nat.mul_comm 16] at h
  rw [h]
  ring

/-- The special zero-bit row reversal agrees with ordinary bit reversal as well. -/
theorem Native.decoder_reverse_m (logN m : Nat) (hlog : 6 ≤ logN) (h32 : logN ≤ 32) :
    (if logN == 6 then 0 else
      (Native.reverse32 m.toUInt32 >>> (32 - (logN - 6)).toUInt32).toNat) =
      NTT.Transform.bitRevNat (logN - 6) m := by
  split
  · rename_i he
    have he' : logN = 6 := by simpa only [beq_iff_eq] using he
    simp only [he', Nat.sub_self, NTT.Transform.bitRevNat]
  · rename_i he
    have he' : logN ≠ 6 := by simpa only [beq_iff_eq] using he
    exact Native.reverse32_shift_eq_bitRevNat (logN - 6) m (by omega) (by omega)

/-- The complete arithmetic body of one native decoder tile. -/
def rawDecoderTile (logN : Nat) (b : ByteArray) (factor : UInt32) (inverse : Bool)
    (m d : Nat) (out : Array KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  let n := 2 ^ logN
  let stride := (n / 4).toUSize
  let shift := (32 - (logN - 6)).toUInt32
  let revM := if logN == 6 then 0 else (Native.reverse32 m.toUInt32 >>> shift).toNat
  let outBase := (Native.reverse32 d.toUInt32 >>> (28 : UInt32)).toNat.toUSize *
    (n / 16).toUSize + (revM * 4).toUSize
  Native.decodeTile b (m * 16 + d).toUSize stride outBase factor inverse out

/-- The native index calculation scatters exactly the tile's natural-order group. -/
theorem rawDecoderTile_scatter (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (m d : Nat)
    (out : Array KoalaBear.Fast.Field) (hlog : 6 ≤ logN) (h32 : logN ≤ 32)
    (hm : m < 2 ^ logN / 64) (hd : d < 16)
    (hs : a.size = 2 ^ logN) (ho : out.size = 2 ^ logN)
    (hu : (packFields a).size < USize.size) :
    rawDecoderTile logN (packFields a) factor.val inverse m d out =
      scatterTile (decodedFields logN a factor inverse)
        (NTT.Transform.bitRevNat (logN - 2) (m * 16 + d)) out := by
  have hrevD : (Native.reverse32 d.toUInt32 >>> (28 : UInt32)).toNat =
      NTT.Transform.bitRevNat 4 d := by
    have h28 : UInt32.ofNat 28 = (28 : UInt32) := by decide
    simpa only [Nat.reduceSub, Nat.toUInt32_eq, h28] using
      Native.reverse_index 4 d (by decide) hd
  have hquarter : 2 ^ logN / 4 = 2 ^ (logN - 2) :=
    Nat.pow_div (x := 2) (m := logN) (n := 2) (by omega) (by decide)
  have hsixteen : 2 ^ logN / 16 = 2 ^ (logN - 4) :=
    Nat.pow_div (x := 2) (m := logN) (n := 4) (by omega) (by decide)
  have hrows : 2 ^ logN / 64 = 2 ^ (logN - 6) :=
    Nat.pow_div (x := 2) (m := logN) (n := 6) hlog (by decide)
  have hm' : m < 2 ^ (logN - 6) := by rw [← hrows]; exact hm
  have hexp : logN - 2 = (logN - 6) + 4 := by omega
  have htile : m * 16 + d < 2 ^ (logN - 2) := by
    rw [hexp, Nat.pow_add]
    norm_num
    omega
  dsimp only [rawDecoderTile]
  rw [Native.decoder_reverse_m logN m hlog h32, hrevD, hquarter, hsixteen]
  simp only [Nat.toUSize_eq, ← USize.ofNat_mul, ← USize.ofNat_add]
  rw [tile_group_geometry logN m d hlog hd]
  simpa only [Nat.toUSize_eq] using
    Native.decodeTile_scatter logN a factor inverse (m * 16 + d) out
      (by omega) htile hs ho hu

end CompPoly.CPolynomial.NTTFast.Packed
