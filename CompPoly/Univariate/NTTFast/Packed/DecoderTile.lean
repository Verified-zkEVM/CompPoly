/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.DecoderStores

/-! # Scalar field semantics of a tiled decoder read and store -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- A lane read retains its natural-number index when the entire lane is in bounds. -/
theorem Native.readWord_at (a : Array KoalaBear.Fast.Field) (base lane stride : USize)
    (ha : (packFields a).size < USize.size)
    (hi : base.toNat + lane.toNat * stride.toNat < a.size) :
    Native.readWord (packFields a) (base + lane * stride) =
      (a.getD (base.toNat + lane.toNat * stride.toNat) 0).val := by
  have hin : base.toNat + lane.toNat * stride.toNat < USize.size := by
    rw [size_packFields] at ha
    omega
  have hm : (lane * stride).toNat = lane.toNat * stride.toNat := by
    have h := USize.toNat_mul lane stride
    change (lane * stride).toNat = (lane.toNat * stride.toNat) % USize.size at h
    rw [Nat.mod_eq_of_lt (by omega)] at h
    exact h
  have hs : (base + lane * stride).toNat = base.toNat + lane.toNat * stride.toNat := by
    have h := USize.toNat_add base (lane * stride)
    change (base + lane * stride).toNat = (base.toNat + (lane * stride).toNat) % USize.size at h
    rw [hm, Nat.mod_eq_of_lt hin] at h
    exact h
  rw [Native.readWord_eq_read, hs, Native.read_packFields _ _ ha hi]

/-- One decoded input lane, including optional inverse normalization. -/
def laneValue (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field)
    (inverse : Bool) (i : Nat) : KoalaBear.Fast.Field :=
  if inverse then factor * a.getD i 0 else a.getD i 0

/-- A decoder tile reads input lanes in two-bit reversed order and writes four scalar field
  values. -/
theorem Native.decodeTile_spec (a : Array KoalaBear.Fast.Field) (base stride outBase : USize)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (out : Array KoalaBear.Fast.Field)
    (ha : (packFields a).size < USize.size) (hi : base.toNat + 3 * stride.toNat < a.size)
    (ho : out.size < USize.size) (hob : outBase.toNat + 4 ≤ out.size) :
    Native.decodeTile (packFields a) base stride outBase factor.val inverse out =
      storeList out outBase.toNat
        [laneValue a factor inverse base.toNat,
          laneValue a factor inverse (base.toNat + 2 * stride.toNat),
          laneValue a factor inverse (base.toNat + stride.toNat),
          laneValue a factor inverse (base.toNat + 3 * stride.toNat)] := by
  cases inverse <;>
    simp (disch := (first | (simp -failIfUnchanged only
      [Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
        Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide),
        Nat.zero_mul, Nat.one_mul] <;> omega) | fail)) only
      [Native.decodeTile, Native.readWord_at, Native.fieldOfRaw, mul_val, ofWord_val,
        Bool.false_eq_true, ite_true, ite_false, Native.setField4_eq_storeList,
        laneValue, Native.usize_numeral 0 (by decide), Native.usize_numeral 1 (by decide),
        Native.usize_numeral 2 (by decide), Native.usize_numeral 3 (by decide),
        Nat.zero_mul, Nat.one_mul, Nat.add_zero]

end CompPoly.CPolynomial.NTTFast.Packed
