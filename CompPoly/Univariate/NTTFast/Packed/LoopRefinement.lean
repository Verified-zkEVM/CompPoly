/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.BatchCorrectness
public import CompPoly.Univariate.NTTFast.Packed.KernelSpecialization

/-! # Packed scalar loop refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The packed scalar radix-four tail agrees with the ordinary field-array loop. -/
theorem Native.inner_packFields (th tl : Array KoalaBear.Fast.Field) (q j i0 i1 i2 i3 : Nat)
    (a : Array KoalaBear.Fast.Field)
    (ha : (packFields a).size < USize.size)
    (hth : (packFields th).size < USize.size) (htl : (packFields tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size)
    (hi : i0 + (q - j) ≤ a.size ∧ i1 + (q - j) ≤ a.size ∧
      i2 + (q - j) ≤ a.size ∧ i3 + (q - j) ≤ a.size) :
    Native.inner (packFields th) (packFields tl) q j i0 i1 i2 i3 (packFields a) =
      packFields (Plan.butterflyDIFRadix4Inner th tl q j i0 i1 i2 i3 a) := by
  rw [Native.inner, Plan.butterflyDIFRadix4Inner]
  split
  · rename_i hj
    simp (config := { maxDischargeDepth := 8 })
      (disch := (simp_all only [Array.size_setIfInBounds, size_packFields] <;> omega)) only
      [Native.read_packFields, add_val, sub_val, mul_val, Native.write_packFields]
    exact Native.inner_packFields th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) _
      (by simpa only [size_packFields, Array.size_setIfInBounds] using ha)
      hth htl hthi htli (by simp only [Array.size_setIfInBounds]; omega)
  · rfl
termination_by q - j
decreasing_by omega


/-- Batched dispatch and the scalar tail together execute the ordinary inner loop. -/
theorem Native.inner16_packFields (th tl : Array KoalaBear.Fast.Field) (q j i0 i1 i2 i3 : Nat)
    (a : Array KoalaBear.Fast.Field)
    (ha : (packFields a).size < USize.size)
    (hth : (packFields th).size < USize.size) (htl : (packFields tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size)
    (hs : i3 + (q - j) ≤ a.size) (h01 : i0 + (q - j) ≤ i1)
    (h12 : i1 + (q - j) ≤ i2) (h23 : i2 + (q - j) ≤ i3) :
    Native.inner16 (packFields th) (packFields tl) q j i0 i1 i2 i3 (packFields a) =
      packFields (Plan.butterflyDIFRadix4Inner th tl q j i0 i1 i2 i3 a) := by
  rw [Native.inner16]
  split
  · rename_i hj
    split
    · rename_i hg
      rw [Native.step16_packFields]
      rw [step16Field_eq_expression]
      rw [Expressions.step16Field_eq_quadCells th tl q _ _ _ _ _ _ a
        (by simp only [USize.toNat_ofNatLT])
        (by simp only [USize.toNat_ofNatLT]; omega)
        (by simp only [USize.toNat_ofNatLT]; omega)
        (by simp only [USize.toNat_ofNatLT]; omega)
        (by simp only [USize.toNat_ofNatLT]; omega)]
      simp only [USize.toNat_ofNatLT]
      rw [Native.inner16_packFields th tl q (j + 16) (i0 + 16) (i1 + 16) (i2 + 16) (i3 + 16) _
        (by simpa only [size_packFields, size_quadCells] using ha)
        hth htl hthi htli
        (by simp only [size_quadCells]; omega) (by omega) (by omega) (by omega)]
      rw [butterflyDIFRadix4Inner_eq_quadCells, butterflyDIFRadix4Inner_eq_quadCells,
        ← quadCells_add]
      have he : 16 + (q - (j + 16)) = q - j := by omega
      rw [he]
    · exact Native.inner_packFields th tl q j i0 i1 i2 i3 a ha hth htl hthi htli (by omega)
  · exact Native.inner_packFields th tl q j i0 i1 i2 i3 a ha hth htl hthi htli (by omega)
termination_by q - j
decreasing_by omega

end CompPoly.CPolynomial.NTTFast.Packed
