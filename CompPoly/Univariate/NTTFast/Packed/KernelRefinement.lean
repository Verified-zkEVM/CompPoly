/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
import all CompPoly.Univariate.NTTFast.Packed.KernelModels
public import CompPoly.Univariate.NTTFast.Packed.KernelModels

/-! # Refinement of packed arithmetic kernels to field-array kernels -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- The vectorizable word kernel is exactly sixteen field butterflies. -/
theorem Native.step16_encode (th tl : Array KoalaBear.Fast.Field)
    (j j1 i0 i1 i2 i3 : USize) (a : Array KoalaBear.Fast.Field) (h) :
    Native.step16 (encode th) (encode tl) j j1 i0 i1 i2 i3 (encode a) h =
      encode (step16Field th tl j j1 i0 i1 i2 i3 a) := by
  rcases h with ⟨hi0, hi1, hi2, hi3, hj1, hj, hjl, ha, hth, htl⟩
  have h0 : i0.toNat + 16 ≤ a.size := by rw [size_encode_fields] at hi0; omega
  have h1 : i1.toNat + 16 ≤ a.size := by rw [size_encode_fields] at hi1; omega
  have h2 : i2.toNat + 16 ≤ a.size := by rw [size_encode_fields] at hi2; omega
  have h3 : i3.toNat + 16 ≤ a.size := by rw [size_encode_fields] at hi3; omega
  rw [size_encode_fields] at ha
  unfold Native.step16
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  simp (config := { maxDischargeDepth := 8 })
    (disch := (simp_all (config := { maxDischargeDepth := 8 }) only
      [size_encode_fields, size_splice16])) only [Native.write16U_encode]
  rfl

/-- The fused final-layer word kernel agrees with its field expression graph. -/
theorem Native.leaf16_encode (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (a : Array KoalaBear.Fast.Field) (h) :
    Native.leaf16 (encode t3) (encode t2) (encode t1) i (encode a) h =
      encode (leaf16Field t3 t2 t1 i a) := by
  have hi : i.toNat + 16 ≤ a.size := by
    have hh := h.1
    rw [size_encode_fields] at hh
    omega
  unfold Native.leaf16
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  rw [Native.write16U_encode _ _ h.2.1 hi]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
