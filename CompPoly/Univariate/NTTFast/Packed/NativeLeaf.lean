/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.KernelSpecialization
public import CompPoly.Univariate.NTTFast.Packed.LeafScaling

/-! # Mathematical specification of the packed fused leaf -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The native final-layer kernel implements the four ordinary local DIF layers. -/
theorem Native.leaf16_correct (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (a : Array KoalaBear.Fast.Field) (h)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.leaf16 (packFields t3) (packFields t2) (packFields t1) i (packFields a) h =
      packFields (Expressions.leaf16Stages t3 t2 t1 a i.toNat) := by
  have hi : i.toNat + 16 ≤ a.size := by
    have hi := h.1
    rw [size_packFields] at hi
    omega
  rw [Native.leaf16_packFields, leaf16Field_eq_expression,
    Expressions.leaf16Field_eq_stages t3 t2 t1 a i hi h3 h2 h1]

/-- The inverse leaf is the same four DIF layers followed by local normalization. -/
theorem Native.leaf16Scaled_correct (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (factor : KoalaBear.Fast.Field) (a : Array KoalaBear.Fast.Field) (h)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.leaf16Scaled (packFields t3) (packFields t2) (packFields t1) i factor.val
      (packFields a) h =
      packFields (scaleSegment (Expressions.leaf16Stages t3 t2 t1 a i.toNat)
        i.toNat 16 factor) := by
  have hi : i.toNat + 16 ≤ a.size := by
    have hi := h.1
    rw [size_packFields] at hi
    omega
  rw [Native.leaf16Scaled_packFields, leaf16ScaledField_eq_expression,
    Expressions.leaf16ScaledField_eq_scaleSegment _ _ _ _ _ _ hi,
    Expressions.leaf16Field_eq_stages _ _ _ _ _ hi h3 h2 h1]

end CompPoly.CPolynomial.NTTFast.Packed
