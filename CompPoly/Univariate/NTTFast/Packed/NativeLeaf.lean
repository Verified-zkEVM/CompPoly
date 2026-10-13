/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.KernelSpecialization
public import CompPoly.Univariate.NTTFast.Packed.KernelCorrectness

/-! # Mathematical specification of the packed fused leaf -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- The native final-layer kernel implements the four ordinary local DIF layers. -/
theorem Native.leaf16_correct (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize)
    (a : Array KoalaBear.Fast.Field) (h)
    (h3 : t3.getD 0 0 = 1) (h2 : t2.getD 0 0 = 1) (h1 : t1.getD 0 0 = 1) :
    Native.leaf16 (encode t3) (encode t2) (encode t1) i (encode a) h =
      encode (Expressions.leaf16Stages t3 t2 t1 a i.toNat) := by
  have hi : i.toNat + 16 ≤ a.size := by
    have hi := h.1
    rw [size_encode_fields] at hi
    omega
  rw [Native.leaf16_encode, leaf16Field_eq_expression,
    Expressions.leaf16Field_eq_stages t3 t2 t1 a i hi h3 h2 h1]

end CompPoly.CPolynomial.NTTFast.Packed
