/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.FieldStorage

/-! # Packed array construction and partition builders -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- Generators agree when their callbacks agree on the generated index range. -/
theorem Native.generate_congr (n : Nat) (f g : Nat → UInt32) (h : ∀ i < n, f i = g i) :
    Native.generate n f = Native.generate n g := by
  rw [Native.generate_eq, Native.generate_eq]
  apply congrArg encode
  apply congrArg Array.ofFn
  funext i
  exact h i.val i.isLt

/-- Generating canonical field words gives the packed field-array encoding. -/
theorem Native.generate_fields (n : Nat) (f : Nat → KoalaBear.Fast.Field) :
    Native.generate n (fun i ↦ (f i).val) =
      encode (Array.ofFn (fun i : Fin n ↦ f i.val)) := by
  rw [Native.generate_eq]
  simp only [encode_eq_map_val] at *
  rw [Array.map_ofFn]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
