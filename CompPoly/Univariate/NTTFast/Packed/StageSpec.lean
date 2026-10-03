/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.RecursiveOrdering

/-! # Sequential packed transforms refine the mathematical DFT -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- An already domain-sized array is unchanged by zero-padding. -/
theorem loadNaturalArray_eq_self [Field R] (D : NTT.Domain R) (a : Array R)
    (hs : a.size = D.n) : NTT.loadNaturalArray D a = a := by
  apply Array.ext (by rw [NTT.size_loadNaturalArray, hs])
  intro i hi hj
  rw [NTT.getElem_loadNaturalArray]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]

/-- The ordinary radix-four pipeline computes the mathematical bit-reversed DFT. -/
theorem planStages_eq_difSpec [Field R] (D : NTT.Domain R) (a : Array R) (hs : a.size = D.n) :
    Plan.runStagesDIFRadix4WithTwiddles D (Plan.twiddleTable D) a = difSpec D a := by
  have h := Plan.runStagesDIFRadix4WithTwiddles_correct D a
  rw [loadNaturalArray_eq_self D a hs] at h
  exact h

/-- The sequential packed arithmetic agrees with the DFT, including optional normalization. -/
theorem Native.stages_difSpec (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (normalize : Bool)
    (ht : TwiddlesFor D tw) (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hn : ValidNormalization D.logN normalize) :
    Native.stages D.logN (tw.map packFields) (packFields a) factor.val normalize =
      packFields (if normalize then (difSpec D a).map (fun x ↦ factor * x) else difSpec D a) := by
  rw [Native.stages_correct_for D tw a factor normalize ht hs hu hn,
    planStages_eq_difSpec D a hs]

end CompPoly.CPolynomial.NTTFast.Packed
