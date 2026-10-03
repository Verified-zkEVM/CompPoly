/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.DecoderCorrectness

/-! # Complete packed parallel FFT correctness -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Mathematical task output shape is preserved with or without normalization. -/
@[simp] theorem size_normalizedDifSpec [Field R] (D : NTT.Domain R) (a : Array R)
    (factor : R) (normalize : Bool) : (normalizedDifSpec D a factor normalize).size = D.n := by
  cases normalize <;> simp only [normalizedDifSpec, Bool.false_eq_true, ite_true, ite_false,
    Array.size_map, size_difSpec]

/-- Decoding an unnormalized DIF result restores natural-order DFT evaluations. -/
theorem decodedFields_difSpec (D : NTT.Domain KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field) (inverse : Bool) :
    decodedFields D.logN (difSpec D a) factor inverse =
      if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
      else NTT.Forward.forwardSpec D a := by
  cases inverse <;>
    simp only [decodedFields, Bool.false_eq_true, ite_false, ite_true,
      NTT.Forward.forwardSpec, Array.map_ofFn]
  all_goals
    apply congrArg Array.ofFn
    funext i
    rw [getD_difSpec D a _ (NTT.Transform.bitRevNat_lt _ _),
      NTT.Transform.bitRevNat_involutive D.logN i.val i.isLt, dftValue_eq_nttAt D a i] <;> rfl

/-- Normalization commutes with ordinary natural-order decoding. -/
theorem decodedFields_scaleMap (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) :
    decodedFields logN (a.map (fun x ↦ factor * x)) factor false =
      (decodedFields logN a factor false).map (fun x ↦ factor * x) := by
  simp only [decodedFields, Bool.false_eq_true, ite_false, Array.map_ofFn]
  apply congrArg Array.ofFn
  funext i
  exact getD_scaleMap a factor _

/-- Normalization is applied exactly once, either inside task leaves or inside the decoder. -/
theorem decodedFields_normalizedDifSpec (D : NTT.Domain KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field)
    (normalize inverse : Bool) (hn : normalize = true → inverse = true) :
    decodedFields D.logN (normalizedDifSpec D a factor normalize) factor (inverse && !normalize) =
      if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
      else NTT.Forward.forwardSpec D a := by
  cases normalize with
  | false =>
    simp only [normalizedDifSpec, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.and_true]
    exact decodedFields_difSpec D a factor inverse
  | true =>
    rw [hn rfl]
    simp only [normalizedDifSpec, ite_true, Bool.not_true, Bool.true_and]
    rw [decodedFields_scaleMap, decodedFields_difSpec]
    rfl

/-- The complete native-storage pipeline computes the DFT with optional inverse normalization. -/
theorem Native.run_dft (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field))
    (depth : Nat) (factor : KoalaBear.Fast.Field) (a : Array KoalaBear.Fast.Field)
    (inverse : Bool) (ht : TwiddlesFor D tw) (hs : a.size = D.n)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    Native.run (tw.map packFields) D.logN depth factor.val a inverse =
      if inverse then (NTT.Forward.forwardSpec D a).map (fun x ↦ factor * x)
      else NTT.Forward.forwardSpec D a := by
  let normalize := inverse && D.logN - depth ≥ 4 && (D.logN - depth) % 2 == 0
  have hn : ValidLeafNormalization D.logN depth normalize := by
    intro h
    simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨h.1.2, h.2⟩
  have hi : normalize = true → inverse = true := by
    intro h
    simp only [normalize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.1.1
  rw [Native.run_eq_before_collection]
  change Native.decodeTiled D.logN
    (Native.splitInputTask (tw.map packFields) D.logN a factor.val normalize depth).get
      factor.val (inverse && !normalize) = _
  rw [Native.splitInputTask_correct D tw a factor normalize depth ht hs hu hn]
  rw [Native.decodeTiled_packFields D.logN _ factor _ h32
    (size_normalizedDifSpec D a factor normalize)
    (by simpa only [size_packFields, size_normalizedDifSpec] using hu)]
  exact decodedFields_normalizedDifSpec D a factor normalize inverse hi

end CompPoly.CPolynomial.NTTFast.Packed
