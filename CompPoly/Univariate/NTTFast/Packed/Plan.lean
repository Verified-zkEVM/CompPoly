/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Correctness

/-! # Proved parallel KoalaBear transforms with packed native storage

The correctness theorems cover the complete Lean pipeline. The two storage externs
in `Native` remain runtime trust assumptions; arithmetic, tasks and ordering are Lean.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- A reusable packed transform plan with certified cached twiddles and index bounds. -/
structure Plan where
  domain : NTT.Domain KoalaBear.Fast.Field
  log_bound : domain.logN ≤ 32
  byte_bound : 4 * domain.n < USize.size
  nInv : KoalaBear.Fast.Field
  nInv_eq : nInv = domain.nInv
  forwardTwiddles : Array ByteArray
  inverseTwiddles : Array ByteArray
  forward_eq : forwardTwiddles = (NTTFast.Plan.twiddleTable domain).map packFields
  inverse_eq : inverseTwiddles = (NTTFast.Plan.twiddleTable domain.inverse).map packFields

namespace Plan

/-- Encode both twiddle tables once; no plan construction is needed inside hot loops. -/
def ofDomain (D : NTT.Domain KoalaBear.Fast.Field) (h32 : D.logN ≤ 32)
    (hu : 4 * D.n < USize.size) : Plan where
  domain := D
  log_bound := h32
  byte_bound := hu
  nInv := D.nInv
  nInv_eq := rfl
  forwardTwiddles := (NTTFast.Plan.twiddleTable D).map Native.encode
  inverseTwiddles := (NTTFast.Plan.twiddleTable D.inverse).map Native.encode
  forward_eq := by
    apply congrArg (Array.map · _)
    funext a
    exact Native.encode_eq a
  inverse_eq := by
    apply congrArg (Array.map · _)
    funext a
    exact Native.encode_eq a

/-- Reuse a domain-sized input, otherwise zero-pad or truncate it. -/
@[inline] def load (P : Plan) (a : Array KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  if a.size = P.domain.n then a
  else NTTFast.tabulate (fun i : P.domain.Idx ↦ a.getD i.val 0)

/-- Loading preserves the ordinary total array semantics. -/
theorem load_eq (P : Plan) (a : Array KoalaBear.Fast.Field) :
    P.load a = NTT.loadNaturalArray P.domain a := by
  unfold load
  split
  · exact (loadNaturalArray_eq_self P.domain a ‹_›).symm
  · exact NTTFast.tabulate_eq _

/-- Complete natural-order forward transform; `depth` bounds the parallel split tree. -/
@[inline] def forward (P : Plan) (a : Array KoalaBear.Fast.Field) (depth : Nat := 4) :
    Array KoalaBear.Fast.Field :=
  Native.run P.forwardTwiddles P.domain.logN depth P.nInv.val (P.load a) false

/-- Complete natural-order inverse, including normalization inside workers when possible. -/
@[inline] def inverse (P : Plan) (a : Array KoalaBear.Fast.Field) (depth : Nat := 4) :
    Array KoalaBear.Fast.Field :=
  Native.run P.inverseTwiddles P.domain.logN depth P.nInv.val (P.load a) true

private theorem forwardSpec_load [Field R] (D : NTT.Domain R) (a : Array R) :
    NTT.Forward.forwardSpec D (NTT.loadNaturalArray D a) = NTT.Forward.forwardSpec D a := by
  unfold NTT.Forward.forwardSpec NTT.Forward.nttAt
  congr 1
  funext k
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem
    (by simpa only [NTT.size_loadNaturalArray] using j.isLt), Option.getD_some,
    NTT.getElem_loadNaturalArray]

private theorem normalized_inverse [Field R] (D : NTT.Domain R) (a : Array R) :
    (NTT.Forward.forwardSpec D.inverse a).map (fun x ↦ D.nInv * x) =
      NTT.Inverse.inverseSpec D a := by
  have h : (NTT.Forward.forwardSpec D.inverse a).map (fun x ↦ D.nInv * x) =
      NTT.Inverse.normalize D (NTT.Forward.forwardSpec D.inverse a) := by
    simp only [NTT.Forward.forwardSpec, Array.map_ofFn, NTT.Inverse.normalize,
      Function.comp_def]
    apply congrArg Array.ofFn
    funext i
    rw [getD_ofFn_bounded _ _ i.isLt]
  rw [h, NTT.Inverse.normalize_forwardSpec_inverse_eq_inverseSpec]

private theorem inverseSpec_load [Field R] (D : NTT.Domain R) (a : Array R) :
    NTT.Inverse.inverseSpec D (NTT.loadNaturalArray D a) = NTT.Inverse.inverseSpec D a := by
  rw [← normalized_inverse, ← normalized_inverse D a]
  change (NTT.Forward.forwardSpec D.inverse (NTT.loadNaturalArray D.inverse a)).map _ = _
  rw [forwardSpec_load]

private theorem inverse_logN [Field R] (D : NTT.Domain R) :
    D.inverse.logN = D.logN := rfl

private theorem inverse_n [Field R] (D : NTT.Domain R) : D.inverse.n = D.n :=
  congrArg (fun logN ↦ 2 ^ logN) (inverse_logN D)

private theorem run_inverse (D : NTT.Domain KoalaBear.Fast.Field)
    (tw : Array (Array KoalaBear.Fast.Field)) (depth : Nat) (a : Array KoalaBear.Fast.Field)
    (ht : TwiddlesFor D.inverse tw) (hs : a.size = D.n)
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) :
    Native.run (tw.map packFields) D.logN depth D.nInv.val a true =
      NTT.Inverse.inverseSpec D a := by
  have h := Native.run_dft D.inverse tw depth D.nInv a true ht
    (hs.trans (inverse_n D).symm) ((inverse_logN D).symm ▸ h32) ((inverse_n D).symm ▸ hu)
  rw [inverse_logN] at h
  exact h.trans (normalized_inverse D a)

/-- The whole packed parallel forward transform equals the mathematical DFT for any input. -/
theorem forward_correct (P : Plan) (a : Array KoalaBear.Fast.Field) (depth : Nat) :
    P.forward a depth = NTT.Forward.forwardSpec P.domain a := by
  rw [forward, P.forward_eq, P.nInv_eq, load_eq,
    Native.run_dft P.domain _ depth P.domain.nInv _ false (fun _ _ ↦ rfl)
      (NTT.size_loadNaturalArray ..) P.log_bound P.byte_bound]
  exact forwardSpec_load P.domain a

/-- The whole packed parallel inverse transform equals the normalized inverse DFT. -/
theorem inverse_correct (P : Plan) (a : Array KoalaBear.Fast.Field) (depth : Nat) :
    P.inverse a depth = NTT.Inverse.inverseSpec P.domain a := by
  rw [inverse, P.inverse_eq, P.nInv_eq, load_eq]
  exact (run_inverse P.domain _ depth _ (fun _ _ ↦ rfl) (NTT.size_loadNaturalArray ..)
    P.log_bound P.byte_bound).trans (inverseSpec_load P.domain a)

end Plan
end CompPoly.CPolynomial.NTTFast.Packed
