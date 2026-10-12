/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.NativeLastCorrectness

/-! # Proved parallel KoalaBear transforms with packed native storage

The correctness theorems cover the complete Lean pipeline. Packed words are read and written
with the `ByteArray` word accessors proposed for Lean core (`CompPoly.Data.ByteArray.Pack`),
whose inline C remains a runtime trust assumption; arithmetic, tasks and ordering are Lean.
`forwardPacked`/`inversePacked` take and return packed Montgomery words: `encode` packs a field
array and `decode` reads one back.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- A reusable packed transform plan with certified cached twiddles and index bounds. -/
structure Plan where
  domain : NTT.Domain KoalaBear.Fast.Field
  log_bound : domain.logN ≤ 32
  byte_bound : 4 * domain.n < USize.size
  nInv : KoalaBear.Fast.Field
  nInv_eq : nInv = domain.nInv
  forwardTwiddles : Array ByteArray
  inverseTwiddles : Array ByteArray
  forward_eq : forwardTwiddles = (NTTFast.Plan.twiddleTable domain).map encode
  inverse_eq : inverseTwiddles = (NTTFast.Plan.twiddleTable domain.inverse).map encode

namespace Plan

/-- Encode both twiddle tables once; no plan construction is needed inside hot loops. -/
def ofDomain (D : NTT.Domain KoalaBear.Fast.Field) (h32 : D.logN ≤ 32)
    (hu : 4 * D.n < USize.size) : Plan where
  domain := D
  log_bound := h32
  byte_bound := hu
  nInv := D.nInv
  nInv_eq := rfl
  forwardTwiddles := (NTTFast.Plan.twiddleTable D).map Native.encodeFields
  inverseTwiddles := (NTTFast.Plan.twiddleTable D.inverse).map Native.encodeFields
  forward_eq := by
    apply congrArg (Array.map · _)
    funext a
    exact Native.encodeFields_eq a
  inverse_eq := by
    apply congrArg (Array.map · _)
    funext a
    exact Native.encodeFields_eq a

/-- Default parallel split depth: serial up to `2 ^ 12` elements, four leaves up to
`2 ^ 14`, sixteen leaves above. Smaller trees avoid task overhead on small inputs. -/
def defaultDepth (logN : Nat) : Nat :=
  if logN ≤ 12 then 0 else if logN ≤ 14 then 2 else 4

/-- Natural-order forward transform of `n` packed Montgomery words. -/
@[inline] def forwardPacked (P : Plan) (a : ByteArray)
    (depth : Nat := defaultDepth P.domain.logN) : ByteArray :=
  Native.runPacked P.forwardTwiddles P.domain.logN depth P.nInv.val a false

/-- Natural-order inverse transform of `n` packed Montgomery words, including normalization. -/
@[inline] def inversePacked (P : Plan) (a : ByteArray)
    (depth : Nat := defaultDepth P.domain.logN) : ByteArray :=
  Native.runPacked P.inverseTwiddles P.domain.logN depth P.nInv.val a true

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

private theorem inverse_logN [Field R] (D : NTT.Domain R) :
    D.inverse.logN = D.logN := rfl

private theorem inverse_n [Field R] (D : NTT.Domain R) : D.inverse.n = D.n :=
  congrArg (fun logN ↦ 2 ^ logN) (inverse_logN D)

/-- The packed forward transform equals the mathematical DFT of every domain-sized input. -/
theorem forwardPacked_correct (P : Plan) (a : Array KoalaBear.Fast.Field) (depth : Nat)
    (hs : a.size = P.domain.n) :
    P.forwardPacked (encode a) depth = encode (NTT.Forward.forwardSpec P.domain a) := by
  rw [forwardPacked, P.forward_eq, P.nInv_eq]
  exact Native.runPacked_dft P.domain _ depth P.domain.nInv a false (fun _ _ ↦ rfl) hs
    P.log_bound P.byte_bound

/-- The packed inverse transform equals the normalized inverse DFT of every domain-sized input. -/
theorem inversePacked_correct (P : Plan) (a : Array KoalaBear.Fast.Field) (depth : Nat)
    (hs : a.size = P.domain.n) :
    P.inversePacked (encode a) depth = encode (NTT.Inverse.inverseSpec P.domain a) := by
  rw [inversePacked, P.inverse_eq, P.nInv_eq]
  have h := Native.runPacked_dft P.domain.inverse _ depth P.domain.nInv a true (fun _ _ ↦ rfl)
    (hs.trans (inverse_n P.domain).symm) ((inverse_logN P.domain).symm ▸ P.log_bound)
    ((inverse_n P.domain).symm ▸ P.byte_bound)
  rw [inverse_logN] at h
  rw [h, ite_eq_left rfl, normalized_inverse]

end Plan
end CompPoly.CPolynomial.NTTFast.Packed
