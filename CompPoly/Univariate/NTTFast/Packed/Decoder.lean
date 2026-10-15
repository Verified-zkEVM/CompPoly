/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.FieldStorage
import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Reverse32

/-! # Natural-order reads of a bit-reversed transform

`decodedFields` reads a bit-reversed array in natural order, optionally scaled; `Native.decode`
computes it from packed words, for leaves too small for the fused final layers.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open CompPoly.PackedRepr (encode)

/-- The natural-order read of a bit-reversed array, optionally scaled. -/
def decodedFields (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) : Array KoalaBear.Fast.Field :=
  Array.ofFn (fun i : Fin (2 ^ logN) ↦
    let x := a.getD (NTT.Transform.bitRevNat logN i.val) 0
    if inverse then factor * x else x)

/-- The thirty-two-bit index calculation agrees with bit reversal on every bounded transform
  index. -/
theorem Native.reverse_index (logN i : Nat) (hlog : logN ≤ 32) (hi : i < 2 ^ logN) :
    (reverse32 i.toUInt32 >>> (32 - logN).toUInt32).toNat =
      NTT.Transform.bitRevNat logN i := by
  by_cases hz : logN = 0
  · subst logN
    have he : i = 0 := by simp only [Nat.pow_zero] at hi; omega
    subst i
    decide
  · exact reverse32_shift_eq_bitRevNat logN i (by omega) hlog

/-- Ordinary packed output conversion computes exactly reversed indexing and optional scaling. -/
theorem Native.decode_encode (logN : Nat) (a : Array KoalaBear.Fast.Field)
    (factor : KoalaBear.Fast.Field) (inverse : Bool) (hlog : logN ≤ 32)
    (hs : a.size = 2 ^ logN) (hu : (encode a).size < USize.size) :
    Native.decode logN (encode a) factor.val inverse = decodedFields logN a factor inverse := by
  change tabulate (fun i : Fin (2 ^ logN) ↦
    ofWord (if inverse then mul factor.val
      (Native.read (encode a) (reverse32 i.val.toUInt32 >>> (32 - logN).toUInt32).toNat)
    else Native.read (encode a)
      (reverse32 i.val.toUInt32 >>> (32 - logN).toUInt32).toNat)) = _
  rw [tabulate_eq]
  unfold decodedFields
  apply congrArg Array.ofFn
  funext i
  rw [Native.reverse_index logN i.val hlog i.isLt,
    Native.read_encode a _ hu (by rw [hs]; exact NTT.Transform.bitRevNat_lt _ _)]
  cases inverse <;> simp only [Bool.false_eq_true, ite_false, ite_true, mul_val, ofWord_val]

end CompPoly.CPolynomial.NTTFast.Packed
