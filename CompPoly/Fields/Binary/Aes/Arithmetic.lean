/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Extension.Arithmetic
public import Mathlib.Data.ZMod.Basic

/-!
# AES polynomial-basis coordinates and arithmetic

`AesField` reuses the nominal monic-extension carrier with coefficients in `ZMod 2` and
modulus `X^8 + X^4 + X^3 + X + 1`. Its explicit byte maps identify bit `i` with the
coefficient of `X^i`, including the constant term at bit zero. Arithmetic uses the existing
extension implementation; no raw-word coercion or separate byte multiplication is installed.

This module contains executable operations and coordinate proofs. Irreducibility, certified
field laws and quotient correspondence are supplied by `Aes.Basic`.

## References

* NIST, *Advanced Encryption Standard (AES)*, FIPS 197, updated May 9, 2023, Sections 3.2
  and 4. https://doi.org/10.6028/NIST.FIPS.197-upd1
-/

@[expose] public section

open CompPoly.Extension

namespace AesField

/-- Degree-eight parameters with lower coefficients of `X^4 + X^3 + X + 1` over `GF(2)`. -/
def params : ExtensionParams (ZMod 2) where
  d := 8
  two_le := by decide
  lower := #v[1, 1, 0, 1, 1, 0, 0, 0]
  q := 2

end AesField

/-- The AES polynomial presentation, with eight coefficients in ascending degree order. -/
abbrev AesField : Type := Ext AesField.params

namespace AesField

/-- Interpret the bits of a byte as polynomial coefficients, least significant bit first. -/
def ofBitVec (a : BitVec 8) : AesField := Ext.ofFn fun i => if a.getLsbD i then 1 else 0

/-- Recover the byte whose bit `i` is the coefficient of `X^i`. -/
def toBitVec (a : AesField) : BitVec 8 :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 8 => decide (Ext.coeff a i = 1))).cast
    List.length_ofFn

/-- The coefficient at index `i` is the corresponding input bit, valued in `GF(2)`. -/
@[simp] theorem coeff_ofBitVec (a : BitVec 8) (i : Fin 8) :
    Ext.coeff (ofBitVec a) i = if a.getLsbD i then 1 else 0 := Ext.coeff_ofFn _ _

/-- Decoding tests each coefficient against one in `GF(2)`. -/
@[simp] theorem getLsbD_toBitVec (a : AesField) (i : Fin 8) :
    (toBitVec a).getLsbD i = decide (Ext.coeff a i = 1) := by
  simp only [toBitVec, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dif_pos, Option.getD_some]

/-- Decoding an encoded byte recovers every input bit. -/
@[simp] theorem toBitVec_ofBitVec (a : BitVec 8) : toBitVec (ofBitVec a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_toBitVec _ ⟨i, hi⟩, coeff_ofBitVec]
  cases a.getLsbD i <;> decide

/-- Encoding the decoded byte recovers every coefficient. -/
@[simp] theorem ofBitVec_toBitVec (a : AesField) : ofBitVec (toBitVec a) = a := by
  apply Ext.ext
  intro i
  rw [coeff_ofBitVec (toBitVec a) i, getLsbD_toBitVec a i]
  generalize Ext.coeff a i = c
  fin_cases c <;> rfl

/-- The coordinate equivalence between AES elements and bytes. -/
def equivBitVec : AesField ≃ BitVec 8 where
  toFun := toBitVec
  invFun := ofBitVec
  left_inv := ofBitVec_toBitVec
  right_inv := toBitVec_ofBitVec

/-- Equal byte encodings identify equal field elements. -/
theorem toBitVec_injective : Function.Injective toBitVec := equivBitVec.injective

/-- The polynomial generator with coefficient one at `X` and zero elsewhere. -/
def gen : AesField := Ext.gen

/-- The polynomial generator is the explicit coordinate byte two. -/
theorem gen_eq_ofBitVec : gen = ofBitVec (2#8) := by
  apply Ext.ext
  intro i
  rw [gen, Ext.coeff_gen, coeff_ofBitVec (2#8) i]
  change (if (i : ℕ) = 1 then (1 : ZMod 2) else 0) =
    if (BitVec.twoPow 8 1).getLsbD i then 1 else 0
  simp only [BitVec.getLsbD_twoPow, Nat.one_lt_ofNat, decide_true, Bool.true_and,
    decide_eq_true_eq]
  simp only [eq_comm]

/-- The polynomial generator has only bit one set in its byte encoding. -/
@[simp] theorem toBitVec_gen : toBitVec gen = 2#8 := by
  rw [gen_eq_ofBitVec, toBitVec_ofBitVec]

end AesField
