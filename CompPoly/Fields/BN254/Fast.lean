/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import Mathlib.Algebra.Field.TransferInstance
import CompPoly.Fields.BN254.Fast.Convert

/-!
# Fast BN254 Scalar Field — Operations

Native-word field operations on the fast Montgomery representation `ScalarField`: addition,
negation, subtraction, the CIOS Montgomery `mul`/`square`, exponentiation `pow`, and Fermat
inversion `inv`/`div`. `toField_mul`/`toField_square` bridge the multiplicative operations to
the canonical `ZMod p` field.
-/

set_option maxRecDepth 4000

namespace BN254
namespace Fast

open BN254 (scalarFieldSize)

@[inline]
def add (x y : ScalarField) : ScalarField :=
  reduceUInt256Lt2Modulus (x.val + y.val) (by
    rw [UInt256L.toNat_add]
    have hx := x.property
    have hy := y.property
    have hm := modulus_toNat
    omega)

/-- Fast zero in Montgomery form (the zero residue). -/
def zero : ScalarField := ⟨0, by decide⟩

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : ScalarField) : ScalarField :=
  if hx : x.val = 0 then
    zero
  else
    ⟨modulus - x.val, by
      have hle : x.val.toNat ≤ modulus.toNat := Nat.le_of_lt x.property
      rw [UInt256L.toNat_sub_of_le hle]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt256L.toNat_inj.mp
        simpa using hzero
      omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : ScalarField) : ScalarField :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt256L.le_iff_toNat_le] at hyx
      rw [UInt256L.toNat_sub_of_le hyx]
      have hx := x.property
      omega⟩
  else
    ⟨x.val + modulus - y.val, by
      have hb := x.property
      have hyb := y.property
      have hm := modulus_toNat
      have h2 := two_mul_scalarFieldSize_lt_two256
      rw [UInt256L.le_iff_toNat_le] at hyx
      have hbound : x.val.toNat + modulus.toNat < 2 ^ 256 := by omega
      have hsum_eq : (x.val + modulus).toNat = x.val.toNat + modulus.toNat := by
        rw [UInt256L.toNat_add, Nat.mod_eq_of_lt hbound]
      have hyle : y.val.toNat ≤ (x.val + modulus).toNat := by rw [hsum_eq]; omega
      rw [UInt256L.toNat_sub_of_le hyle, hsum_eq]
      omega⟩





/-- Fast one in Montgomery form (the residue `R mod p`). -/
def one : ScalarField := ⟨rModModulus, by decide⟩

/-- Fast modular multiplication in Montgomery form (CIOS Montgomery product). -/
@[inline]
def mul (x y : ScalarField) : ScalarField :=
  ⟨montgomeryMul x.val y.val, (montgomeryMul_spec x.val y.val (property_lt x)).1⟩

/-- Fast squaring. -/
@[inline]
def square (x : ScalarField) : ScalarField := mul x x

/-- Exponentiation by binary repeated squaring over the fast representation. -/
@[specialize]
def pow (x : ScalarField) (n : Nat) : ScalarField :=
  @npowBinRec ScalarField ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the prime field (`x⁻¹ = x^(p-2)`). -/
def invExponent : Nat := scalarFieldSize - 2

/-- Inversion in Montgomery form via Fermat's little theorem. -/
@[inline]
def inv (x : ScalarField) : ScalarField := pow x invExponent

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : ScalarField) : ScalarField := mul x (inv y)

/-- Fast multiplication agrees with multiplication in the canonical `ZMod p` field —
the field-level payoff of `montgomeryMul_spec`. -/
@[simp]
theorem toField_mul (x y : ScalarField) : toField (mul x y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv (mul x y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  have hval : (mul x y).val = montgomeryMul x.val y.val := rfl
  rw [hval, (montgomeryMul_spec x.val y.val (property_lt x)).2]
  ring

/-- Fast squaring agrees with self-multiplication in the canonical field. -/
@[simp]
theorem toField_square (x : ScalarField) : toField (square x) = toField x * toField x := by
  unfold square; exact toField_mul x x


end Fast
end BN254
