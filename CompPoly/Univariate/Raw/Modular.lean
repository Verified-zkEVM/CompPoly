/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Raw.Context

/-!
# Raw Modular Operations on Univariate Polynomials

Context-parametric modular multiplication and exponentiation over raw
univariate polynomials.
-/

namespace CompPoly

namespace CPolynomial.Raw

/-- Raw multiplication modulo a polynomial, treating zero modulus as no reduction. -/
def mulModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus p q : CPolynomial.Raw F) : CPolynomial.Raw F :=
  let product := M.mul p q
  if modulus.trim == 0 then
    product
  else
    D.modByMonic product (monicNormalize modulus)

/-- Raw binary modular exponentiation accumulator. -/
def powModBinaryAuxWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial.Raw F) :
    Nat → CPolynomial.Raw F → CPolynomial.Raw F → CPolynomial.Raw F
  | 0, acc, _ => acc
  | n + 1, acc, current =>
      let acc' :=
        if (n + 1) % 2 == 1 then
          mulModWith M D modulus acc current
        else
          acc
      let current' := mulModWith M D modulus current current
      powModBinaryAuxWith M D modulus ((n + 1) / 2) acc' current'
termination_by exp _ _ => exp
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

/-- Raw modular exponentiation by repeated squaring. -/
def powModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus base : CPolynomial.Raw F) (exponent : Nat) : CPolynomial.Raw F :=
  let oneMod :=
    if modulus.trim == 0 then
      (1 : CPolynomial.Raw F)
    else
      D.modByMonic (1 : CPolynomial.Raw F) (monicNormalize modulus)
  powModBinaryAuxWith M D modulus exponent oneMod base

/-- Raw `X mod modulus`, with zero modulus treated as no reduction. -/
def xModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (D : CPolynomial.Raw.ModContext F) : CPolynomial.Raw F → CPolynomial.Raw F
  | modulus =>
      if modulus.trim == 0 then
        (CPolynomial.Raw.X : CPolynomial.Raw F)
      else
        D.modByMonic (CPolynomial.Raw.X : CPolynomial.Raw F) (monicNormalize modulus)

/-- Raw `(X^q mod modulus) - (X mod modulus)`, without materializing `X^q - X`. -/
def xPowSubXModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (modulus : CPolynomial.Raw F) : CPolynomial.Raw F :=
  powModWith M D modulus (CPolynomial.Raw.X : CPolynomial.Raw F) q - xModWith D modulus

end CPolynomial.Raw

end CompPoly
