/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Context

/-!
# Modular Operations on Univariate Polynomials

Reusable executable modular arithmetic for canonical `CPolynomial`s over public
`CPolynomial.MulContext` and `CPolynomial.ModContext` backends.
-/

namespace CompPoly

namespace CPolynomial

/-- Multiply modulo a polynomial, treating zero modulus as no reduction. -/
def mulModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : MulContext F) (D : ModContext F)
    (modulus p q : CPolynomial F) : CPolynomial F :=
  let product := M.mul p q
  if modulus == 0 then
    product
  else
    D.modByMonic product (monicNormalize modulus)

/-- Binary modular exponentiation accumulator. -/
def powModBinaryAuxWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : MulContext F) (D : ModContext F)
    (modulus : CPolynomial F) :
    Nat → CPolynomial F → CPolynomial F → CPolynomial F
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

/-- Modular exponentiation by repeated squaring. -/
def powModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : MulContext F) (D : ModContext F)
    (modulus base : CPolynomial F) (exponent : Nat) : CPolynomial F :=
  let oneMod :=
    if modulus == 0 then
      (1 : CPolynomial F)
    else
      D.modByMonic (1 : CPolynomial F) (monicNormalize modulus)
  powModBinaryAuxWith M D modulus exponent oneMod base

/-- `X mod modulus`, with zero modulus treated as no reduction. -/
def xModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (D : ModContext F) : CPolynomial F → CPolynomial F
  | modulus =>
      if modulus == 0 then
        (CPolynomial.X : CPolynomial F)
      else
        D.modByMonic (CPolynomial.X : CPolynomial F) (monicNormalize modulus)

/-- `(X^q mod modulus) - (X mod modulus)`, without materializing `X^q - X`. -/
def xPowSubXModWith {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (M : MulContext F) (D : ModContext F)
    (q : Nat) (modulus : CPolynomial F) : CPolynomial F :=
  powModWith M D modulus (CPolynomial.X : CPolynomial F) q - xModWith D modulus

end CPolynomial

end CompPoly
