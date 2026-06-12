/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.CoeffRows
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant
import CompPoly.Univariate.CoefficientInterpolation
import CompPoly.Univariate.Vanishing

/-!
# Approximant-Basis Guruswami-Sudan Modular Data

Construction of the diagonal modular equations used by the approximant-basis
interpolation backend.

## References

* [Chowdhury, M. F. I., Jeannerod, C.-P., Neiger, V., Schost, E., and
    Villard, G., *Faster algorithms for multivariate interpolation with
    multiplicities and simultaneous polynomial approximations*][CJNSV15]
-/

namespace CompPoly

namespace GuruswamiSudan

namespace ApproximantBasis

open PolynomialMatrix
open PolynomialMatrix.Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-- GS column moduli `M_b = G^(s-b)`, for `b = 0, ..., s-1`, built by iterated
context multiplication so each power costs one fast product. -/
def gsModuli (mulCtx : CPolynomial.MulContext F) (G : CPolynomial F) (s : Nat) :
    Array (CPolynomial F) := Id.run do
  if s == 0 then
    return #[]
  let mut ascending : Array (CPolynomial F) := #[G]
  for _ in [1:s] do
    ascending := ascending.push (mulCtx.mul (ascending.getD (ascending.size - 1) 0) G)
  return ascending.reverse

/-- Specification for one relation-matrix entry
`choose(j,b) * R^(j-b) mod M_b`, with zero below the triangular support.
This is the reference definition; the production path builds whole columns
incrementally with `gsRelationColumn`. -/
def gsRelationEntry (modCtx : CPolynomial.ModContext F)
    (R modulus : CPolynomial F) (j b : Nat) : CPolynomial F :=
  if b ≤ j then
    PolynomialMatrix.modByMonicWith modCtx
      (CPolynomial.C (Nat.choose j b : F) * R ^ (j - b)) modulus
  else
    0

/-- One relation-matrix column, built by iterated multiply-and-reduce.  Entry
`j` of column `b` is `choose(j,b) * R^(j-b) mod M_b`; the reduced power of `R`
is carried across entries so each step costs one context multiplication of
operands already reduced below `deg M_b` plus one context remainder. -/
def gsRelationColumn (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    (R modulus : CPolynomial F) (width b : Nat) :
    Array (CPolynomial F) := Id.run do
  let mut column := Array.replicate width (0 : CPolynomial F)
  let reducedR := PolynomialMatrix.modByMonicWith modCtx R modulus
  let mut power : CPolynomial F := 1
  for j in [b:width] do
    column := column.setIfInBounds j (CPolynomial.C (Nat.choose j b : F) * power)
    power := PolynomialMatrix.modByMonicWith modCtx (mulCtx.mul power reducedR) modulus
  return column

/-- GS relation matrix for the congruences `p * Fmat = 0 mod (G^s, ..., G)`,
assembled from incrementally built columns over precomputed moduli. -/
def gsRelationMatrixWithModuli (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    (R : CPolynomial F) (moduli : Array (CPolynomial F))
    (params : GSInterpParams) : PolynomialMatrix F :=
  let width := interpolationWidth params
  let columns := (List.range params.multiplicity).map
    (fun b ↦ gsRelationColumn mulCtx modCtx R (moduli.getD b 1) width b) |>.toArray
  PolynomialMatrix.ofFn width params.multiplicity fun j b ↦
    (columns.getD b #[]).getD j 0

/-- GS relation matrix for the congruences
`p * Fmat = 0 mod (G^s, ..., G)`. -/
def gsRelationMatrixWithRG (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    (R G : CPolynomial F) (params : GSInterpParams) : PolynomialMatrix F :=
  gsRelationMatrixWithModuli mulCtx modCtx R
    (gsModuli mulCtx G params.multiplicity) params

/-- Complete GS modular-equation data for the approximant backend. -/
structure GSModularData (F : Type*) [Zero F] where
  G : CPolynomial F
  R : CPolynomial F
  moduli : Array (CPolynomial F)
  matrix : PolynomialMatrix F
  shift : Array Nat

/-- Build column moduli, the binomial relation matrix, and the GS shift array
from precomputed interpolation polynomials `R` and `G`.  The moduli are
computed once and shared with the relation-matrix construction. -/
def buildGSModularDataWithRG
    (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    (R G : CPolynomial F) (params : GSInterpParams) : GSModularData F :=
  let moduli := gsModuli mulCtx G params.multiplicity
  { G := G
    R := R
    moduli := moduli
    matrix := gsRelationMatrixWithModuli mulCtx modCtx R moduli params
    shift := interpolationShifts params }

/-- Build `G`, `R`, column moduli, the binomial relation matrix, and the GS
shift array. -/
def buildGSModularData
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F)
    (points : Array (F × F)) (params : GSInterpParams) : GSModularData F :=
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
  buildGSModularDataWithRG mulCtx modCtx R G params

/-- Modular-equation view of GS modular data. -/
def modularEquation (data : GSModularData F) : ModularEquation F :=
  { moduli := data.moduli, matrix := data.matrix }

end ApproximantBasis

end GuruswamiSudan

end CompPoly
