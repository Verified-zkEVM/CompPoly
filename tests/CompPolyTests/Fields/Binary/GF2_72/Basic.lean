/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.Binary.GF2_72

/-!
  # GF(2^72) Basic Tests

  Compile-time checks for the direct-extension specification surface.
-/

namespace CompPolyTests.Fields.Binary.GF2_72.Basic

example : GF2_72.definingPolynomial.natDegree = GF2_72.extensionDegree :=
  GF2_72.definingPolynomial_natDegree

example : GF2_72.definingPolynomial.Monic :=
  GF2_72.definingPolynomial_monic

example : GF2_72.definingPolynomial ≠ 0 :=
  GF2_72.definingPolynomial_ne_zero

example :
    Polynomial.eval₂ (algebraMap (ZMod 2) GF2_72.SpecField) GF2_72.root
      GF2_72.definingPolynomial = 0 :=
  GF2_72.root_satisfies_definingPolynomial

example :
    BinaryField.Extension.sparsePolynomial GF2_72.definingPolynomialExponents =
      GF2_72.definingPolynomial :=
  GF2_72.sparsePolynomial_definingPolynomialExponents

#guard GF2_72.smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell)
    (GF2_72.fieldSize - 1) == 1

#guard GF2_72.primitivePrimeFactors ==
  [3, 5, 7, 13, 17, 19, 37, 73, 109, 241, 433, 38737]

example :
    GF2_72.multiplicativeGroupOrder =
      3 ^ 3 * 5 * 7 * 13 * 17 * 19 * 37 * 73 * 109 * 241 * 433 * 38737 :=
  GF2_72.multiplicativeGroupOrder_factorization

end CompPolyTests.Fields.Binary.GF2_72.Basic
