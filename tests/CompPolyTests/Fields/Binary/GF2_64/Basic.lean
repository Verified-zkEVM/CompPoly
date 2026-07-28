/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.Binary.GF2_64

/-!
  # GF(2^64) Basic Tests

  Compile-time checks for the direct-extension specification surface.
-/

namespace CompPolyTests.Fields.Binary.GF2_64.Basic

example : GF2_64.definingPolynomial.natDegree = GF2_64.extensionDegree :=
  GF2_64.definingPolynomial_natDegree

example : GF2_64.definingPolynomial.Monic :=
  GF2_64.definingPolynomial_monic

example : GF2_64.definingPolynomial ≠ 0 :=
  GF2_64.definingPolynomial_ne_zero

example :
    Polynomial.eval₂ (algebraMap (ZMod 2) GF2_64.SpecField) GF2_64.root
      GF2_64.definingPolynomial = 0 :=
  GF2_64.root_satisfies_definingPolynomial

example :
    BinaryField.Extension.sparsePolynomial GF2_64.definingPolynomialExponents =
      GF2_64.definingPolynomial :=
  GF2_64.sparsePolynomial_definingPolynomialExponents

#guard GF2_64.smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell)
    (GF2_64.fieldSize - 1) == 1

#guard GF2_64.primitivePrimeFactors == [3, 5, 17, 257, 641, 65537, 6700417]

example :
    GF2_64.multiplicativeGroupOrder = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 :=
  GF2_64.multiplicativeGroupOrder_factorization

end CompPolyTests.Fields.Binary.GF2_64.Basic
