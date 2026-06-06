/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.Binary.GF2_32

/-!
  # GF(2^32) Basic Tests

  Compile-time checks for the direct-extension specification surface.
-/

namespace CompPolyTests.Fields.Binary.GF2_32.Basic

example : GF2_32.definingPolynomial.natDegree = GF2_32.extensionDegree :=
  GF2_32.definingPolynomial_natDegree

example : GF2_32.definingPolynomial.Monic :=
  GF2_32.definingPolynomial_monic

example : GF2_32.definingPolynomial ≠ 0 :=
  GF2_32.definingPolynomial_ne_zero

example :
    Polynomial.eval₂ (algebraMap (ZMod 2) GF2_32.SpecField) GF2_32.root
      GF2_32.definingPolynomial = 0 :=
  GF2_32.root_satisfies_definingPolynomial

example :
    BinaryField.Extension.sparsePolynomial GF2_32.definingPolynomialExponents =
      GF2_32.definingPolynomial :=
  GF2_32.sparsePolynomial_definingPolynomialExponents

#guard GF2_32.smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell)
    (GF2_32.fieldSize - 1) == 1

#guard GF2_32.primitivePrimeFactors == [3, 5, 17, 257, 65537]

example :
    GF2_32.multiplicativeGroupOrder = 3 * 5 * 17 * 257 * 65537 :=
  GF2_32.multiplicativeGroupOrder_factorization

end CompPolyTests.Fields.Binary.GF2_32.Basic
