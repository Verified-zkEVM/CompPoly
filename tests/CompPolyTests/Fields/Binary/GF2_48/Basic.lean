/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.Binary.GF2_48

/-!
  # GF(2^48) Basic Tests

  Compile-time checks for the direct-extension specification surface.
-/

namespace CompPolyTests.Fields.Binary.GF2_48.Basic

example : GF2_48.definingPolynomial.natDegree = GF2_48.extensionDegree :=
  GF2_48.definingPolynomial_natDegree

example : GF2_48.definingPolynomial.Monic :=
  GF2_48.definingPolynomial_monic

example : GF2_48.definingPolynomial ≠ 0 :=
  GF2_48.definingPolynomial_ne_zero

example :
    Polynomial.eval₂ (algebraMap (ZMod 2) GF2_48.SpecField) GF2_48.root
      GF2_48.definingPolynomial = 0 :=
  GF2_48.root_satisfies_definingPolynomial

example :
    BinaryField.Extension.sparsePolynomial GF2_48.definingPolynomialExponents =
      GF2_48.definingPolynomial :=
  GF2_48.sparsePolynomial_definingPolynomialExponents

#guard GF2_48.smoothRootSchedule.toList.foldl (fun order ell ↦ order / ell)
    (GF2_48.fieldSize - 1) == 1

#guard GF2_48.primitivePrimeFactors == [3, 5, 7, 13, 17, 97, 241, 257, 673]

example :
    GF2_48.multiplicativeGroupOrder =
      3 ^ 2 * 5 * 7 * 13 * 17 * 97 * 241 * 257 * 673 :=
  GF2_48.multiplicativeGroupOrder_factorization

end CompPolyTests.Fields.Binary.GF2_48.Basic
