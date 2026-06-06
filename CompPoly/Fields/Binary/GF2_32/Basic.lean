/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Basic
import CompPoly.Fields.Binary.GF2_32.Prelude

/-!
# GF(2^32) Quotient Specification

The quotient/specification carrier for the candidate polynomial
`X ^ 32 + X ^ 22 + X ^ 2 + X + 1`.

Field, finite, characteristic, and cardinality instances are conditional on the
irreducibility certificate that will be provided by the concrete certificate
modules.
-/

namespace GF2_32

open Polynomial AdjoinRoot

noncomputable section

/-- Quotient/specification carrier for `GF(2^32)`. -/
abbrev SpecField : Type :=
  BinaryField.Extension.SpecField definingPolynomialData

private instance instIrreduciblePolynomialFact [Fact (Irreducible definingPolynomial)] :
    Fact (Irreducible (BinaryField.Extension.polynomial definingPolynomialData)) := by
  simpa [definingPolynomial] using (inferInstance : Fact (Irreducible definingPolynomial))

/-- Conditional field instance, available once irreducibility is certified. -/
instance instFieldSpecField [Fact (Irreducible definingPolynomial)] :
    Field SpecField :=
  inferInstanceAs (Field (BinaryField.Extension.SpecField definingPolynomialData))

/-- Conditional nontriviality, available once irreducibility is certified. -/
instance instNontrivialSpecField [Fact (Irreducible definingPolynomial)] :
    Nontrivial SpecField :=
  inferInstance

/-- Quotient/specification carrier is inhabited. -/
instance instInhabitedSpecField : Inhabited SpecField :=
  inferInstance

/-- Algebra structure over `GF(2)`. -/
instance instAlgebraSpecField : Algebra (ZMod 2) SpecField :=
  inferInstanceAs (Algebra (ZMod 2) (BinaryField.Extension.SpecField definingPolynomialData))

/-- Conditional characteristic-two instance, available once irreducibility is certified. -/
instance instCharTwoSpecField [Fact (Irreducible definingPolynomial)] :
    CharP SpecField 2 :=
  inferInstance

/-- Canonical embedding of `GF(2)` into `SpecField`. -/
def ofGF2 : ZMod 2 →+* SpecField :=
  BinaryField.Extension.ofGF2 definingPolynomialData

/-- The quotient root/generator. -/
def root : SpecField :=
  BinaryField.Extension.root definingPolynomialData

/-- The quotient root satisfies the defining polynomial. -/
theorem root_satisfies_definingPolynomial :
    Polynomial.eval₂ (algebraMap (ZMod 2) SpecField) root definingPolynomial = 0 :=
  BinaryField.Extension.root_satisfies_polynomial definingPolynomialData

/-- Conditional finite type, available once irreducibility is certified. -/
instance instFintypeSpecField [Fact (Irreducible definingPolynomial)] :
    Fintype SpecField :=
  inferInstanceAs (Fintype (BinaryField.Extension.SpecField definingPolynomialData))

/-- Cardinality of the certified quotient specification. -/
theorem SpecField_card [Fact (Irreducible definingPolynomial)] :
    Fintype.card SpecField = 2 ^ extensionDegree :=
  BinaryField.Extension.specField_card definingPolynomialData

end

end GF2_32
