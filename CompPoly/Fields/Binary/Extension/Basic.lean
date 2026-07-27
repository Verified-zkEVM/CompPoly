/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Prelude
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot

/-!
# Direct Binary-Extension Quotient Fields

Generic quotient/specification surface for direct binary extensions
`GF(2)[X] / (X^m + tail)`.

The field and cardinality instances are conditional on a future
`Fact (Irreducible (polynomial data))`, so concrete modules can expose the type
early while certificate files later make it a genuine finite field.
-/

namespace BinaryField

namespace Extension

open Polynomial AdjoinRoot

noncomputable section

/-- Quotient/specification carrier for a direct binary extension. -/
abbrev SpecField (data : DefiningPolynomialData) : Type :=
  AdjoinRoot (polynomial data)

/-- The quotient specification is inhabited. -/
instance instInhabitedSpecField (data : DefiningPolynomialData) :
    Inhabited (SpecField data) :=
  ⟨0⟩

/-- Conditional field instance, available once irreducibility is certified. -/
instance instFieldSpecField (data : DefiningPolynomialData)
    [Fact (Irreducible (polynomial data))] :
    Field (SpecField data) :=
  AdjoinRoot.instField

/-- Conditional nontriviality, available once irreducibility is certified. -/
instance instNontrivialSpecField (data : DefiningPolynomialData)
    [Fact (Irreducible (polynomial data))] :
    Nontrivial (SpecField data) :=
  inferInstance

/-- Algebra structure over `GF(2)`. -/
instance instAlgebraSpecField (data : DefiningPolynomialData) :
    Algebra (ZMod 2) (SpecField data) :=
  AdjoinRoot.instAlgebra (polynomial data)

/-- Conditional characteristic-two instance, available once irreducibility is certified. -/
instance instCharTwoSpecField (data : DefiningPolynomialData)
    [Fact (Irreducible (polynomial data))] :
    CharP (SpecField data) 2 := by
  haveI : CharP (ZMod 2) 2 := inferInstance
  exact charP_of_injective_algebraMap' (ZMod 2) 2

/-- Canonical embedding of `GF(2)` into the quotient specification. -/
def ofGF2 (data : DefiningPolynomialData) : ZMod 2 →+* SpecField data :=
  algebraMap (ZMod 2) (SpecField data)

/-- The quotient root/generator. -/
def root (data : DefiningPolynomialData) : SpecField data :=
  AdjoinRoot.root (polynomial data)

/-- The quotient root satisfies the defining polynomial. -/
theorem root_satisfies_polynomial (data : DefiningPolynomialData) :
    eval₂ (algebraMap (ZMod 2) (SpecField data)) (root data)
      (polynomial data) = 0 := by
  unfold root
  exact AdjoinRoot.eval₂_root (polynomial data)

/-- Conditional finite type, available once irreducibility is certified. -/
instance instFintypeSpecField (data : DefiningPolynomialData)
    [Fact (Irreducible (polynomial data))] :
    Fintype (SpecField data) := by
  have hpoly_ne_zero : polynomial data ≠ 0 :=
    Irreducible.ne_zero (Fact.out : Irreducible (polynomial data))
  let pb := AdjoinRoot.powerBasis hpoly_ne_zero
  letI : Module.Finite (ZMod 2) (SpecField data) := PowerBasis.finite pb
  haveI : Finite (SpecField data) := by
    have : Module.finrank (ZMod 2) (SpecField data) = pb.dim :=
      PowerBasis.finrank pb
    exact Finite.of_equiv (Fin pb.dim →₀ ZMod 2) (pb.basis.repr.toEquiv.symm)
  exact Fintype.ofFinite (SpecField data)

/-- Cardinality of a certified direct binary-extension quotient. -/
theorem specField_card (data : DefiningPolynomialData)
    [Fact (Irreducible (polynomial data))] :
    Fintype.card (SpecField data) = 2 ^ data.degree := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := SpecField data)]
  have hpoly_ne_zero : polynomial data ≠ 0 :=
    Irreducible.ne_zero (Fact.out : Irreducible (polynomial data))
  let pb := AdjoinRoot.powerBasis hpoly_ne_zero
  rw [PowerBasis.finrank pb]
  have h_pb_dim : pb.dim = (polynomial data).natDegree := by
    rfl
  rw [h_pb_dim, polynomial_natDegree]
  norm_num

end

end Extension

end BinaryField
