/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.Binary.GF2_64

/-!
  # GF(2^64) Executable Tests

  Regression checks for the raw `BitVec` executable carrier. These tests cover
  the certified computation layer and the field typeclass surface.
-/

namespace CompPolyTests.Fields.Binary.GF2_64.Impl

private abbrev F := GF2_64.ConcreteField

private def alpha : F :=
  GF2_64.ConcreteField.root

private def tailFromPowers : F :=
  GF2_64.ConcreteField.add
    (GF2_64.ConcreteField.add
    (GF2_64.ConcreteField.add
    ((GF2_64.ConcreteField.pow alpha 4))
    (GF2_64.ConcreteField.pow alpha 3))
    (GF2_64.ConcreteField.pow alpha 1))
    1

#guard GF2_64.ConcreteField.toNat (GF2_64.ConcreteField.ofNat (2 ^ 64 + 5)) == 5

#guard GF2_64.ConcreteField.toNat
    (GF2_64.ConcreteField.add (GF2_64.ConcreteField.ofNat 0x1234)
      (GF2_64.ConcreteField.ofNat 0x00f0)) == 0x12c4

#guard GF2_64.ConcreteField.toNat
    (GF2_64.ConcreteField.mul (GF2_64.ConcreteField.ofNat 3)
      (GF2_64.ConcreteField.ofNat 5)) == 15

#guard GF2_64.ConcreteField.pow alpha 64 == tailFromPowers

#guard GF2_64.ConcreteField.toNat (GF2_64.ConcreteField.pow alpha 64) == 27

#guard GF2_64.ConcreteField.toNat (GF2_64.ConcreteField.traceValue 1) == 0

example :
    Fintype.card F = 2 ^ GF2_64.extensionDegree :=
  GF2_64.ConcreteField.card

example : GF2_64.ConcreteField.polynomialBasis.size = GF2_64.extensionDegree :=
  GF2_64.ConcreteField.polynomialBasis_size

example : GF2_64.ConcreteField.baseConstants.size = 2 :=
  GF2_64.ConcreteField.baseConstants_size

example : AddCommGroup F :=
  inferInstance

noncomputable example : Field F :=
  inferInstance

noncomputable example : CharP F 2 :=
  inferInstance

noncomputable example : Algebra (ZMod 2) F :=
  inferInstance

example : GF2_64.finiteFieldContext.q = GF2_64.fieldSize :=
  rfl

example : Nat.card F = GF2_64.fieldSize :=
  GF2_64.finiteFieldContext.card_eq

noncomputable example (a : F) : a ^ GF2_64.finiteFieldContext.q = a :=
  GF2_64.finiteFieldContext.frobenius_fixed a

example :
    orderOf GF2_64.primitiveRoot = GF2_64.fieldSize - 1 :=
  GF2_64.primitiveRoot_order

example :
    GF2_64.smoothHornerRootContext.q = GF2_64.fieldSize :=
  rfl

example :
    GF2_64.smoothHornerRootContext.generator = GF2_64.primitiveRoot :=
  rfl

example :
    GF2_64.smoothSubproductRootContext.q = GF2_64.fieldSize :=
  rfl

example :
    GF2_64.smoothSubproductRootContext.generator = GF2_64.primitiveRoot :=
  rfl

example : GF2_64.shoupTraceContext.p = 2 :=
  rfl

example : GF2_64.shoupTraceContext.k = GF2_64.extensionDegree :=
  rfl

example :
    GF2_64.shoupTraceContext.baseConstants.size = GF2_64.shoupTraceContext.p :=
  GF2_64.shoupTraceContext.baseConstants_size

example :
    GF2_64.shoupTraceContext.basis.size = GF2_64.shoupTraceContext.k :=
  GF2_64.shoupTraceContext.basis_size

noncomputable example (z : F) :
    GF2_64.shoupTraceContext.traceValue z =
      CompPoly.CPolynomial.Roots.FiniteField.tracePowerSum 2 GF2_64.extensionDegree z :=
  GF2_64.shoupTraceContext.traceValue_eq_powerSum z

noncomputable example (z : F) :
    GF2_64.shoupTraceContext.traceValue z ∈
      GF2_64.shoupTraceContext.baseConstants.toList :=
  GF2_64.shoupTraceContext.traceValue_mem_base z

noncomputable example {a b : F} (hne : a ≠ b) :
    ∃ beta, beta ∈ GF2_64.shoupTraceContext.basis.toList ∧
      GF2_64.shoupTraceContext.traceValue (beta * (a - b)) ≠ 0 :=
  GF2_64.shoupTraceContext.trace_separates hne

example : Function.Injective GF2_64.ConcreteField.toSpec :=
  GF2_64.ConcreteField.toSpec_injective

example :
    GF2_64.ConcreteField.toSpec GF2_64.ConcreteField.root = GF2_64.root :=
  GF2_64.ConcreteField.toSpec_root

example :
    GF2_64.ConcreteField.toSpec (0 : F) = 0 :=
  GF2_64.ConcreteField.toSpec_zero

example :
    GF2_64.ConcreteField.toSpec (1 : F) = 1 :=
  GF2_64.ConcreteField.toSpec_one

example (a b : F) :
    GF2_64.ConcreteField.toSpec (a + b) =
      GF2_64.ConcreteField.toSpec a + GF2_64.ConcreteField.toSpec b :=
  GF2_64.ConcreteField.toSpec_add a b

example (a b : F) :
    GF2_64.ConcreteField.toSpec (a - b) =
      GF2_64.ConcreteField.toSpec a - GF2_64.ConcreteField.toSpec b :=
  GF2_64.ConcreteField.toSpec_sub a b

example (a b : F) :
    GF2_64.ConcreteField.toSpec (a * b) =
      GF2_64.ConcreteField.toSpec a * GF2_64.ConcreteField.toSpec b :=
  GF2_64.ConcreteField.toSpec_mul a b

end CompPolyTests.Fields.Binary.GF2_64.Impl
