/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Fields.Binary.GF2_72

/-!
  # GF(2^72) Executable Tests

  Regression checks for the raw `BitVec` executable carrier. These tests cover
  the certified computation layer and the field typeclass surface.
-/

namespace CompPolyTests.Fields.Binary.GF2_72.Impl

private abbrev F := GF2_72.ConcreteField

private def alpha : F :=
  GF2_72.ConcreteField.root

private def tailFromPowers : F :=
  GF2_72.ConcreteField.add
    (GF2_72.ConcreteField.add
      (GF2_72.ConcreteField.add
        (GF2_72.ConcreteField.add
          (GF2_72.ConcreteField.add
            (GF2_72.ConcreteField.pow alpha 6)
            (GF2_72.ConcreteField.pow alpha 4))
          (GF2_72.ConcreteField.pow alpha 3))
        (GF2_72.ConcreteField.pow alpha 2))
      alpha)
    1

#guard GF2_72.ConcreteField.toNat (GF2_72.ConcreteField.ofNat (2 ^ 72 + 5)) == 5

#guard GF2_72.ConcreteField.toNat
    (GF2_72.ConcreteField.add (GF2_72.ConcreteField.ofNat 0x1234)
      (GF2_72.ConcreteField.ofNat 0x00f0)) == 0x12c4

#guard GF2_72.ConcreteField.toNat
    (GF2_72.ConcreteField.mul (GF2_72.ConcreteField.ofNat 3)
      (GF2_72.ConcreteField.ofNat 5)) == 15

#guard GF2_72.ConcreteField.pow alpha 72 == tailFromPowers

#guard GF2_72.ConcreteField.toNat (GF2_72.ConcreteField.pow alpha 72) == 95

#guard GF2_72.ConcreteField.toNat (GF2_72.ConcreteField.traceValue 1) == 0

example :
    Fintype.card F = 2 ^ GF2_72.extensionDegree :=
  GF2_72.ConcreteField.card

example : GF2_72.ConcreteField.polynomialBasis.size = GF2_72.extensionDegree :=
  GF2_72.ConcreteField.polynomialBasis_size

example : GF2_72.ConcreteField.baseConstants.size = 2 :=
  GF2_72.ConcreteField.baseConstants_size

example : AddCommGroup F :=
  inferInstance

noncomputable example : Field F :=
  inferInstance

noncomputable example : CharP F 2 :=
  inferInstance

noncomputable example : Algebra (ZMod 2) F :=
  inferInstance

example : GF2_72.finiteFieldContext.q = GF2_72.fieldSize :=
  rfl

example : Nat.card F = GF2_72.fieldSize :=
  GF2_72.finiteFieldContext.card_eq

noncomputable example (a : F) : a ^ GF2_72.finiteFieldContext.q = a :=
  GF2_72.finiteFieldContext.frobenius_fixed a

example :
    orderOf GF2_72.primitiveRoot = GF2_72.fieldSize - 1 :=
  GF2_72.primitiveRoot_order

example :
    GF2_72.smoothHornerRootContext.q = GF2_72.fieldSize :=
  rfl

example :
    GF2_72.smoothHornerRootContext.generator = GF2_72.primitiveRoot :=
  rfl

example :
    GF2_72.smoothSubproductRootContext.q = GF2_72.fieldSize :=
  rfl

example :
    GF2_72.smoothSubproductRootContext.generator = GF2_72.primitiveRoot :=
  rfl

example : GF2_72.shoupTraceContext.p = 2 :=
  rfl

example : GF2_72.shoupTraceContext.k = GF2_72.extensionDegree :=
  rfl

example :
    GF2_72.shoupTraceContext.baseConstants.size = GF2_72.shoupTraceContext.p :=
  GF2_72.shoupTraceContext.baseConstants_size

example :
    GF2_72.shoupTraceContext.basis.size = GF2_72.shoupTraceContext.k :=
  GF2_72.shoupTraceContext.basis_size

noncomputable example (z : F) :
    GF2_72.shoupTraceContext.traceValue z =
      CompPoly.CPolynomial.Roots.FiniteField.tracePowerSum 2 GF2_72.extensionDegree z :=
  GF2_72.shoupTraceContext.traceValue_eq_powerSum z

noncomputable example (z : F) :
    GF2_72.shoupTraceContext.traceValue z ∈
      GF2_72.shoupTraceContext.baseConstants.toList :=
  GF2_72.shoupTraceContext.traceValue_mem_base z

noncomputable example {a b : F} (hne : a ≠ b) :
    ∃ beta, beta ∈ GF2_72.shoupTraceContext.basis.toList ∧
      GF2_72.shoupTraceContext.traceValue (beta * (a - b)) ≠ 0 :=
  GF2_72.shoupTraceContext.trace_separates hne

example : Function.Injective GF2_72.ConcreteField.toSpec :=
  GF2_72.ConcreteField.toSpec_injective

example :
    GF2_72.ConcreteField.toSpec GF2_72.ConcreteField.root = GF2_72.root :=
  GF2_72.ConcreteField.toSpec_root

example :
    GF2_72.ConcreteField.toSpec (0 : F) = 0 :=
  GF2_72.ConcreteField.toSpec_zero

example :
    GF2_72.ConcreteField.toSpec (1 : F) = 1 :=
  GF2_72.ConcreteField.toSpec_one

example (a b : F) :
    GF2_72.ConcreteField.toSpec (a + b) =
      GF2_72.ConcreteField.toSpec a + GF2_72.ConcreteField.toSpec b :=
  GF2_72.ConcreteField.toSpec_add a b

example (a b : F) :
    GF2_72.ConcreteField.toSpec (a - b) =
      GF2_72.ConcreteField.toSpec a - GF2_72.ConcreteField.toSpec b :=
  GF2_72.ConcreteField.toSpec_sub a b

example (a b : F) :
    GF2_72.ConcreteField.toSpec (a * b) =
      GF2_72.ConcreteField.toSpec a * GF2_72.ConcreteField.toSpec b :=
  GF2_72.ConcreteField.toSpec_mul a b

end CompPolyTests.Fields.Binary.GF2_72.Impl
