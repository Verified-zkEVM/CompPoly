/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-Field Root Contexts

Explicit contexts for executable univariate root finding over odd finite fields.
The algorithms use the cardinality carried here; downstream proofs use the
finite-field and splitter contracts without unfolding concrete implementations.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Finite-field facts needed by executable root extraction over odd fields. -/
structure OddFiniteFieldContext (F : Type*) [Field F] where
  q : Nat
  finite : Finite F
  card_eq : Nat.card F = q
  q_odd : q % 2 = 1
  frobenius_fixed : ∀ a : F, a ^ q = a

/-- A polynomial represented as a nonconstant linear factor. -/
def IsLinearFactor {F : Type*} [Field F] (factor : CPolynomial F) : Prop :=
  factor.val.size ≤ 2 ∧ factor.coeff 1 ≠ 0

/-- A linear factor whose extracted root is `a`. -/
def IsLinearRootFactorCandidate {F : Type*} [Field F]
    (factor : CPolynomial F) (a : F) : Prop :=
  IsLinearFactor factor ∧ factor.coeff 0 + factor.coeff 1 * a = 0

/-- A deterministic splitter for squarefree products of linear factors.

The executable function consumes the field cardinality and the current factor.
The contract is intentionally explicit: completeness of the public root backend
depends on this splitter being complete for every linear-factor product reached
by the recursion.
-/
structure LinearFactorProductSplitter (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  splitLinearFactors : Nat → CPolynomial F → Array (CPolynomial F)
  sound :
    ∀ q p factor,
      factor ∈ (splitLinearFactors q p).toList →
        IsLinearFactor factor
  complete :
    ∀ q p a,
      p ≠ 0 →
        CPolynomial.eval a p = 0 →
          ∃ factor,
            factor ∈ (splitLinearFactors q p).toList ∧
              IsLinearRootFactorCandidate factor a

end FiniteField

end Roots

end CPolynomial

end CompPoly
