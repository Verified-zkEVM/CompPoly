/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-Field Root Contexts

Explicit contexts for executable univariate root finding over finite fields.
The algorithms use the cardinality carried here; downstream proofs use the
finite-field and splitter contracts without unfolding concrete implementations.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Finite-field facts needed by executable root extraction. -/
structure FiniteFieldContext (F : Type*) [Field F] where
  q : Nat
  finite : Finite F
  card_eq : Nat.card F = q
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
Completeness of the public root backend depends on splitter completeness for
every linear-factor product reached by the recursion.
-/
structure LinearFactorProductSplitter (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  splitLinearFactors : Nat → CPolynomial F → Array (CPolynomial F)
  /--
  The precondition under which `complete` is claimed for the splitter input.

  Root backends should establish this predicate for the field-root product they
  pass to the splitter. Executable splitters may remain defensive outside this
  predicate, but completeness is only part of the contract under it.
  -/
  validInput : Nat → CPolynomial F → Prop := fun _ _ ↦ True
  sound :
    ∀ q p factor,
      factor ∈ (splitLinearFactors q p).toList →
        IsLinearFactor factor
  complete :
    ∀ q p a,
      validInput q p →
        p ≠ 0 →
        CPolynomial.eval a p = 0 →
          ∃ factor,
            factor ∈ (splitLinearFactors q p).toList ∧
              IsLinearRootFactorCandidate factor a

end FiniteField

end Roots

end CPolynomial

end CompPoly
