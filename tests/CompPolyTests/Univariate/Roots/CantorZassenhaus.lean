/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitrios Mitsios
-/
import CompPoly.Univariate.Roots.CantorZassenhaus
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Tests: Cantor–Zassenhaus linear-factor splitter

Executable `#guard` checks over the small prime field `ZMod 7`, where the default
shift schedule `0..6` is cheap. The splitter takes a squarefree product of linear
factors and returns its individual linear factors.
-/

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

namespace CompPolyTests
namespace CantorZassenhausTest

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev F : Type := ZMod 7

/-! ### Splitting `(X - 2)(X - 3)` into its two linear factors. -/

private def p₂₃ : CPolynomial F :=
  (CPolynomial.X - CPolynomial.C 2) * (CPolynomial.X - CPolynomial.C 3)

#guard (czSplitLinearFactors 7 p₂₃).size == 2
#guard (czSplitLinearFactors 7 p₂₃).contains (CPolynomial.linearFactor (2 : F))
#guard (czSplitLinearFactors 7 p₂₃).contains (CPolynomial.linearFactor (3 : F))

/-! ### A factor with root `0` is also found (`X(X - 1) = X² - X`). -/

private def p₀₁ : CPolynomial F := CPolynomial.X ^ 2 - CPolynomial.X

#guard (czSplitLinearFactors 7 p₀₁).size == 2
#guard (czSplitLinearFactors 7 p₀₁).contains (CPolynomial.linearFactor (0 : F))
#guard (czSplitLinearFactors 7 p₀₁).contains (CPolynomial.linearFactor (1 : F))

/-! ### Every emitted factor is linear (soundness, on a concrete input). -/

#guard (czSplitLinearFactors 7 p₂₃).all (fun f => isRepresentedLinearFactor f)

/-! ### Completeness is provable for any root (theorem-level check).

The polynomial-level hypotheses are kept abstract: `decide` does not kernel-reduce
`CPolynomial`/`ZMod` equalities, so `p ≠ 0` and `eval a p = 0` are taken as
arguments. The point is that `czComplete_zmod` composes for `ZMod 7`. -/

example (a : F) (hpne : p₂₃ ≠ 0) (h : CPolynomial.eval a p₂₃ = 0) :
    ∃ factor, factor ∈ (czSplitLinearFactors 7 p₂₃).toList ∧
      IsLinearRootFactorCandidate factor a :=
  czComplete_zmod 7 (by decide) p₂₃ a hpne h

end CantorZassenhausTest
end CompPolyTests
