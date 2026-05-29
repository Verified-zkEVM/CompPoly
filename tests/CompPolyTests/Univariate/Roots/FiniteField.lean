/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Finite-Field Univariate Root Tests

Focused executable coverage for the generic odd finite-field root backend.
-/

namespace CompPolyTests

open CompPoly
open CompPoly.CPolynomial.Roots.FiniteField

namespace Univariate.Roots.FiniteField

abbrev F3 := ZMod 3
abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 3) :=
  ⟨by decide⟩

instance : Fact (Nat.Prime 5) :=
  ⟨by decide⟩

private def f3Ctx : OddFiniteFieldContext F3 where
  q := 3
  finite := by infer_instance
  card_eq := by
    simp [F3, Nat.card_eq_fintype_card, ZMod.card]
  q_odd := by decide
  frobenius_fixed := by decide

private def f5Ctx : OddFiniteFieldContext F5 where
  q := 5
  finite := by infer_instance
  card_eq := by
    simp [F5, Nat.card_eq_fintype_card, ZMod.card]
  q_odd := by decide
  frobenius_fixed := by decide

private def f3Repeated : CPolynomial F3 :=
  CPolynomial.linearFactor (1 : F3) *
    CPolynomial.linearFactor (2 : F3) *
      CPolynomial.linearFactor (2 : F3)

private def f3SquarefreeProduct : CPolynomial F3 :=
  CPolynomial.linearFactor (1 : F3) *
    CPolynomial.linearFactor (2 : F3)

private def f3RootProduct : CPolynomial F3 :=
  finiteFieldRootProduct f3Ctx f3Repeated

#guard CPolynomial.evalHorner (1 : F3) f3RootProduct == 0
#guard CPolynomial.evalHorner (2 : F3) f3RootProduct == 0
#guard CPolynomial.evalHorner (0 : F3) f3RootProduct != 0
#guard f3RootProduct == f3SquarefreeProduct

private def f3NoRoot : CPolynomial F3 :=
  CPolynomial.ofArray #[(1 : F3), 0, 1]

#guard finiteFieldRootProduct f3Ctx f3NoRoot == 1

private def f5MultipleRoots : CPolynomial F5 :=
  CPolynomial.linearFactor (1 : F5) *
    CPolynomial.linearFactor (1 : F5) *
      CPolynomial.linearFactor (3 : F5)

private def f5LinearProduct : CPolynomial F5 :=
  CPolynomial.linearFactor (1 : F5) *
    CPolynomial.linearFactor (3 : F5)

private def f5RootProduct : CPolynomial F5 :=
  finiteFieldRootProduct f5Ctx f5MultipleRoots

#guard CPolynomial.evalHorner (1 : F5) f5RootProduct == 0
#guard CPolynomial.evalHorner (3 : F5) f5RootProduct == 0
#guard CPolynomial.evalHorner (2 : F5) f5RootProduct != 0
#guard f5RootProduct == f5LinearProduct

end Univariate.Roots.FiniteField

end CompPolyTests
