/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Minimal

/-!
# Correctness Contract for Mulders-Storjohann Reduction

Public correctness surface for the executable Mulders-Storjohann shifted row
reducer. The proof internals are split across
`MuldersStorjohannCorrectness.*` modules; this file collects the public
declarations through those imports.
-/
