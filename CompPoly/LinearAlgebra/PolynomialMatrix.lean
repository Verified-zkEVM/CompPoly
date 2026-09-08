/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.LinearAlgebra.PolynomialMatrix.Basic
public import CompPoly.LinearAlgebra.PolynomialMatrix.Degree
public import CompPoly.LinearAlgebra.PolynomialMatrix.Operations
public import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant
public import CompPoly.LinearAlgebra.PolynomialMatrix.Shifted
public import CompPoly.LinearAlgebra.PolynomialMatrix.RowSpan
public import CompPoly.LinearAlgebra.PolynomialMatrix.ShiftedReduction
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
public import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness

/-!
# Polynomial-Matrix Infrastructure

Reusable row-oriented polynomial-matrix infrastructure.
-/

@[expose] public section
