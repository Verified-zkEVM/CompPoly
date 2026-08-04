/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.LinearAlgebra.Dense.Basic
public import CompPoly.LinearAlgebra.Dense.RowOps
public import CompPoly.LinearAlgebra.Dense.RowOpsCorrectness
public import CompPoly.LinearAlgebra.Dense.RrefSemantics
public import CompPoly.LinearAlgebra.Dense.RrefShape
public import CompPoly.LinearAlgebra.Dense.Kernel
public import CompPoly.LinearAlgebra.Dense.KernelInPlace
public import CompPoly.LinearAlgebra.Dense.KernelCorrectness
public import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness

/-!
# Dense Linear Algebra

Facade module for dense row-major matrices, row operations, homogeneous-kernel
extraction, and their correctness contracts.
-/

@[expose] public section
