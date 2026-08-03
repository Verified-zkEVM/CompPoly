/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Setup

/-!
# Evaluation Benchmarks

Compiled benchmark executable for polynomial evaluation methods.
-/

public section

/-- Executable entry point for `lake exe CompPolyBench`. -/
def main (args : List String) : IO UInt32 :=
  CompPolyBench.run args
