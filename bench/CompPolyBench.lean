/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Setup

/-!
# Evaluation Benchmarks

Compiled benchmark executable for polynomial evaluation methods.
-/

/-- Executable entry point for `lake exe CompPolyBench`. -/
def main : IO UInt32 :=
  CompPolyBench.run
