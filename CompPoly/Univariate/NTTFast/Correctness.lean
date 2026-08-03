/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Correctness.DIF
public import CompPoly.Univariate.NTTFast.Correctness.Radix4DIT
public import CompPoly.Univariate.NTTFast.Correctness.Radix4DIF
public import CompPoly.Univariate.NTTFast.Correctness.Pair
public import CompPoly.Univariate.NTTFast.Correctness.Pipeline

/-!
# Correctness proofs for NTTFast multiplication

This module re-exports the correctness proofs for the `NTTFast` transforms and
multiplication pipelines.
-/

@[expose] public section
