/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Georgios Raikos
-/
module

public import CompPoly.Fields.BLS12_381.Basic
public import CompPoly.Fields.BLS12_381.Fast

/-!
# BLS12-381 Scalar Field

Facade module for the BLS12-381 scalar field. It re-exports the canonical `ZMod` model
from `CompPoly.Fields.BLS12_381.Basic` and the native-word Montgomery implementation from
`CompPoly.Fields.BLS12_381.Fast`.
-/
