/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Varun Thakore
-/

module

public import CompPoly.Fields.Goldilocks.Basic
public import CompPoly.Fields.Goldilocks.Fast

/-!
  # Goldilocks prime field `2^{64} - 2^{32} + 1`

  Facade module for the Goldilocks field. It re-exports the canonical `ZMod` model
  from `CompPoly.Fields.Goldilocks.Basic` and the native-word implementation from
  `CompPoly.Fields.Goldilocks.Fast`.
-/

@[expose] public section
