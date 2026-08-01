/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/
module

public import CompPoly.Fields.KoalaBear.Basic
public import CompPoly.Fields.KoalaBear.Fast

/-!
# KoalaBear Field

Facade module for the KoalaBear field. It re-exports the canonical `ZMod` model
from `CompPoly.Fields.KoalaBear.Basic` and the native-word implementation from
`CompPoly.Fields.KoalaBear.Fast`.
-/

@[expose] public section
