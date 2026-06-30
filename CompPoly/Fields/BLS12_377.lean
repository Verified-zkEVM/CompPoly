/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Georgios Raikos
-/
module

import CompPoly.Fields.BLS12_377.Basic
import CompPoly.Fields.BLS12_377.Fast

/-!
# BLS12-377 Scalar Field

Facade module for the BLS12-377 scalar field. It re-exports the canonical `ZMod` model
from `CompPoly.Fields.BLS12_377.Basic` and the native-word Montgomery implementation from
`CompPoly.Fields.BLS12_377.Fast`.
-/
