/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Georgios Raikos
-/
module

import CompPoly.Fields.BN254.Basic
import CompPoly.Fields.BN254.Fast

/-!
# BN254 Scalar Field

Facade module for the BN254 scalar field. It re-exports the canonical `ZMod` model
from `CompPoly.Fields.BN254.Basic` and the native-word Montgomery implementation from
`CompPoly.Fields.BN254.Fast`.
-/
