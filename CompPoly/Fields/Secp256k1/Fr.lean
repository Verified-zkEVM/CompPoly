/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Georgios Raikos
-/

import CompPoly.Fields.Secp256k1
import CompPoly.Fields.Secp256k1.Fr.Fast

/-!
# secp256k1 Scalar Field (`Fr`)

Facade module for the secp256k1 scalar field (the group order `SCALAR_FIELD_CARD`). It
re-exports the canonical `ZMod` model `Secp256k1.ScalarField` from `CompPoly.Fields.Secp256k1`
and the native-word Montgomery implementation from `CompPoly.Fields.Secp256k1.Fr.Fast`.
-/
