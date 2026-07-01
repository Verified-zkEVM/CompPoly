/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Georgios Raikos
-/

import CompPoly.Fields.Secp256k1
import CompPoly.Fields.Secp256k1.Fq.Fast

/-!
# secp256k1 Base Field (`Fq`)

Facade module for the secp256k1 base/coordinate field (`BASE_FIELD_CARD = 2²⁵⁶ − 2³² − 977`). It
re-exports the canonical `ZMod` model `Secp256k1.BaseField` from `CompPoly.Fields.Secp256k1`
and the native-word Montgomery implementation from `CompPoly.Fields.Secp256k1.Fq.Fast`.
-/
