/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Georgios Raikos
-/
module

public import CompPoly.Fields.Secp256k1.Basic
public import CompPoly.Fields.Secp256k1.Fast

/-!
# Secp256k1 Fields

Facade module for the secp256k1 base and scalar fields. It re-exports the canonical `ZMod`
models from `CompPoly.Fields.Secp256k1.Basic` and the native-word Montgomery implementations
from `CompPoly.Fields.Secp256k1.Fast`.
-/
