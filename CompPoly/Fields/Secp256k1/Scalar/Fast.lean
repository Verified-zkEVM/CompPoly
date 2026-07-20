/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Secp256k1.Scalar.Fast.Field

/-!
# Fast secp256k1 Scalar Field

Public entry point for the 4×UInt64 secp256k1 scalar implementation.

Importing this module provides the fast `Secp256k1.Scalar.Fast.Field`,
conversion functions, verified arithmetic operations, correctness theorems relating it
to the canonical `Secp256k1.Scalar.Basic.Field`, and the ring equivalence.
-/
