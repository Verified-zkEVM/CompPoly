/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Logic.Embedding.Basic

/-!
# `HasSize` class

A type has a size in units of `β` when it embeds into `Vector β size`. A duplex sponge over
units `β` absorbs and squeezes elements of such a type `size` units at a time.

Ported verbatim from ArkLib (`ArkLib/Data/Classes/HasSize.lean`).
-/

@[expose] public section

/-- Type class for types that has an injective mapping to a vector of a given length `size` of
  another type (often `UInt8`). -/
class HasSize (α : Type*) (β : Type*) where
  size : Nat
  toFun : α ↪ Vector β size
