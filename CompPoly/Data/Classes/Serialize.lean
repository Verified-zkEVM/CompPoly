/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Serialization and deserialization classes

Simple type classes for serializing a type into another type, most often `ByteArray` or a
fixed-length `Vector` of units, and for deserializing back, with or without failure.

These declarations are ported verbatim from ArkLib (`ArkLib/Data/Classes/Serde.lean`) so that
CompPoly can supply instances for its field and polynomial types directly. The
statistical-closeness class `Deserialize.CloseToUniform` stays in ArkLib, where the probability
theory it needs already lives; CompPoly proves the counting facts behind it in `Nat` terms.
-/

@[expose] public section

universe u v

/-- Type class for types that can be serialized to another type (most often `ByteArray` or
  `String`). -/
class Serialize (α : Type u) (β : Type v) where
  serialize : α → β

export Serialize (serialize)

/-- Type class for injective serialization. -/
class Serialize.IsInjective (α : Type u) (β : Type v) [inst : Serialize α β] : Prop where
  serialize_inj : Function.Injective inst.serialize

/-- Type class for types that can be deserialized from another type (most often `ByteArray` or
  `String`), which _never_ fails. -/
class Deserialize (α : Type u) (β : Type v) where
  deserialize : β → α

/-- Type class for types that can be deserialized from another type (most often `ByteArray` or
  `String`), returning an `Option` if the deserialization fails. -/
class DeserializeOption (α : Type u) (β : Type v) where
  deserialize : β → Option α

/-- Type class for types that can be serialized and deserialized (with potential failure) to/from
  another type (most often `ByteArray` or `String`). -/
class Serde (α : Type u) (β : Type v) extends Serialize α β, DeserializeOption α β
