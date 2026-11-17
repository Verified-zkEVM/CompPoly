/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public meta import CompPoly.Data.Bytes.Delimited
public meta import CompPoly.Data.Bytes.CanonicalNat
public import CompPoly.Data.Bytes.Delimited
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Self-delimiting codecs

`u64` framing, lists, pairs, fixed-length vectors, and the fixed-width codecs read as delimited
ones. Checked here: known vectors, that decoding consumes exactly one encoding and returns the
rest, that a stream with leftover or missing bytes is rejected at the `ByteArray` level, and the
class-level round trips.
-/

public meta section

namespace CompPolyTests.Delimited

open CompPoly CompPoly.DelimitedCodec

/-! ## `u64` framing -/

#guard encode (3 : ℕ) = [3, 0, 0, 0, 0, 0, 0, 0]
#guard encode (2 ^ 64 - 1 : ℕ) = List.replicate 8 0xff
#guard decode? (α := ℕ) [3, 0, 0, 0, 0, 0, 0, 0, 9, 9] = some (3, [9, 9])
#guard decode? (α := ℕ) [3, 0, 0] = none
-- Above the format's range the encoding wraps, so such a natural is not `Valid`.
#guard encode (2 ^ 64 : ℕ) = List.replicate 8 0
example : ¬ Valid (2 ^ 64 : ℕ) := by simp only [valid_nat, lt_self_iff_false, not_false_eq_true]
example : Valid (5 : ℕ) := by simp only [valid_nat]; norm_num

/-! ## Fixed-width codecs as delimited codecs -/

#guard encode (-1 : ZMod 257) = [0, 1]
#guard decode? (α := ZMod 257) [0, 1, 7] = some (-1, [7])
#guard decode? (α := ZMod 257) [0] = none
-- Out of range within the width is refused, as in the fixed codec.
#guard decode? (α := ZMod 257) [2, 1, 7] = none
example : Total (ZMod 257) := inferInstance

/-! ## Lists -/

#guard encode ([1, 2, 256] : List (ZMod 257)) = [3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1]
#guard encode ([] : List (ZMod 257)) = List.replicate 8 0
#guard decode? (α := List (ZMod 257)) [2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 5] = some ([1, 2], [5])
#guard decode? (α := List (ZMod 257)) [2, 0, 0, 0, 0, 0, 0, 0, 1, 0] = none
#guard (ofByteArray? (toByteArray ([1, 2, 256] : List (ZMod 257))) : Option (List (ZMod 257)))
  = some [1, 2, 256]
-- Leftover bytes are rejected by the `ByteArray` decoder.
#guard (ofByteArray? ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 9]⟩ : Option (List (ZMod 257))) = none
#guard (DeserializeOption.deserialize (serialize ([7, 8] : List (ZMod 257)) : ByteArray) :
  Option (List (ZMod 257))) = some [7, 8]

/-! ## Pairs and vectors -/

#guard encode ((3 : ℕ), (-1 : ZMod 257)) = [3, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#guard decode? (α := ℕ × ZMod 257) [3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4] = some ((3, -1), [4])
#guard (DelimitedCodec.vector (α := ℕ) 2).encode #v[1, 2]
  = [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
#guard (DelimitedCodec.vector (α := ℕ) 2).decode?
  [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 9] = some (#v[1, 2], [9])
#guard vectorOfList? 2 [1, 2] = some #v[1, 2]
#guard vectorOfList? (γ := ℕ) 3 [1, 2] = none

/-! ## Round trips and injectivity, as theorems -/

example (l : List (ZMod 257)) (h : l.length < 2 ^ 64) :
    (DeserializeOption.deserialize (serialize l : ByteArray) : Option (List (ZMod 257))) = some l :=
  deserialize_serialize ((valid_list l).mpr ⟨h, fun _ _ => trivial⟩)
example (x y : List (ZMod 257)) (hx : x.length < 2 ^ 64) (hy : y.length < 2 ^ 64)
    (h : encode x = encode y) : x = y :=
  encode_inj ((valid_list x).mpr ⟨hx, fun _ _ => trivial⟩)
    ((valid_list y).mpr ⟨hy, fun _ _ => trivial⟩) h
-- A fixed-width type keeps its fixed-width protocol instances, and the two codecs agree.
example (x : ZMod 257) : (serialize x : ByteArray) = ByteCodec.toByteArray x := rfl
example (x : ZMod 257) : DelimitedCodec.toByteArray x = ByteCodec.toByteArray x :=
  toByteArray_ofByteCodec x
example : Serialize.IsInjective (ZMod 257) ByteArray := inferInstance

end CompPolyTests.Delimited
