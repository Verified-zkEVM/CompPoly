/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Bytes.Codec
public import Mathlib.Tactic.Ring

/-!
# Byte codecs of vectors

A `Vector F n` encodes as the concatenation of the encodings of its entries, `n * width F`
bytes, and decodes entry by entry. This is the codec of every fixed-length composite: an
extension field element is its coefficient vector, a multilinear polynomial its evaluation
vector, a degree-bounded univariate polynomial its padded coefficient vector. It matches how
arkworks and plonky3 serialize extension fields and coefficient lists.

`Deserialize (Vector F n) (Vector UInt8 (n * k))` likewise decodes total, entry by entry, from
any per-entry total decoder, which is how a vector of challenges is read from a byte sponge.
-/

@[expose] public section

universe u

namespace CompPoly

namespace ByteCodec

variable {F : Type u} [ByteCodec F]

/-- Decode a list of exactly `width F` bytes. -/
def ofBytesList? (l : List UInt8) : Option F :=
  if h : l.length = width F then ofBytes? ⟨l.toArray, by simp only [List.size_toArray, h]⟩
  else none

@[simp]
theorem ofBytesList?_toList (x : F) : ofBytesList? (toBytes x).toList = some x := by
  unfold ofBytesList?
  split
  · simp only [Vector.toList, Array.toArray_toList, Vector.mk_toArray, ofBytes?_toBytes]
  · exact absurd (Vector.length_toList) (by assumption)

/-- The concatenated encodings of a list. -/
def encodeList (l : List F) : List UInt8 := l.flatMap fun x => (toBytes x).toList

@[simp] theorem encodeList_nil : encodeList ([] : List F) = [] := rfl

@[simp] theorem encodeList_cons (x : F) (l : List F) :
    encodeList (x :: l) = (toBytes x).toList ++ encodeList l := rfl

@[simp]
theorem length_encodeList (l : List F) : (encodeList l).length = l.length * width F := by
  induction l with
  | nil => simp only [encodeList_nil, List.length_nil, Nat.zero_mul]
  | cons x l ih =>
    rw [encodeList_cons, List.length_append, Vector.length_toList, ih, List.length_cons]
    ring

/-- Decode `m` consecutive encodings, failing on leftover bytes. -/
def decodeList : ℕ → List UInt8 → Option (List F)
  | 0, [] => some []
  | 0, _ :: _ => none
  | m + 1, l => do
    let x ← ofBytesList? (l.take (width F))
    let xs ← decodeList m (l.drop (width F))
    pure (x :: xs)

theorem decodeList_encodeList_of_length {m : ℕ} {l : List F} (h : l.length = m) :
    decodeList m (encodeList l) = some l := by
  induction l generalizing m with
  | nil =>
    subst h
    rfl
  | cons x l ih =>
    subst h
    rw [List.length_cons, encodeList_cons, decodeList,
      List.take_left' Vector.length_toList, List.drop_left' Vector.length_toList,
      ofBytesList?_toList, ih rfl]
    rfl

@[simp]
theorem decodeList_encodeList (l : List F) : decodeList l.length (encodeList l) = some l :=
  decodeList_encodeList_of_length rfl

/-- The concatenation codec of `Vector F n`: `n * width F` bytes. -/
instance instVector (n : ℕ) : ByteCodec (Vector F n) where
  width := n * width F
  toBytes v := ⟨(encodeList v.toList).toArray, by
    simp only [List.size_toArray, length_encodeList, Vector.length_toList]⟩
  ofBytes? b := (decodeList n b.toList).bind fun l =>
    if h : l.length = n then some ⟨l.toArray, by simp only [List.size_toArray, h]⟩ else none
  ofBytes?_toBytes v := by
    simp only [Vector.toList_mk]
    rw [decodeList_encodeList_of_length Vector.length_toList]
    simp only [Option.bind_some, Vector.toList, Array.toArray_toList, Vector.mk_toArray]
    have h : v.toArray.toList.length = n := by
      simp only [Array.length_toList, Vector.size_toArray]
    simp only [h, dite_true]

@[simp] theorem width_vector (n : ℕ) : width (Vector F n) = n * width F := rfl

theorem toList_toBytes_vector {n : ℕ} (v : Vector F n) :
    (toBytes v).toList = encodeList v.toList := rfl

end ByteCodec

/-- Total entry-by-entry decoding of a vector from `n * k` bytes. -/
def Vector.ofBytesEach {F : Type u} {k : ℕ} [Deserialize F (Vector UInt8 k)] (n : ℕ)
    (b : Vector UInt8 (n * k)) : Vector F n :=
  Vector.ofFn fun i => Deserialize.deserialize (Vector.ofFn fun j : Fin k =>
    b[i.1 * k + j.1]'(by
      calc i.1 * k + j.1 < i.1 * k + k := Nat.add_lt_add_left j.2 _
        _ = (i.1 + 1) * k := (Nat.succ_mul _ _).symm
        _ ≤ n * k := Nat.mul_le_mul_right k i.2))

instance {F : Type u} {k : ℕ} [Deserialize F (Vector UInt8 k)] (n : ℕ) :
    Deserialize (Vector F n) (Vector UInt8 (n * k)) :=
  ⟨Vector.ofBytesEach n⟩

end CompPoly
