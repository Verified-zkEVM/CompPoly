/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Bytes.Vector
public import CompPoly.Data.Bytes.LittleEndian

/-!
# Self-delimiting byte codecs

A variable-length type such as a polynomial cannot have a `ByteCodec`, whose width is fixed.
What it can have is a *self-delimiting* encoding: a decoder that reads exactly the bytes of one
encoding from the front of a stream and returns the rest. `DelimitedCodec α` is that pair,
with the one law `decode? (encode x ++ rest) = some (x, rest)`, stated for the `Valid x` the
format can represent. Every fixed-width codec is a delimited codec with `Valid = True`
(`DelimitedCodec.ofByteCodec`).

Lengths, counts, and exponents are framed as `u64` little-endian words, the arkworks layout,
so a natural is `Valid` when it is below `2 ^ 64` and a list when its length is and its
entries are. `Serialize.IsInjective` is derived only for `Total` codecs, where everything is
valid; for the others the injectivity theorem `encode_inj` carries the validity hypotheses.
Composite codecs for lists, pairs, and fixed-length vectors are built here, and the polynomial
codecs in `CompPoly.Univariate.Bytes`, `CompPoly.Multivariate.Bytes`, and
`CompPoly.Bivariate.Bytes` are assembled from them.
-/

@[expose] public section

universe u v

namespace CompPoly

/-- A self-delimiting byte encoding of `α`: `decode?` reads one encoding off the front of a
stream and returns the remainder. `Valid` marks the elements the format represents. -/
class DelimitedCodec (α : Type u) where
  /-- Encode an element. -/
  encode : α → List UInt8
  /-- Read one encoding from the front of a stream, returning the element and the rest. -/
  decode? : List UInt8 → Option (α × List UInt8)
  /-- The elements the format can represent. -/
  Valid : α → Prop
  decode?_encode_append (x : α) (rest : List UInt8) (h : Valid x) :
    decode? (encode x ++ rest) = some (x, rest)

namespace DelimitedCodec

variable {α : Type u} [DelimitedCodec α]

/-- A codec every element of whose type is valid. -/
class Total (α : Type u) [DelimitedCodec α] : Prop where
  valid (x : α) : Valid x

theorem decode?_encode {x : α} (h : Valid x) : decode? (encode x) = some (x, []) := by
  simpa only [List.append_nil] using decode?_encode_append x [] h

theorem encode_inj {x y : α} (hx : Valid x) (hy : Valid y) (h : encode x = encode y) : x = y := by
  have := decode?_encode hy
  rw [← h, decode?_encode hx, Option.some.injEq, Prod.mk.injEq] at this
  exact this.1

theorem encode_injective [Total α] : Function.Injective (encode : α → List UInt8) :=
  fun _ _ h => encode_inj (Total.valid _) (Total.valid _) h

/-- The encoding as a `ByteArray`. -/
def toByteArray (x : α) : ByteArray := ⟨(encode x).toArray⟩

/-- Decode a `ByteArray` holding exactly one encoding. -/
def ofByteArray? (b : ByteArray) : Option α :=
  match decode? b.data.toList with
  | some (x, []) => some x
  | _ => none

theorem ofByteArray?_toByteArray {x : α} (h : Valid x) : ofByteArray? (toByteArray x) = some x := by
  simp only [ofByteArray?, toByteArray, List.toList_toArray, decode?_encode h]

theorem toByteArray_inj {x y : α} (hx : Valid x) (hy : Valid y)
    (h : toByteArray x = toByteArray y) : x = y := by
  apply encode_inj hx hy
  have := congrArg (fun b : ByteArray => b.data.toList) h
  simpa only [toByteArray, List.toList_toArray] using this

/-! The protocol-facing instances are low priority so that a type with a `ByteCodec` keeps the
fixed-width instances of `CompPoly.Data.Bytes.Codec`; the two agree byte for byte
(`toByteArray_ofByteCodec`), but only one should be the canonical instance. -/

instance (priority := low) : Serialize α ByteArray := ⟨toByteArray⟩

instance (priority := low) : DeserializeOption α ByteArray := ⟨ofByteArray?⟩

instance (priority := low) : Serde α ByteArray where

instance (priority := low) [Total α] : Serialize.IsInjective α ByteArray :=
  ⟨fun _ _ h => toByteArray_inj (Total.valid _) (Total.valid _) h⟩

@[simp] theorem serialize_eq (x : α) : (serialize x : ByteArray) = toByteArray x := rfl

@[simp] theorem deserialize_eq (b : ByteArray) :
    (DeserializeOption.deserialize b : Option α) = ofByteArray? b := rfl

theorem deserialize_serialize {x : α} (h : Valid x) :
    (DeserializeOption.deserialize (serialize x : ByteArray) : Option α) = some x :=
  ofByteArray?_toByteArray h

/-! ## Fixed-width codecs are delimited -/

/-- A fixed-width codec read as a delimited one: `width` bytes, every element valid. -/
instance (priority := low) ofByteCodec {β : Type v} [ByteCodec β] : DelimitedCodec β where
  encode x := (ByteCodec.toBytes x).toList
  decode? l := (ByteCodec.ofBytesList? (l.take (ByteCodec.width β))).map
    fun x => (x, l.drop (ByteCodec.width β))
  Valid _ := True
  decode?_encode_append x rest _ := by
    rw [List.take_left' Vector.length_toList, List.drop_left' Vector.length_toList,
      ByteCodec.ofBytesList?_toList, Option.map_some]

instance {β : Type v} [ByteCodec β] : Total β := ⟨fun _ => trivial⟩

@[simp] theorem valid_ofByteCodec {β : Type v} [ByteCodec β] (x : β) : Valid x ↔ True := Iff.rfl

theorem encode_ofByteCodec {β : Type v} [ByteCodec β] (x : β) :
    encode x = (ByteCodec.toBytes x).toList := rfl

/-- Read as a delimited codec, a fixed-width codec produces the same bytes. -/
theorem toByteArray_ofByteCodec {β : Type v} [ByteCodec β] (x : β) :
    DelimitedCodec.toByteArray x = ByteCodec.toByteArray x := rfl

/-! ## `u64` framing -/

/-- The `u64` little-endian framing of a natural: lengths, counts, exponents. -/
def encodeU64 (n : ℕ) : List UInt8 := Bytes.toListLE 8 n

/-- Read a `u64` little-endian word from the front of a stream. -/
def decodeU64? (l : List UInt8) : Option (ℕ × List UInt8) :=
  if 8 ≤ l.length then some (Bytes.ofListLE (l.take 8), l.drop 8) else none

@[simp] theorem length_encodeU64 (n : ℕ) : (encodeU64 n).length = 8 := Bytes.length_toListLE 8 n

theorem decodeU64?_encodeU64_append {n : ℕ} (h : n < 2 ^ 64) (rest : List UInt8) :
    decodeU64? (encodeU64 n ++ rest) = some (n, rest) := by
  have hlen : (encodeU64 n).length = 8 := length_encodeU64 n
  have h8 : 8 ≤ (encodeU64 n ++ rest).length := by
    rw [List.length_append, hlen]
    omega
  simp only [decodeU64?, h8, ite_true]
  rw [List.take_left' hlen, List.drop_left' hlen, encodeU64,
    Bytes.ofListLE_toListLE_of_lt (show n < 256 ^ 8 by norm_num; exact h)]

/-- Naturals framed as `u64` words; valid below `2 ^ 64`. -/
instance instNat : DelimitedCodec ℕ where
  encode := encodeU64
  decode? := decodeU64?
  Valid n := n < 2 ^ 64
  decode?_encode_append _ rest h := decodeU64?_encodeU64_append h rest

@[simp] theorem valid_nat (n : ℕ) : Valid n ↔ n < 2 ^ 64 := Iff.rfl

@[simp] theorem encode_nat (n : ℕ) : encode n = encodeU64 n := rfl

/-! ## Sequences -/

/-- The concatenated encodings of a list, with no framing. -/
def encodeList (l : List α) : List UInt8 := l.flatMap encode

@[simp] theorem encodeList_nil : encodeList ([] : List α) = [] := rfl

@[simp] theorem encodeList_cons (x : α) (l : List α) :
    encodeList (x :: l) = encode x ++ encodeList l := rfl

/-- Read `m` consecutive encodings from the front of a stream. -/
def decodeN? : ℕ → List UInt8 → Option (List α × List UInt8)
  | 0, l => some ([], l)
  | m + 1, l => (decode? l).bind fun xl =>
    (decodeN? m xl.2).bind fun xsl => some (xl.1 :: xsl.1, xsl.2)

theorem decodeN?_encodeList_append {l : List α} (hv : ∀ x ∈ l, Valid x) (rest : List UInt8) :
    decodeN? l.length (encodeList l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, encodeList_cons, List.append_assoc, decodeN?,
      decode?_encode_append x _ (hv x List.mem_cons_self), Option.bind_some,
      ih (fun y hy => hv y (List.mem_cons_of_mem x hy)), Option.bind_some]

/-- Lists: a `u64` count, then the encodings. Valid when the count fits and the entries are
valid. -/
instance instList : DelimitedCodec (List α) where
  encode l := encodeU64 l.length ++ encodeList l
  decode? b := (decodeU64? b).bind fun nb => decodeN? nb.1 nb.2
  Valid l := l.length < 2 ^ 64 ∧ ∀ x ∈ l, Valid x
  decode?_encode_append l rest h := by
    rw [List.append_assoc, decodeU64?_encodeU64_append h.1, Option.bind_some,
      decodeN?_encodeList_append h.2]

theorem valid_list (l : List α) : Valid l ↔ l.length < 2 ^ 64 ∧ ∀ x ∈ l, Valid x := Iff.rfl

theorem encode_list (l : List α) : encode l = encodeU64 l.length ++ encodeList l := rfl

/-- Pairs: the first encoding, then the second. -/
instance instProd {β : Type v} [DelimitedCodec β] : DelimitedCodec (α × β) where
  encode p := encode p.1 ++ encode p.2
  decode? l := (decode? l).bind fun al =>
    (decode? (α := β) al.2).bind fun bl => some ((al.1, bl.1), bl.2)
  Valid p := Valid p.1 ∧ Valid p.2
  decode?_encode_append p rest h := by
    rw [List.append_assoc, decode?_encode_append _ _ h.1, Option.bind_some,
      decode?_encode_append _ _ h.2, Option.bind_some]

theorem valid_prod {β : Type v} [DelimitedCodec β] (p : α × β) : Valid p ↔ Valid p.1 ∧ Valid p.2 :=
  Iff.rfl

/-- A list of exactly `n` entries as a vector. -/
def vectorOfList? {γ : Type v} (n : ℕ) (xs : List γ) : Option (Vector γ n) :=
  if h : xs.length = n then some ⟨xs.toArray, by simp only [List.size_toArray, h]⟩ else none

@[simp]
theorem vectorOfList?_toList {γ : Type v} {n : ℕ} (v : Vector γ n) :
    vectorOfList? n v.toList = some v := by
  unfold vectorOfList?
  split
  · simp only [Vector.toList, Array.toArray_toList, Vector.mk_toArray]
  · exact absurd Vector.length_toList (by assumption)

/-- Fixed-length vectors of delimited elements: the `n` encodings with no count. Not an
instance, since a vector of fixed-width elements already has a codec through
`ByteCodec.instVector`; use it for element types without a `ByteCodec`. -/
@[instance_reducible]
def vector (n : ℕ) : DelimitedCodec (Vector α n) where
  encode v := encodeList v.toList
  decode? l := (decodeN? n l).bind fun p => (vectorOfList? n p.1).map fun v => (v, p.2)
  Valid v := ∀ x ∈ v.toList, Valid x
  decode?_encode_append v rest h := by
    have hl : (decodeN? v.toList.length (encodeList v.toList ++ rest) : Option (List α × _))
        = some (v.toList, rest) := decodeN?_encodeList_append h rest
    rw [Vector.length_toList] at hl
    rw [hl, Option.bind_some, vectorOfList?_toList, Option.map_some]

end DelimitedCodec

end CompPoly
