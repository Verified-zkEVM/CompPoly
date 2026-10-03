/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Data.Bytes.UInt32

/-! # Packed-word storage semantics for native FFT kernels -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Storage

/-- Pack words into consecutive four-byte little-endian slots. -/
def pack (words : Array UInt32) : ByteArray :=
  ⟨(ByteCodec.encodeList words.toList).toArray⟩

/-- Read a complete word slot, with zero for a missing slot. -/
def wordAt (bytes : ByteArray) (index : Nat) : UInt32 :=
  UInt32.ofNat (Bytes.ofListLE ((bytes.data.toList.drop (4 * index)).take 4))

@[simp] theorem size_pack (words : Array UInt32) : (pack words).size = 4 * words.size := by
  simp only [pack, ByteArray.size, List.size_toArray, ByteCodec.length_encodeList,
    Array.length_toList, ByteCodec.width_uint32, Nat.mul_comm]

/-- Packing preserves concatenation of complete word slots. -/
theorem pack_append (xs ys : Array UInt32) : pack (xs ++ ys) = pack xs ++ pack ys := by
  apply ByteArray.ext
  simp only [pack, ByteArray.data_append, Array.toList_append, ByteCodec.encodeList,
    List.flatMap_append, List.append_toArray]

private theorem drop_encodeList (words : List UInt32) (index : Nat) :
    (ByteCodec.encodeList words).drop (4 * index) = ByteCodec.encodeList (words.drop index) := by
  induction index generalizing words with
  | zero => simp only [Nat.mul_zero, List.drop_zero]
  | succ index ih =>
    cases words with
    | nil => simp only [ByteCodec.encodeList_nil, List.drop_nil]
    | cons x xs =>
      have hx : (ByteCodec.toBytes x).toList.length = 4 := by
        simp only [Vector.length_toList, ByteCodec.width_uint32]
      rw [ByteCodec.encodeList_cons, List.drop_append,
        List.drop_of_length_le (show (ByteCodec.toBytes x).toList.length ≤ 4 * (index + 1) by
          rw [hx]; omega)]
      simp only [List.nil_append, hx]
      rw [show 4 * (index + 1) - 4 = 4 * index by omega, ih, List.drop_succ_cons]

private theorem take_encodeList (words : List UInt32) (count : Nat) :
    (ByteCodec.encodeList words).take (4 * count) = ByteCodec.encodeList (words.take count) := by
  induction count generalizing words with
  | zero => simp only [Nat.mul_zero, List.take_zero, ByteCodec.encodeList_nil]
  | succ count ih =>
    cases words with
    | nil => simp only [ByteCodec.encodeList_nil, List.take_nil]
    | cons x xs =>
      have hx : (ByteCodec.toBytes x).toList.length = 4 := by
        simp only [Vector.length_toList, ByteCodec.width_uint32]
      rw [ByteCodec.encodeList_cons,
        show 4 * (count + 1) = (ByteCodec.toBytes x).toList.length + 4 * count by rw [hx]; omega,
        List.take_length_add_append, ih, List.take_succ_cons, ByteCodec.encodeList_cons]

/-- Byte extraction on slot boundaries is word extraction. -/
theorem pack_extract (words : Array UInt32) (first last : Nat) :
    (pack words).data.extract (4 * first) (4 * last) = (pack (words.extract first last)).data := by
  apply Array.toList_inj.mp
  simp only [pack, Array.toList_extract, List.toList_toArray, List.extract,
    ← Nat.mul_sub_left_distrib, drop_encodeList, take_encodeList]

/-- Replace a byte range without changing the other bytes. -/
def replace (bytes : ByteArray) (offset : Nat) (values : ByteArray) : ByteArray :=
  ⟨bytes.data.extract 0 offset ++ values.data ++
    bytes.data.extract (offset + values.size) bytes.size⟩

/-- Replacing packed slots is exactly the corresponding word-array splice. -/
theorem replace_pack (words values : Array UInt32) (index : Nat) :
    replace (pack words) (4 * index) (pack values) =
      pack (words.extract 0 index ++ values ++ words.extract (index + values.size) words.size) := by
  simp only [replace, size_pack, pack_append]
  apply ByteArray.ext
  simp only [ByteArray.data_append]
  have hp := pack_extract words 0 index
  simp only [Nat.mul_zero] at hp
  rw [hp,
    show 4 * index + 4 * values.size = 4 * (index + values.size) by omega, pack_extract]

/-- Each packed slot decodes to its original word. -/
theorem wordAt_pack (words : Array UInt32) (index : Nat) :
    wordAt (pack words) index = words.getD index 0 := by
  simp only [wordAt, pack, List.toList_toArray, drop_encodeList]
  rw [List.drop_eq_getElem?_toList_append]
  cases h : words.toList[index]? with
  | none =>
    have hn : words.toList.length ≤ index := List.getElem?_eq_none_iff.mp h
    rw [List.drop_of_length_le (show words.toList.length ≤ index + 1 by omega)]
    simp only [Option.toList_none, List.nil_append]
    simp only [ByteCodec.encodeList_nil, List.take_nil, Bytes.ofListLE_nil,
      Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h,
      Option.getD_none]
    rfl
  | some x =>
    simp only [Option.toList_some, List.singleton_append, ByteCodec.encodeList_cons]
    rw [List.take_left' (show (ByteCodec.toBytes x).toList.length = 4 by
      simp only [Vector.length_toList, ByteCodec.width_uint32]), ByteCodec.toBytes_uint32,
      Bytes.ofListLE_toListLE_of_lt (show x.toNat < 256 ^ 4 from x.toNat_lt),
      UInt32.ofNat_toNat]
    simp only [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, Option.getD_some]

end CompPoly.CPolynomial.NTTFast.Packed.Storage
