/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Data.ByteArray.Pack
public import CompPoly.Data.Bytes.LittleEndian

/-!
# Packed arrays of fixed-width elements

`PackedRepr R` stores every `R` in `width` bytes. `toBytes` and `ofBytes` are the specification;
`read` and `write` are the fast accesses at a byte offset, proved equal to it. The class stores
the carrier as is: a Montgomery field stores its residue, unlike its canonical `ByteCodec`
serialization.

A packed array is a `ByteArray` read through `PackedRepr.decode`; `PackedRepr.encode` packs an
`Array R`. Unlike an array of boxed values, a packed array is one scalar array: no per-element
indirection, and the runtime marks it as shared at once when a task returns it.

The byte-range lemmas (`encode_extract`, `replaceAt_encode`) describe the batch stores of fast
kernels; `read_encode` and `write_encode` describe single elements.
-/

@[expose] public section

universe u

namespace ByteArray

/-- Bytes `off, …, off + w - 1` of `b`; zero past the end. -/
def bytesAt (b : ByteArray) (off w : Nat) : Vector UInt8 w :=
  Vector.ofFn fun j ↦ b.get! (off + j.val)

/-- `b` with the bytes from `off` replaced by `values`; bytes past the end are dropped. -/
def replaceAt (b : ByteArray) (off : Nat) (values : ByteArray) : ByteArray :=
  ⟨b.data.extract 0 off ++ values.data ++ b.data.extract (off + values.size) b.size⟩

theorem size_replaceAt (b values : ByteArray) (off : Nat) (h : off + values.size ≤ b.size) :
    (b.replaceAt off values).size = b.size := by
  simp only [replaceAt, ByteArray.size, Array.size_append, Array.size_extract]
  simp only [ByteArray.size] at h
  omega

theorem replaceAt_empty (b : ByteArray) (off : Nat) (h : off ≤ b.size) :
    b.replaceAt off ByteArray.empty = b := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [replaceAt, ByteArray.size, Array.size_append, Array.size_extract]
    simp only [ByteArray.size] at h
    change min off b.data.size - 0 + 0 + (min b.data.size b.data.size - (off + 0)) = _
    omega
  · intro j h1 h2
    have he : ByteArray.empty.data.size = 0 := rfl
    simp only [ByteArray.size] at h
    simp only [replaceAt, ByteArray.size, Array.getElem_append, Array.getElem_extract,
      Array.size_append, Array.size_extract]
    split_ifs <;> first | omega | (congr 1; omega)

/-- Replacing two adjacent byte ranges is replacing their concatenation. -/
theorem replaceAt_replaceAt (b p q : ByteArray) (off : Nat)
    (h : off + p.size + q.size ≤ b.size) :
    (b.replaceAt off p).replaceAt (off + p.size) q = b.replaceAt off (p ++ q) := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [replaceAt, ByteArray.size, ByteArray.data_append, Array.size_append,
      Array.size_extract]
    simp only [ByteArray.size] at h
    omega
  · intro j h1 h2
    simp only [ByteArray.size] at h
    simp only [replaceAt, ByteArray.size, ByteArray.data_append, Array.getElem_append,
      Array.getElem_extract, Array.size_append, Array.size_extract]
    split_ifs <;> first | omega | (congr 1; omega)

/-- Replacing a byte range with its own bytes changes nothing. -/
theorem replaceAt_self (b : ByteArray) (off w : Nat) (h : off + w ≤ b.size) :
    b.replaceAt off ⟨(b.bytesAt off w).toArray⟩ = b := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [replaceAt, ByteArray.size, Array.size_append, Array.size_extract,
      Vector.size_toArray]
    simp only [ByteArray.size] at h
    omega
  · intro j h1 h2
    simp only [ByteArray.size] at h
    simp only [replaceAt, ByteArray.size, Array.getElem_append, Array.getElem_extract,
      Array.size_append, Array.size_extract, Vector.size_toArray]
    split_ifs
    · simp only [Nat.zero_add]
    · simp only [bytesAt, Vector.getElem_toArray, Vector.getElem_ofFn, ByteArray.get!,
        Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega
    · congr 1
      omega

/-- A 4 KiB zero block, the source of zero fills. -/
def zeroBlock : ByteArray := ⟨Array.replicate 4096 0⟩

/-- Append zero blocks to `b` until it holds `target` bytes, at most `fuel` times. The source is
a separate object, so the destination stays exclusive and is written in place. -/
def fillZeros (target : Nat) : Nat → ByteArray → ByteArray
  | 0, b => b
  | fuel + 1, b =>
    let n := b.size
    if n < target then
      fillZeros target fuel (zeroBlock.copySlice 0 b n (min 4096 (target - n)) false)
    else b

/-- `n` zero bytes, filled in place. -/
def zeros (n : Nat) : ByteArray :=
  fillZeros n (n / 4096 + 1) (ByteArray.emptyWithCapacity n)

theorem copySlice_replicate (k m len : Nat) (hl : len ≤ k) :
    (⟨Array.replicate k 0⟩ : ByteArray).copySlice 0 ⟨Array.replicate m 0⟩ m len false =
      ⟨Array.replicate (m + len) 0⟩ := by
  rw [ByteArray.copySlice_eq_append]
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.data_append, ByteArray.data_extract, Array.size_append,
      Array.size_extract, Array.size_replicate]
    omega
  · intro j h1 h2
    simp only [ByteArray.data_append, ByteArray.data_extract, Array.getElem_append,
      Array.getElem_extract, Array.getElem_replicate]
    split_ifs <;> rfl

theorem fillZeros_replicate (target : Nat) :
    ∀ (fuel m : Nat), m ≤ target → target ≤ m + 4096 * fuel →
      fillZeros target fuel ⟨Array.replicate m 0⟩ = ⟨Array.replicate target 0⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro m hle hge
    rw [show m = target by omega]
    rfl
  | succ fuel ih =>
    intro m hle hge
    have hm : (⟨Array.replicate m 0⟩ : ByteArray).size = m := Array.size_replicate
    unfold fillZeros
    by_cases hlt : m < target
    · simp only [hm, hlt, ↓reduceIte]
      rw [show zeroBlock = ⟨Array.replicate 4096 0⟩ from rfl,
        copySlice_replicate 4096 m _ (by omega)]
      exact ih _ (by omega) (by omega)
    · simp only [hm, hlt, ↓reduceIte]
      rw [show m = target by omega]

theorem zeros_eq (n : Nat) : zeros n = ⟨Array.replicate n 0⟩ := by
  unfold zeros
  rw [show ByteArray.emptyWithCapacity n = ⟨Array.replicate 0 0⟩ from rfl]
  exact fillZeros_replicate _ _ _ (by omega) (by omega)

@[simp] theorem size_zeros (n : Nat) : (zeros n).size = n := by
  rw [zeros_eq]
  exact Array.size_replicate

end ByteArray

namespace CompPoly

/-- A fixed-width byte representation of `R`, with fast accesses at byte offsets. -/
class PackedRepr (R : Type u) where
  /-- Bytes per element. -/
  width : Nat
  width_pos : 0 < width
  /-- The stored bytes of an element. -/
  toBytes : R → Vector UInt8 width
  /-- The element of stored bytes; every byte string decodes. -/
  ofBytes : Vector UInt8 width → R
  ofBytes_toBytes (x : R) : ofBytes (toBytes x) = x
  /-- Read the element at byte offset `i`. -/
  read : (b : ByteArray) → (i : USize) → i.toNat + width ≤ b.size → b.size < USize.size → R
  /-- Overwrite the element at byte offset `i`. -/
  write : (b : ByteArray) → (i : USize) → R → i.toNat + width ≤ b.size → b.size < USize.size →
    ByteArray
  read_eq (b : ByteArray) (i : USize) (h : i.toNat + width ≤ b.size) (hu : b.size < USize.size) :
    read b i h hu = ofBytes (b.bytesAt i.toNat width)
  write_eq (b : ByteArray) (i : USize) (x : R) (h : i.toNat + width ≤ b.size)
    (hu : b.size < USize.size) : write b i x h hu = b.replaceAt i.toNat ⟨(toBytes x).toArray⟩

attribute [simp] PackedRepr.ofBytes_toBytes

namespace PackedRepr

variable {R : Type u} [PackedRepr R]

/-- Pack elements into consecutive `width`-byte slots. -/
def encode (a : Array R) : ByteArray :=
  ⟨(a.toList.flatMap fun x ↦ (toBytes x).toList).toArray⟩

/-- The elements of the complete slots of a byte array. -/
def decode (b : ByteArray) : Array R :=
  Array.ofFn (n := b.size / width R) fun i ↦ ofBytes (b.bytesAt (width R * i.val) (width R))

private theorem length_flatMap (l : List R) :
    (l.flatMap fun x ↦ (toBytes x).toList).length = width R * l.length := by
  induction l with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero]
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, Vector.length_toList, ih,
      List.length_cons]
    rw [Nat.mul_succ]
    omega

@[simp] theorem size_encode (a : Array R) : (encode a).size = width R * a.size := by
  simp only [encode, ByteArray.size, List.size_toArray, length_flatMap, Array.length_toList]

@[simp] theorem encode_empty : encode (#[] : Array R) = ByteArray.empty := rfl

/-- Packing preserves concatenation. -/
theorem encode_append (a b : Array R) : encode (a ++ b) = encode a ++ encode b := by
  apply ByteArray.ext
  simp only [encode, ByteArray.data_append, Array.toList_append, List.flatMap_append,
    List.append_toArray]

private theorem drop_flatMap (l : List R) (i : Nat) :
    (l.flatMap fun x ↦ (toBytes x).toList).drop (width R * i) =
      (l.drop i).flatMap fun x ↦ (toBytes x).toList := by
  induction i generalizing l with
  | zero => simp only [Nat.mul_zero, List.drop_zero]
  | succ i ih =>
    cases l with
    | nil => simp only [List.flatMap_nil, List.drop_nil]
    | cons x xs =>
      rw [List.flatMap_cons, List.drop_append,
        List.drop_of_length_le (show (toBytes x).toList.length ≤ width R * (i + 1) by
          rw [Vector.length_toList, Nat.mul_succ]; omega)]
      simp only [List.nil_append, Vector.length_toList]
      rw [show width R * (i + 1) - width R = width R * i by rw [Nat.mul_succ]; omega, ih,
        List.drop_succ_cons]

private theorem take_flatMap (l : List R) (i : Nat) :
    (l.flatMap fun x ↦ (toBytes x).toList).take (width R * i) =
      (l.take i).flatMap fun x ↦ (toBytes x).toList := by
  induction i generalizing l with
  | zero => simp only [Nat.mul_zero, List.take_zero, List.flatMap_nil]
  | succ i ih =>
    cases l with
    | nil => simp only [List.flatMap_nil, List.take_nil]
    | cons x xs =>
      rw [List.flatMap_cons,
        show width R * (i + 1) = (toBytes x).toList.length + width R * i by
          rw [Vector.length_toList, Nat.mul_succ]; omega,
        List.take_length_add_append, ih, List.take_succ_cons, List.flatMap_cons]

/-- Byte extraction on slot boundaries is element extraction. -/
theorem encode_extract (a : Array R) (first last : Nat) :
    (encode a).data.extract (width R * first) (width R * last) =
      (encode (a.extract first last)).data := by
  apply Array.toList_inj.mp
  simp only [encode, Array.toList_extract, List.toList_toArray, List.extract,
    ← Nat.mul_sub_left_distrib, drop_flatMap, take_flatMap]

/-- Appending a slot range of a packed array copies its elements. -/
theorem copySlice_encode (a o : Array R) (i c : Nat) :
    (encode a).copySlice (width R * i) (encode o) (encode o).size (width R * c) =
      encode (o ++ a.extract i (i + c)) := by
  have hm : (encode a).extract (width R * i) (width R * i + width R * c) =
      encode (a.extract i (i + c)) := by
    apply ByteArray.ext
    rw [ByteArray.data_extract, ← Nat.mul_add, encode_extract]
  rw [ByteArray.copySlice_eq_append, ByteArray.extract_zero_size, hm,
    (ByteArray.extract_eq_empty_iff).mpr (by simp only [ByteArray.size]; omega),
    ByteArray.append_empty, encode_append]

/-- Replacing packed slots is the corresponding element splice. -/
theorem replaceAt_encode (a v : Array R) (i : Nat) :
    (encode a).replaceAt (width R * i) (encode v) =
      encode (a.extract 0 i ++ v ++ a.extract (i + v.size) a.size) := by
  simp only [ByteArray.replaceAt, size_encode, encode_append]
  apply ByteArray.ext
  simp only [ByteArray.data_append]
  have hp := encode_extract a 0 i
  simp only [Nat.mul_zero] at hp
  rw [hp, show width R * i + width R * v.size = width R * (i + v.size) by
    rw [Nat.mul_add], encode_extract]

/-- The bytes of a slot are its element's bytes. -/
theorem bytesAt_encode (a : Array R) (i : Nat) (hi : i < a.size) :
    (encode a).bytesAt (width R * i) (width R) = toBytes a[i] := by
  apply Vector.ext
  intro j hj
  have hd := congrArg (·[j]?) (drop_flatMap a.toList i)
  simp only [List.getElem?_drop] at hd
  rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList] using hi),
    List.flatMap_cons, List.getElem?_append_left (by simpa only [Vector.length_toList])] at hd
  simp only [ByteArray.bytesAt, Vector.getElem_ofFn, ByteArray.get!, encode,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, hd,
    Vector.getElem?_toList, Array.getElem_toList, Vector.getElem?_eq_getElem hj,
    Option.getD_some]

/-- Reading slot `i` of packed elements returns element `i`. -/
theorem read_encode (a : Array R) (off : USize) (i : Nat) (ho : off.toNat = width R * i)
    (hi : i < a.size) (h hu) : read (encode a) off h hu = a[i] := by
  rw [read_eq, ho, bytesAt_encode a i hi, ofBytes_toBytes]

omit [PackedRepr R] in
theorem set_eq_splice (a : Array R) (i : Nat) (x : R) (hi : i < a.size) :
    a.set i x hi = a.extract 0 i ++ #[x] ++ a.extract (i + 1) a.size := by
  apply Array.ext
  · simp only [Array.size_set, Array.size_append, Array.size_extract, List.size_toArray,
      List.length_cons, List.length_nil]
    omega
  · intro j h1 h2
    simp only [Array.size_set] at h1
    rw [Array.getElem_set]
    simp only [Array.getElem_append, Array.getElem_extract, Array.size_extract,
      List.size_toArray, List.length_cons, List.length_nil, Array.size_append]
    split_ifs <;> first | omega | (congr 1; omega) |
      (simp only [show j - (min i a.size - 0) = 0 by omega]; rfl)

/-- Writing slot `i` of packed elements sets element `i`. -/
theorem write_encode (a : Array R) (off : USize) (i : Nat) (x : R)
    (ho : off.toNat = width R * i) (hi : i < a.size) (h hu) :
    write (encode a) off x h hu = encode (a.set i x hi) := by
  rw [write_eq, ho, show (⟨(toBytes x).toArray⟩ : ByteArray) = encode #[x] by
      apply ByteArray.ext
      simp only [encode, List.flatMap_cons, List.flatMap_nil, List.append_nil, Vector.toList,
        Array.toArray_toList],
    replaceAt_encode, set_eq_splice a i x hi]
  rfl

/-- Decoding inverts packing. -/
@[simp] theorem decode_encode (a : Array R) : decode (encode a) = a := by
  have hw := width_pos (R := R)
  apply Array.ext
  · simp only [decode, Array.size_ofFn, size_encode, Nat.mul_div_cancel_left _ hw]
  · intro i h1 h2
    simp only [decode, Array.getElem_ofFn]
    rw [bytesAt_encode a i h2, ofBytes_toBytes]

theorem size_decode (b : ByteArray) : (decode (R := R) b).size = b.size / width R := by
  simp only [decode, Array.size_ofFn]

theorem getElem_decode (b : ByteArray) (i : Nat) (hi : i < (decode (R := R) b).size) :
    (decode (R := R) b)[i] = ofBytes (b.bytesAt (width R * i) (width R)) := by
  simp only [decode, Array.getElem_ofFn]

/-! ### Elements by index -/

/-- Element `j` of a byte array: the decoding of slot `j`, zero-padded past the end. -/
def get (b : ByteArray) (j : Nat) : R := ofBytes (b.bytesAt (width R * j) (width R))

theorem get_encode (a : Array R) (j : Nat) (hj : j < a.size) : get (encode a) j = a[j] := by
  rw [get, bytesAt_encode a j hj, ofBytes_toBytes]

theorem getElem_decode_eq_get (b : ByteArray) (j : Nat) (hj : j < (decode (R := R) b).size) :
    (decode (R := R) b)[j] = get b j :=
  getElem_decode b j hj

/-- Slot `k` of a buffer of `n` bytes with at least `k + 1` slots, at a machine offset. -/
theorem slot_toNat (k : USize) (n : Nat) (hk : k.toNat < n / width R) (hu : n < USize.size) :
    (k * (width R).toUSize).toNat = width R * k.toNat ∧ width R * k.toNat + width R ≤ n := by
  have hw := width_pos (R := R)
  have hle := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt hk)
  rw [Nat.succ_mul, Nat.mul_comm] at hle
  have hwu : width R < USize.size := by omega
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  refine ⟨?_, hle⟩
  rw [USize.toNat_mul, USize.toNat_ofNat_of_lt' hwu, hsize, Nat.mod_eq_of_lt (by
    rw [Nat.mul_comm]; omega), Nat.mul_comm]

/-- Read element `k` of a buffer with at least `k + 1` slots. -/
@[inline] def getAt (b : ByteArray) (k : USize) (hk : k.toNat < b.size / width R)
    (hu : b.size < USize.size) : R :=
  read b (k * (width R).toUSize) (by have := slot_toNat k b.size hk hu; rw [this.1]; omega) hu

theorem getAt_eq (b : ByteArray) (k : USize) (hk) (hu) :
    getAt (R := R) b k hk hu = get b k.toNat := by
  rw [getAt, read_eq, (slot_toNat k b.size hk hu).1, get]

/-- Overwrite element `k` of a buffer with at least `k + 1` slots. -/
@[inline] def setAt (b : ByteArray) (k : USize) (x : R) (hk : k.toNat < b.size / width R)
    (hu : b.size < USize.size) : ByteArray :=
  write b (k * (width R).toUSize) x (by have := slot_toNat k b.size hk hu; rw [this.1]; omega)
    hu

@[simp] theorem size_setAt (b : ByteArray) (k : USize) (x : R) (hk) (hu) :
    (setAt b k x hk hu).size = b.size := by
  have := slot_toNat k b.size hk hu
  have hsz : (⟨(toBytes x).toArray⟩ : ByteArray).size = width R := Vector.size_toArray _
  rw [setAt, write_eq, ByteArray.size_replaceAt _ _ _ (by rw [this.1, hsz]; exact this.2)]

theorem get!_replaceAt (b v : ByteArray) (off i : Nat) (h : off + v.size ≤ b.size) :
    (b.replaceAt off v).get! i = if off ≤ i ∧ i < off + v.size then v.get! (i - off)
      else b.get! i := by
  simp only [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ByteArray.size]
  simp only [ByteArray.size] at h
  by_cases hi : i < b.data.size
  · have hr : i < (b.replaceAt off v).data.size := by
      simp only [ByteArray.replaceAt, Array.size_append, Array.size_extract, ByteArray.size]
      omega
    rw [Array.getElem?_eq_getElem hr, Option.getD_some]
    simp only [ByteArray.replaceAt, Array.getElem_append, Array.getElem_extract,
      Array.size_append, Array.size_extract, ByteArray.size]
    split_ifs <;> first
      | omega
      | (rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1; omega)
  · have hr : ¬ i < (b.replaceAt off v).data.size := by
      simp only [ByteArray.replaceAt, Array.size_append, Array.size_extract, ByteArray.size]
      omega
    rw [Array.getElem?_eq_none (show (b.replaceAt off v).data.size ≤ i by omega)]
    split_ifs
    · omega
    · rw [Array.getElem?_eq_none (show b.data.size ≤ i by omega)]

theorem get_setAt (b : ByteArray) (k : USize) (x : R) (hk) (hu) (j : Nat) :
    get (setAt b k x hk hu) j = if j = k.toNat then x else get b j := by
  have hs := slot_toNat k b.size hk hu
  have hw := width_pos (R := R)
  have hs2 : width R * k.toNat + width R ≤ b.data.size := hs.2
  rw [setAt, write_eq, hs.1]
  unfold get
  split
  · rename_i hj
    subst hj
    conv_rhs => rw [← ofBytes_toBytes (R := R) x]
    congr 1
    apply Vector.ext
    intro t ht
    simp only [ByteArray.bytesAt, Vector.getElem_ofFn]
    rw [get!_replaceAt _ _ _ _ (by simp only [ByteArray.size, Vector.size_toArray]; omega)]
    simp only [ByteArray.size, Vector.size_toArray]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      show width R * k.toNat + t - width R * k.toNat = t by omega]
    simp only [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show t < (toBytes x).toArray.size by
        simp only [Vector.size_toArray]; exact ht), Option.getD_some, Vector.getElem_toArray]
  · rename_i hj
    congr 1
    apply Vector.ext
    intro t ht
    simp only [ByteArray.bytesAt, Vector.getElem_ofFn]
    rw [get!_replaceAt _ _ _ _ (by simp only [ByteArray.size, Vector.size_toArray]; omega)]
    simp only [ByteArray.size, Vector.size_toArray]
    refine ite_eq_right (fun hc ↦ ?_)
    obtain ⟨h1, h2⟩ := hc
    rcases Nat.lt_or_gt_of_ne hj with hlt | hgt
    · have : width R * (j + 1) ≤ width R * k.toNat := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_succ] at this
      omega
    · have : width R * (k.toNat + 1) ≤ width R * j := Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_succ] at this
      omega

/-- Overwrite element `k` of a buffer of `n` bytes when it is in range; otherwise leave the
buffer unchanged. The machine-size bound is proved once for `n`, not checked per store. -/
@[inline] def setIf (n : Nat) (hn : n < USize.size) (b : ByteArray) (k : USize) (x : R) :
    ByteArray :=
  if h : b.size = n ∧ k.toNat < b.size / width R then setAt b k x h.2 (h.1 ▸ hn) else b

theorem setAt_encode (a : Array R) (k : USize) (x : R) (hk) (hu) :
    setAt (encode a) k x hk hu =
      encode (a.set k.toNat x (by rwa [size_encode, Nat.mul_div_cancel_left _ width_pos] at hk)) :=
  write_encode a _ k.toNat x (slot_toNat k _ hk hu).1 _ _ _

/-- A guarded store into packed elements is the guarded array store. -/
theorem setIf_encode (a : Array R) (k : USize) (x : R) (hn : width R * a.size < USize.size) :
    setIf (width R * a.size) hn (encode a) k x = encode (a.setIfInBounds k.toNat x) := by
  unfold setIf
  have hdiv : (encode a).size / width R = a.size := by
    rw [size_encode, Nat.mul_div_cancel_left _ width_pos]
  split
  · rename_i h
    rw [setAt_encode]
    congr 1
    simp only [Array.setIfInBounds, show k.toNat < a.size by rw [← hdiv]; exact h.2,
      ↓reduceDIte]
  · rename_i h
    have hk : ¬ k.toNat < a.size := fun hk ↦ h ⟨size_encode a, by rw [hdiv]; exact hk⟩
    simp only [Array.setIfInBounds, hk, ↓reduceDIte]

theorem setIf_encode_of_eq (a : Array R) (k : USize) (x : R) (m : Nat) (hm : m < USize.size)
    (h : width R * a.size = m) :
    setIf m hm (encode a) k x = encode (a.setIfInBounds k.toNat x) := by
  subst h
  exact setIf_encode a k x hm

/-- A zero-filled buffer of `n` slots. -/
def alloc (R : Type u) [PackedRepr R] (n : Nat) : ByteArray := ByteArray.zeros (width R * n)

@[simp] theorem size_alloc (n : Nat) : (alloc R n).size = width R * n := ByteArray.size_zeros _

@[simp] theorem size_alloc_div (n : Nat) : (alloc R n).size / width R = n := by
  rw [size_alloc, Nat.mul_div_cancel_left _ width_pos]

/-- `n` copies of `block` appended to `acc`, by binary doubling. -/
def replicateGo (n : Nat) (block acc : ByteArray) : ByteArray :=
  if n = 0 then acc
  else replicateGo (n / 2) (block ++ block) (if n % 2 = 1 then acc ++ block else acc)
termination_by n
decreasing_by omega

/-- `n` packed copies of `x`, filled by doubling copies of its bytes. -/
def replicate (n : Nat) (x : R) : ByteArray :=
  replicateGo n ⟨(toBytes x).toArray⟩ (ByteArray.emptyWithCapacity (width R * n))

theorem replicateGo_encode (x : R) : ∀ (n m a : Nat),
    replicateGo n (encode (Array.replicate m x)) (encode (Array.replicate a x)) =
      encode (Array.replicate (a + n * m) x) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m a
    unfold replicateGo
    split
    · subst n; simp only [Nat.zero_mul, Nat.add_zero]
    · rename_i hn
      have hb : encode (Array.replicate m x) ++ encode (Array.replicate m x) =
          encode (Array.replicate (m + m) x) := by
        rw [← encode_append, Array.replicate_append_replicate]
      have hacc : encode (Array.replicate a x) ++ encode (Array.replicate m x) =
          encode (Array.replicate (a + m) x) := by
        rw [← encode_append, Array.replicate_append_replicate]
      rw [hb]
      have hk : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      generalize n / 2 = k at hk ih ⊢
      split
      · rename_i ho
        rw [hacc, ih k (by omega)]
        congr 2
        rw [hk, ho]
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.one_mul]
        omega
      · rename_i ho
        rw [ih k (by omega)]
        congr 2
        rw [hk, show n % 2 = 0 by omega]
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.zero_mul]
        omega

theorem replicate_eq (n : Nat) (x : R) : replicate n x = encode (Array.replicate n x) := by
  have h1 : (⟨(toBytes x).toArray⟩ : ByteArray) = encode (Array.replicate 1 x) := by
    apply ByteArray.ext
    simp only [encode, Array.replicate_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Vector.toList, Array.toArray_toList]
  have h0 : ByteArray.emptyWithCapacity (width R * n) = encode (Array.replicate 0 x) := rfl
  rw [replicate, h1, h0, replicateGo_encode, Nat.zero_add, Nat.mul_one]

/-! ### Four-byte words -/

/-- The little-endian bytes of a word. -/
def wordBytes (v : UInt32) : Vector UInt8 4 := Bytes.toVecLE 4 v.toNat

/-- The word of four little-endian bytes. -/
def ofWordBytes (v : Vector UInt8 4) : UInt32 := UInt32.ofNat (Bytes.ofVecLE v)

theorem ofWordBytes_wordBytes (v : UInt32) : ofWordBytes (wordBytes v) = v := by
  apply UInt32.toNat_inj.mp
  simp only [ofWordBytes, wordBytes, Bytes.ofVecLE_toVecLE_of_lt (show v.toNat < 256 ^ 4 from
    v.toNat_lt), UInt32.toNat_ofNat', Nat.mod_eq_of_lt v.toNat_lt]

theorem wordBytes_ofWordBytes (v : Vector UInt8 4) : wordBytes (ofWordBytes v) = v := by
  have hl := Bytes.ofVecLE_lt v
  simp only [wordBytes, ofWordBytes, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (show Bytes.ofVecLE v < 2 ^ 32 by simpa using hl), Bytes.toVecLE_ofVecLE]

theorem toUInt8_shiftRight (v : UInt32) (s : UInt32) (k : Nat) (hs : s.toNat = 8 * k)
    (hk : k < 4) : (v >>> s).toUInt8 = UInt8.ofNat (v.toNat / 2 ^ (8 * k) % 256) := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    hs, Nat.mod_eq_of_lt (show 8 * k < 32 by omega), Nat.mod_mod]

/-- A little-endian word store replaces four bytes with the word's bytes. -/
theorem setUInt32LE!_eq_replaceAt (b : ByteArray) (off : Nat) (v : UInt32)
    (h : off + 4 ≤ b.size) :
    b.setUInt32LE! off v = b.replaceAt off ⟨(wordBytes v).toArray⟩ := by
  have hp : (wordBytes v).toArray = #[UInt8.ofNat (v.toNat % 256),
      UInt8.ofNat (v.toNat / 256 % 256), UInt8.ofNat (v.toNat / 256 / 256 % 256),
      UInt8.ofNat (v.toNat / 256 / 256 / 256 % 256)] := by
    apply Array.toList_inj.mp
    simp only [wordBytes, Vector.toList_toArray, Bytes.toList_toVecLE, Bytes.toListLE_succ,
      Bytes.toListLE_zero]
  have hv0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := by
    have := toUInt8_shiftRight v 0 0 rfl (by decide)
    rwa [UInt32.shiftRight_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  have hv1 : (v >>> 8).toUInt8 = UInt8.ofNat (v.toNat / 256 % 256) :=
    toUInt8_shiftRight v 8 1 rfl (by decide)
  have hv2 : (v >>> 16).toUInt8 = UInt8.ofNat (v.toNat / 256 / 256 % 256) := by
    rw [Nat.div_div_eq_div_mul]; exact toUInt8_shiftRight v 16 2 rfl (by decide)
  have hv3 : (v >>> 24).toUInt8 = UInt8.ofNat (v.toNat / 256 / 256 / 256 % 256) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact toUInt8_shiftRight v 24 3 rfl (by decide)
  rw [hp]
  unfold ByteArray.setUInt32LE!
  rw [ite_eq_left h]
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.replaceAt, ByteArray.size, ByteArray.set!,
      Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_append,
      Array.size_extract, List.size_toArray, List.length_cons, List.length_nil]
    simp only [ByteArray.size] at h
    omega
  · intro j h1' h2'
    simp only [ByteArray.size] at h
    have hj : j < b.data.size := by
      simpa only [ByteArray.set!, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using h1'
    simp only [ByteArray.set!, Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds (by simp only [Array.size_setIfInBounds]; exact hj),
      Array.getElem_setIfInBounds (by simp only [Array.size_setIfInBounds]; exact hj),
      Array.getElem_setIfInBounds (by simp only [Array.size_setIfInBounds]; exact hj),
      Array.getElem_setIfInBounds hj]
    simp only [ByteArray.replaceAt, ByteArray.size, Array.getElem_append, Array.getElem_extract,
      Array.size_append, Array.size_extract, List.size_toArray, List.length_cons,
      List.length_nil, hv0, hv1, hv2, hv3]
    split_ifs <;> first
      | omega | (congr 1; omega)
      | (simp only [show j - (min off b.data.size - 0) = 0 by omega]; rfl)
      | (simp only [show j - (min off b.data.size - 0) = 1 by omega]; rfl)
      | (simp only [show j - (min off b.data.size - 0) = 2 by omega]; rfl)
      | (simp only [show j - (min off b.data.size - 0) = 3 by omega]; rfl)

/-- A little-endian word load reads the word of four bytes. -/
theorem getUInt32LE!_eq_ofWordBytes (b : ByteArray) (off : Nat) (h : off + 4 ≤ b.size) :
    b.getUInt32LE! off = ofWordBytes (b.bytesAt off 4) := by
  have hs := setUInt32LE!_eq_replaceAt b off (ofWordBytes (b.bytesAt off 4)) h
  rw [wordBytes_ofWordBytes, ByteArray.replaceAt_self b off 4 h] at hs
  have := ByteArray.getUInt32LE!_setUInt32LE!_self b off (ofWordBytes (b.bytesAt off 4)) h
  rwa [hs] at this

/-- Writing back the word just read changes nothing. -/
theorem setUInt32LE!_getUInt32LE! (b : ByteArray) (off : Nat) (h : off + 4 ≤ b.size) :
    b.setUInt32LE! off (b.getUInt32LE! off) = b := by
  rw [getUInt32LE!_eq_ofWordBytes b off h, setUInt32LE!_eq_replaceAt b off _ h,
    wordBytes_ofWordBytes, ByteArray.replaceAt_self b off 4 h]

/-- A representation by one 32-bit word: `toWord` stores, `ofWord` decodes every word. The
accesses are single word loads and stores. -/
@[inline, reducible] def ofWord32 {R : Type u} (toWord : R → UInt32) (ofWord : UInt32 → R)
    (ofWord_toWord : ∀ x, ofWord (toWord x) = x) : PackedRepr R where
  width := 4
  width_pos := by decide
  toBytes x := wordBytes (toWord x)
  ofBytes v := ofWord (ofWordBytes v)
  ofBytes_toBytes x := by simp only [ofWordBytes_wordBytes, ofWord_toWord]
  read b i h _ := ofWord (b.ugetUInt32LE i h)
  write b i x h _ := b.usetUInt32LE i (toWord x) h
  read_eq b i h _ := by
    simp only [ByteArray.ugetUInt32LE, getUInt32LE!_eq_ofWordBytes b i.toNat h]
  write_eq b i x h _ := by
    simp only [ByteArray.usetUInt32LE, setUInt32LE!_eq_replaceAt b i.toNat _ h]

@[inline] instance : PackedRepr UInt32 := ofWord32 id id fun _ ↦ rfl

@[simp] theorem width_uint32 : width UInt32 = 4 := rfl

@[simp] theorem size_encode_uint32 (W : Array UInt32) : (encode W).size = 4 * W.size :=
  size_encode W

/-- A little-endian word store replaces four bytes with the packed word. -/
theorem setUInt32LE!_eq_replaceAt_encode (b : ByteArray) (off : Nat) (v : UInt32)
    (h : off + 4 ≤ b.size) : b.setUInt32LE! off v = b.replaceAt off (encode #[v]) := by
  rw [setUInt32LE!_eq_replaceAt b off v h]
  rfl

/-- Replacing packed word slots is the corresponding word splice. -/
theorem replaceAt_encode_uint32 (W V : Array UInt32) (i : Nat) :
    (encode W).replaceAt (4 * i) (encode V) =
      encode (W.extract 0 i ++ V ++ W.extract (i + V.size) W.size) :=
  replaceAt_encode W V i

/-- Packing elements of a one-word representation is packing their words. -/
theorem encode_ofWord32 {R : Type u} (toWord : R → UInt32) (ofWord : UInt32 → R)
    (h : ∀ x, ofWord (toWord x) = x) (a : Array R) :
    @encode R (ofWord32 toWord ofWord h) a = encode (a.map toWord) := by
  apply ByteArray.ext
  simp only [encode, Array.toList_map, List.flatMap_map]
  rfl

/-- A word load from packed words reads one word. -/
theorem getUInt32LE!_encode (W : Array UInt32) (k : Nat) :
    (encode W).getUInt32LE! (4 * k) = W.getD k 0 := by
  by_cases hk : k < W.size
  · rw [getUInt32LE!_eq_ofWordBytes _ _ (by rw [size_encode]; simp; omega)]
    have := bytesAt_encode W k hk
    simp only [width_uint32] at this
    rw [this, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
    exact ofWordBytes_wordBytes _
  · unfold ByteArray.getUInt32LE!
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by rw [size_encode, width_uint32]; omega)),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]

/-- A word store into packed words sets one word. -/
theorem setUInt32LE!_encode (W : Array UInt32) (k : Nat) (v : UInt32) :
    (encode W).setUInt32LE! (4 * k) v = encode (W.set! k v) := by
  by_cases hk : k < W.size
  · rw [setUInt32LE!_eq_replaceAt _ _ _ (by rw [size_encode, width_uint32]; omega)]
    have := replaceAt_encode W #[v] k
    simp only [width_uint32] at this
    rw [show (⟨(wordBytes v).toArray⟩ : ByteArray) = encode #[v] by
        apply ByteArray.ext
        simp only [encode, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rfl, this]
    simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hk, ↓reduceDIte,
      set_eq_splice W k v hk]
    rfl
  · have hs : W.set! k v = W := by
      simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, show ¬k < W.size from hk,
        ↓reduceDIte]
    rw [hs]
    unfold ByteArray.setUInt32LE!
    rw [ite_eq_right_iff.mpr (fun h ↦ absurd h (by rw [size_encode, width_uint32]; omega))]

end PackedRepr

end CompPoly
