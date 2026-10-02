/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module
public import CompPoly.Univariate.NTTFast.Packed.Arithmetic
public import CompPoly.Univariate.NTTFast.Packed.Storage
public import CompPoly.Univariate.NTTFast.Natural
/-! # Packed native-storage KoalaBear FFT kernels
All arithmetic and scheduling are Lean. The two explicit externs replace only packed
word reads and batch writes/appends; their Lean definitions specify those storage operations.
-/
@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
theorem usize_numeral (n : Nat) (h : n < 4294967296) :
    (OfNat.ofNat n : USize).toNat = n := by
  rw [USize.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le h USize.le_size)
/-- Write or append at most sixteen little-endian words, preserving shared inputs. -/
@[extern c inline "({ lean_object *r = #1; size_t k = #2, n = lean_sarray_size(r), c = #3, z =
  4*c; uint32_t v[16] = {#5,#6,#7,#8,#9,#10,#11,#12,#13,#14,#15,#16,#17,#18,#19,#20}; if (c <=
  16) { if (#4) { if (lean_is_exclusive(r) && n <= SIZE_MAX-z && lean_sarray_capacity(r) >= n+z)
  { __builtin_memcpy(lean_sarray_cptr(r)+n, v, z); lean_sarray_set_size(r,n+z); } else { for
  (size_t j=0; j<c; ++j) for (unsigned q=0; q<4; ++q)
  r=lean_byte_array_push(r,(uint8_t)(v[j]>>(8*q))); } } else if (k <= SIZE_MAX-z && k+z <= n) {
  if (!lean_is_exclusive(r)) r=lean_copy_byte_array(r);
  __builtin_memcpy(lean_sarray_cptr(r)+k,v,z); } } r; })"] def storeWords (b : ByteArray) (offset :
    USize) (count : UInt8) (append : Bool)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) : ByteArray :=
  if count.toNat > 16 then b else
  let values := #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  let packed := Storage.pack (values.extract 0 count.toNat)
  if append then b ++ packed else
  if offset.toNat + 4 * count.toNat ≤ b.size ∧ offset.toNat + 4 * count.toNat < USize.size then
    Storage.replace b offset.toNat packed
  else b
/-- Read one packed word; unchecked reads carry a proof of the byte range. -/
@[extern c inline "({ size_t k = (#2 + #3) * 4; uint32_t v = 0; if (!#4 || (k <= SIZE_MAX - 4 &&
  k + 3 < lean_sarray_size(#1))) __builtin_memcpy(&v, lean_sarray_cptr(#1) + k, 4); v; })"] def
  readRaw (b : @& ByteArray) (i o : USize) (checked : Bool)
    (_h : checked = false → 4 * (i.toNat + o.toNat) + 3 < b.size ∧ b.size < USize.size) : UInt32 :=
  let offset := (i + o) * 4
  if checked && !(offset.toNat + 3 < b.size ∧ offset.toNat + 3 < USize.size) then 0 else
    UInt32.ofNat (Bytes.ofListLE ((b.data.toList.drop offset.toNat).take 4))
/-- Ordinary reads use the same checked word primitive. -/
@[inline] def read (b : @& ByteArray) (i : @& Nat) : UInt32 :=
  readRaw b i.toUSize 0 true (by intro h; cases h)
/-- Single-word writes use the same batch storage primitive. -/
@[inline] def write (b : ByteArray) (i : @& Nat) (v : UInt32) : ByteArray :=
  storeWords b (i.toUSize * 4) 1 false v 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
@[inline] def push (b : ByteArray) (v : UInt32) : ByteArray :=
  storeWords b 0 1 true v 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
def encode (a : Array KoalaBear.Fast.Field) : ByteArray :=
  a.foldl (fun b x ↦ push b x.val) (ByteArray.emptyWithCapacity (4 * a.size))
@[inline] def write16 (b : ByteArray) (i : @& Nat) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  v14 v15 : UInt32) : ByteArray :=
  storeWords b (i.toUSize * 4) 16 false v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
@[inline] def push16 (b : ByteArray) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 :
  UInt32) : ByteArray :=
  storeWords b 0 16 true v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
def inner (th tl : ByteArray) (q j i0 i1 i2 i3 : Nat) (b : ByteArray) : ByteArray :=
  if j < q then
    let x0 := read b i0
    let x1 := read b i1
    let x2 := read b i2
    let x3 := read b i3
    let a0 := add x0 x2
    let a1 := add x1 x3
    let a2 := mul (read th j) (sub x0 x2)
    let a3 := mul (read th (j + q)) (sub x1 x3)
    let b := write b i0 (add a0 a1)
    let b := write b i1 (mul (read tl j) (sub a0 a1))
    let b := write b i2 (add a2 a3)
    let b := write b i3 (mul (read tl j) (sub a2 a3))
    inner th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) b
  else b
termination_by q - j
decreasing_by omega
@[inline] def readUOffset (b : @& ByteArray) (i : USize) (o : USize)
    (h : 4 * (i.toNat + o.toNat) + 3 < b.size ∧ b.size < USize.size) : UInt32 :=
  readRaw b i o false (fun _ ↦ h)
@[noinline] def step16 (th tl : @& ByteArray) (j j1 i0 i1 i2 i3 : USize) (b : ByteArray)
    (h : 4 * (i0.toNat + 15) + 3 < b.size ∧
      4 * (i1.toNat + 15) + 3 < b.size ∧
      4 * (i2.toNat + 15) + 3 < b.size ∧
      4 * (i3.toNat + 15) + 3 < b.size ∧
      4 * (j1.toNat + 15) + 3 < th.size ∧
      4 * (j.toNat + 15) + 3 < th.size ∧
      4 * (j.toNat + 15) + 3 < tl.size ∧
      b.size < USize.size ∧
      th.size < USize.size ∧
      tl.size < USize.size) : ByteArray :=
  let x0_0 := readUOffset b (i0) 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1_0 := readUOffset b (i1) 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x2_0 := readUOffset b (i2) 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x3_0 := readUOffset b (i3) 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let a0_0 := add x0_0 x2_0
  let a1_0 := add x1_0 x3_0
  let a2_0 := mul (readUOffset th (j) 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (sub x0_0 x2_0)
  let a3_0 := mul (readUOffset th (j1) 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (sub x1_0 x3_0)
  let y0_0 := add a0_0 a1_0
  let y1_0 := mul (readUOffset tl (j) 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (sub a0_0 a1_0)
  let y2_0 := add a2_0 a3_0
  let y3_0 := mul (readUOffset tl (j) 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (sub a2_0 a3_0)
  let x0_1 := readUOffset b (i0) 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x1_1 := readUOffset b (i1) 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2_1 := readUOffset b (i2) 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x3_1 := readUOffset b (i3) 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let a0_1 := add x0_1 x2_1
  let a1_1 := add x1_1 x3_1
  let a2_1 := mul (readUOffset th (j) 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (sub x0_1 x2_1)
  let a3_1 := mul (readUOffset th (j1) 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (sub x1_1 x3_1)
  let y0_1 := add a0_1 a1_1
  let y1_1 := mul (readUOffset tl (j) 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (sub a0_1 a1_1)
  let y2_1 := add a2_1 a3_1
  let y3_1 := mul (readUOffset tl (j) 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (sub a2_1 a3_1)
  let x0_2 := readUOffset b (i0) 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x1_2 := readUOffset b (i1) 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x2_2 := readUOffset b (i2) 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3_2 := readUOffset b (i3) 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let a0_2 := add x0_2 x2_2
  let a1_2 := add x1_2 x3_2
  let a2_2 := mul (readUOffset th (j) 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (sub x0_2 x2_2)
  let a3_2 := mul (readUOffset th (j1) 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (sub x1_2 x3_2)
  let y0_2 := add a0_2 a1_2
  let y1_2 := mul (readUOffset tl (j) 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (sub a0_2 a1_2)
  let y2_2 := add a2_2 a3_2
  let y3_2 := mul (readUOffset tl (j) 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (sub a2_2 a3_2)
  let x0_3 := readUOffset b (i0) 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x1_3 := readUOffset b (i1) 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x2_3 := readUOffset b (i2) 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x3_3 := readUOffset b (i3) 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let a0_3 := add x0_3 x2_3
  let a1_3 := add x1_3 x3_3
  let a2_3 := mul (readUOffset th (j) 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (sub x0_3 x2_3)
  let a3_3 := mul (readUOffset th (j1) 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (sub x1_3 x3_3)
  let y0_3 := add a0_3 a1_3
  let y1_3 := mul (readUOffset tl (j) 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (sub a0_3 a1_3)
  let y2_3 := add a2_3 a3_3
  let y3_3 := mul (readUOffset tl (j) 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (sub a2_3 a3_3)
  let x0_4 := readUOffset b (i0) 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x1_4 := readUOffset b (i1) 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x2_4 := readUOffset b (i2) 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x3_4 := readUOffset b (i3) 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let a0_4 := add x0_4 x2_4
  let a1_4 := add x1_4 x3_4
  let a2_4 := mul (readUOffset th (j) 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (sub x0_4 x2_4)
  let a3_4 := mul (readUOffset th (j1) 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (sub x1_4 x3_4)
  let y0_4 := add a0_4 a1_4
  let y1_4 := mul (readUOffset tl (j) 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (sub a0_4 a1_4)
  let y2_4 := add a2_4 a3_4
  let y3_4 := mul (readUOffset tl (j) 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (sub a2_4 a3_4)
  let x0_5 := readUOffset b (i0) 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x1_5 := readUOffset b (i1) 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x2_5 := readUOffset b (i2) 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x3_5 := readUOffset b (i3) 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let a0_5 := add x0_5 x2_5
  let a1_5 := add x1_5 x3_5
  let a2_5 := mul (readUOffset th (j) 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (sub x0_5 x2_5)
  let a3_5 := mul (readUOffset th (j1) 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (sub x1_5 x3_5)
  let y0_5 := add a0_5 a1_5
  let y1_5 := mul (readUOffset tl (j) 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (sub a0_5 a1_5)
  let y2_5 := add a2_5 a3_5
  let y3_5 := mul (readUOffset tl (j) 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (sub a2_5 a3_5)
  let x0_6 := readUOffset b (i0) 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x1_6 := readUOffset b (i1) 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x2_6 := readUOffset b (i2) 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x3_6 := readUOffset b (i3) 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let a0_6 := add x0_6 x2_6
  let a1_6 := add x1_6 x3_6
  let a2_6 := mul (readUOffset th (j) 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (sub x0_6 x2_6)
  let a3_6 := mul (readUOffset th (j1) 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (sub x1_6 x3_6)
  let y0_6 := add a0_6 a1_6
  let y1_6 := mul (readUOffset tl (j) 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (sub a0_6 a1_6)
  let y2_6 := add a2_6 a3_6
  let y3_6 := mul (readUOffset tl (j) 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (sub a2_6 a3_6)
  let x0_7 := readUOffset b (i0) 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x1_7 := readUOffset b (i1) 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x2_7 := readUOffset b (i2) 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x3_7 := readUOffset b (i3) 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let a0_7 := add x0_7 x2_7
  let a1_7 := add x1_7 x3_7
  let a2_7 := mul (readUOffset th (j) 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (sub x0_7 x2_7)
  let a3_7 := mul (readUOffset th (j1) 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (sub x1_7 x3_7)
  let y0_7 := add a0_7 a1_7
  let y1_7 := mul (readUOffset tl (j) 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (sub a0_7 a1_7)
  let y2_7 := add a2_7 a3_7
  let y3_7 := mul (readUOffset tl (j) 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (sub a2_7 a3_7)
  let x0_8 := readUOffset b (i0) 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x1_8 := readUOffset b (i1) 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x2_8 := readUOffset b (i2) 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x3_8 := readUOffset b (i3) 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let a0_8 := add x0_8 x2_8
  let a1_8 := add x1_8 x3_8
  let a2_8 := mul (readUOffset th (j) 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (sub x0_8 x2_8)
  let a3_8 := mul (readUOffset th (j1) 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (sub x1_8 x3_8)
  let y0_8 := add a0_8 a1_8
  let y1_8 := mul (readUOffset tl (j) 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (sub a0_8 a1_8)
  let y2_8 := add a2_8 a3_8
  let y3_8 := mul (readUOffset tl (j) 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (sub a2_8 a3_8)
  let x0_9 := readUOffset b (i0) 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x1_9 := readUOffset b (i1) 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x2_9 := readUOffset b (i2) 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x3_9 := readUOffset b (i3) 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let a0_9 := add x0_9 x2_9
  let a1_9 := add x1_9 x3_9
  let a2_9 := mul (readUOffset th (j) 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (sub x0_9 x2_9)
  let a3_9 := mul (readUOffset th (j1) 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (sub x1_9 x3_9)
  let y0_9 := add a0_9 a1_9
  let y1_9 := mul (readUOffset tl (j) 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (sub a0_9 a1_9)
  let y2_9 := add a2_9 a3_9
  let y3_9 := mul (readUOffset tl (j) 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (sub a2_9 a3_9)
  let x0_10 := readUOffset b (i0) 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x1_10 := readUOffset b (i1) 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x2_10 := readUOffset b (i2) 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x3_10 := readUOffset b (i3) 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let a0_10 := add x0_10 x2_10
  let a1_10 := add x1_10 x3_10
  let a2_10 := mul (readUOffset th (j) 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (sub x0_10 x2_10)
  let a3_10 := mul (readUOffset th (j1) 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (sub x1_10 x3_10)
  let y0_10 := add a0_10 a1_10
  let y1_10 := mul (readUOffset tl (j) 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (sub a0_10 a1_10)
  let y2_10 := add a2_10 a3_10
  let y3_10 := mul (readUOffset tl (j) 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (sub a2_10 a3_10)
  let x0_11 := readUOffset b (i0) 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x1_11 := readUOffset b (i1) 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x2_11 := readUOffset b (i2) 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x3_11 := readUOffset b (i3) 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let a0_11 := add x0_11 x2_11
  let a1_11 := add x1_11 x3_11
  let a2_11 := mul (readUOffset th (j) 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (sub x0_11 x2_11)
  let a3_11 := mul (readUOffset th (j1) 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (sub x1_11 x3_11)
  let y0_11 := add a0_11 a1_11
  let y1_11 := mul (readUOffset tl (j) 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (sub a0_11 a1_11)
  let y2_11 := add a2_11 a3_11
  let y3_11 := mul (readUOffset tl (j) 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (sub a2_11 a3_11)
  let x0_12 := readUOffset b (i0) 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x1_12 := readUOffset b (i1) 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x2_12 := readUOffset b (i2) 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x3_12 := readUOffset b (i3) 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let a0_12 := add x0_12 x2_12
  let a1_12 := add x1_12 x3_12
  let a2_12 := mul (readUOffset th (j) 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (sub x0_12 x2_12)
  let a3_12 := mul (readUOffset th (j1) 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (sub x1_12 x3_12)
  let y0_12 := add a0_12 a1_12
  let y1_12 := mul (readUOffset tl (j) 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (sub a0_12 a1_12)
  let y2_12 := add a2_12 a3_12
  let y3_12 := mul (readUOffset tl (j) 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (sub a2_12 a3_12)
  let x0_13 := readUOffset b (i0) 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x1_13 := readUOffset b (i1) 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x2_13 := readUOffset b (i2) 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x3_13 := readUOffset b (i3) 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let a0_13 := add x0_13 x2_13
  let a1_13 := add x1_13 x3_13
  let a2_13 := mul (readUOffset th (j) 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (sub x0_13 x2_13)
  let a3_13 := mul (readUOffset th (j1) 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (sub x1_13 x3_13)
  let y0_13 := add a0_13 a1_13
  let y1_13 := mul (readUOffset tl (j) 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (sub a0_13 a1_13)
  let y2_13 := add a2_13 a3_13
  let y3_13 := mul (readUOffset tl (j) 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (sub a2_13 a3_13)
  let x0_14 := readUOffset b (i0) 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x1_14 := readUOffset b (i1) 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x2_14 := readUOffset b (i2) 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x3_14 := readUOffset b (i3) 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let a0_14 := add x0_14 x2_14
  let a1_14 := add x1_14 x3_14
  let a2_14 := mul (readUOffset th (j) 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (sub x0_14 x2_14)
  let a3_14 := mul (readUOffset th (j1) 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (sub x1_14 x3_14)
  let y0_14 := add a0_14 a1_14
  let y1_14 := mul (readUOffset tl (j) 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (sub a0_14 a1_14)
  let y2_14 := add a2_14 a3_14
  let y3_14 := mul (readUOffset tl (j) 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (sub a2_14 a3_14)
  let x0_15 := readUOffset b (i0) 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x1_15 := readUOffset b (i1) 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x2_15 := readUOffset b (i2) 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x3_15 := readUOffset b (i3) 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let a0_15 := add x0_15 x2_15
  let a1_15 := add x1_15 x3_15
  let a2_15 := mul (readUOffset th (j) 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (sub x0_15 x2_15)
  let a3_15 := mul (readUOffset th (j1) 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (sub x1_15 x3_15)
  let y0_15 := add a0_15 a1_15
  let y1_15 := mul (readUOffset tl (j) 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (sub a0_15 a1_15)
  let y2_15 := add a2_15 a3_15
  let y3_15 := mul (readUOffset tl (j) 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (sub a2_15 a3_15)
  let b := write16 b i0.toNat y0_0 y0_1 y0_2 y0_3 y0_4 y0_5 y0_6 y0_7 y0_8 y0_9 y0_10 y0_11 y0_12
    y0_13 y0_14 y0_15
  let b := write16 b i1.toNat y1_0 y1_1 y1_2 y1_3 y1_4 y1_5 y1_6 y1_7 y1_8 y1_9 y1_10 y1_11 y1_12
    y1_13 y1_14 y1_15
  let b := write16 b i2.toNat y2_0 y2_1 y2_2 y2_3 y2_4 y2_5 y2_6 y2_7 y2_8 y2_9 y2_10 y2_11 y2_12
    y2_13 y2_14 y2_15
  let b := write16 b i3.toNat y3_0 y3_1 y3_2 y3_3 y3_4 y3_5 y3_6 y3_7 y3_8 y3_9 y3_10 y3_11 y3_12
    y3_13 y3_14 y3_15
  b
def inner16 (th tl : ByteArray) (q j i0 i1 i2 i3 : Nat) (b : ByteArray) : ByteArray :=
  if hj : j + 16 ≤ q then
    if h : 4 * (i0 + 15) + 3 < b.size ∧
      4 * (i1 + 15) + 3 < b.size ∧
      4 * (i2 + 15) + 3 < b.size ∧
      4 * (i3 + 15) + 3 < b.size ∧
      4 * (j + q + 15) + 3 < th.size ∧
      4 * (j + 15) + 3 < tl.size ∧
      b.size < USize.size ∧
      th.size < USize.size ∧
      tl.size < USize.size then
      let b := step16 th tl (USize.ofNatLT (j) (by omega)) (USize.ofNatLT (j + q) (by omega))
        (USize.ofNatLT (i0) (by omega)) (USize.ofNatLT (i1) (by omega)) (USize.ofNatLT (i2)
        (by omega)) (USize.ofNatLT (i3) (by omega)) b (by simp only [USize.toNat_ofNatLT]; omega)
      inner16 th tl q (j + 16) (i0 + 16) (i1 + 16) (i2 + 16) (i3 + 16) b
    else inner th tl q j i0 i1 i2 i3 b
  else inner th tl q j i0 i1 i2 i3 b
termination_by q - j
decreasing_by omega
@[noinline] def leaf16 (t3 t2 t1 : @& ByteArray) (i : USize) (b : ByteArray)
    (h : 4 * (i.toNat + 15) + 3 < b.size ∧ b.size < USize.size ∧
      31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
      7 < t1.size ∧ t1.size < USize.size) : ByteArray :=
  let x0_0 := readUOffset b i 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x0_1 := readUOffset b i 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x0_2 := readUOffset b i 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x0_3 := readUOffset b i 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x0_4 := readUOffset b i 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x0_5 := readUOffset b i 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x0_6 := readUOffset b i 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x0_7 := readUOffset b i 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x0_8 := readUOffset b i 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x0_9 := readUOffset b i 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x0_10 := readUOffset b i 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x0_11 := readUOffset b i 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x0_12 := readUOffset b i 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x0_13 := readUOffset b i 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x0_14 := readUOffset b i 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x0_15 := readUOffset b i 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let w0_1 := readUOffset t3 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let w0_2 := readUOffset t3 0 2 (by
      rw [usize_numeral 0 (by decide), usize_numeral 2 (by decide)]
      omega)
  let w0_3 := readUOffset t3 0 3 (by
      rw [usize_numeral 0 (by decide), usize_numeral 3 (by decide)]
      omega)
  let w0_4 := readUOffset t3 0 4 (by
      rw [usize_numeral 0 (by decide), usize_numeral 4 (by decide)]
      omega)
  let w0_5 := readUOffset t3 0 5 (by
      rw [usize_numeral 0 (by decide), usize_numeral 5 (by decide)]
      omega)
  let w0_6 := readUOffset t3 0 6 (by
      rw [usize_numeral 0 (by decide), usize_numeral 6 (by decide)]
      omega)
  let w0_7 := readUOffset t3 0 7 (by
      rw [usize_numeral 0 (by decide), usize_numeral 7 (by decide)]
      omega)
  let x1_0 := add x0_0 x0_8
  let x1_8 := sub x0_0 x0_8
  let x1_1 := add x0_1 x0_9
  let x1_9 := mul w0_1 (sub x0_1 x0_9)
  let x1_2 := add x0_2 x0_10
  let x1_10 := mul w0_2 (sub x0_2 x0_10)
  let x1_3 := add x0_3 x0_11
  let x1_11 := mul w0_3 (sub x0_3 x0_11)
  let x1_4 := add x0_4 x0_12
  let x1_12 := mul w0_4 (sub x0_4 x0_12)
  let x1_5 := add x0_5 x0_13
  let x1_13 := mul w0_5 (sub x0_5 x0_13)
  let x1_6 := add x0_6 x0_14
  let x1_14 := mul w0_6 (sub x0_6 x0_14)
  let x1_7 := add x0_7 x0_15
  let x1_15 := mul w0_7 (sub x0_7 x0_15)
  let w1_1 := readUOffset t2 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let w1_2 := readUOffset t2 0 2 (by
      rw [usize_numeral 0 (by decide), usize_numeral 2 (by decide)]
      omega)
  let w1_3 := readUOffset t2 0 3 (by
      rw [usize_numeral 0 (by decide), usize_numeral 3 (by decide)]
      omega)
  let x2_0 := add x1_0 x1_4
  let x2_4 := sub x1_0 x1_4
  let x2_1 := add x1_1 x1_5
  let x2_5 := mul w1_1 (sub x1_1 x1_5)
  let x2_2 := add x1_2 x1_6
  let x2_6 := mul w1_2 (sub x1_2 x1_6)
  let x2_3 := add x1_3 x1_7
  let x2_7 := mul w1_3 (sub x1_3 x1_7)
  let x2_8 := add x1_8 x1_12
  let x2_12 := sub x1_8 x1_12
  let x2_9 := add x1_9 x1_13
  let x2_13 := mul w1_1 (sub x1_9 x1_13)
  let x2_10 := add x1_10 x1_14
  let x2_14 := mul w1_2 (sub x1_10 x1_14)
  let x2_11 := add x1_11 x1_15
  let x2_15 := mul w1_3 (sub x1_11 x1_15)
  let w2_1 := readUOffset t1 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let x3_0 := add x2_0 x2_2
  let x3_2 := sub x2_0 x2_2
  let x3_1 := add x2_1 x2_3
  let x3_3 := mul w2_1 (sub x2_1 x2_3)
  let x3_4 := add x2_4 x2_6
  let x3_6 := sub x2_4 x2_6
  let x3_5 := add x2_5 x2_7
  let x3_7 := mul w2_1 (sub x2_5 x2_7)
  let x3_8 := add x2_8 x2_10
  let x3_10 := sub x2_8 x2_10
  let x3_9 := add x2_9 x2_11
  let x3_11 := mul w2_1 (sub x2_9 x2_11)
  let x3_12 := add x2_12 x2_14
  let x3_14 := sub x2_12 x2_14
  let x3_13 := add x2_13 x2_15
  let x3_15 := mul w2_1 (sub x2_13 x2_15)
  let x4_0 := add x3_0 x3_1
  let x4_1 := sub x3_0 x3_1
  let x4_2 := add x3_2 x3_3
  let x4_3 := sub x3_2 x3_3
  let x4_4 := add x3_4 x3_5
  let x4_5 := sub x3_4 x3_5
  let x4_6 := add x3_6 x3_7
  let x4_7 := sub x3_6 x3_7
  let x4_8 := add x3_8 x3_9
  let x4_9 := sub x3_8 x3_9
  let x4_10 := add x3_10 x3_11
  let x4_11 := sub x3_10 x3_11
  let x4_12 := add x3_12 x3_13
  let x4_13 := sub x3_12 x3_13
  let x4_14 := add x3_14 x3_15
  let x4_15 := sub x3_14 x3_15
  write16 b i.toNat x4_0 x4_1 x4_2 x4_3 x4_4 x4_5 x4_6 x4_7 x4_8 x4_9 x4_10 x4_11 x4_12 x4_13
    x4_14 x4_15
@[noinline] def leaf16Scaled (t3 t2 t1 : @& ByteArray) (i : USize) (nInv : UInt32) (b : ByteArray)
    (h : 4 * (i.toNat + 15) + 3 < b.size ∧ b.size < USize.size ∧
      31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
      7 < t1.size ∧ t1.size < USize.size) : ByteArray :=
  let x0_0 := readUOffset b i 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x0_1 := readUOffset b i 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x0_2 := readUOffset b i 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x0_3 := readUOffset b i 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x0_4 := readUOffset b i 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x0_5 := readUOffset b i 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x0_6 := readUOffset b i 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x0_7 := readUOffset b i 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x0_8 := readUOffset b i 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x0_9 := readUOffset b i 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x0_10 := readUOffset b i 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x0_11 := readUOffset b i 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x0_12 := readUOffset b i 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x0_13 := readUOffset b i 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x0_14 := readUOffset b i 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x0_15 := readUOffset b i 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let w0_1 := readUOffset t3 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let w0_2 := readUOffset t3 0 2 (by
      rw [usize_numeral 0 (by decide), usize_numeral 2 (by decide)]
      omega)
  let w0_3 := readUOffset t3 0 3 (by
      rw [usize_numeral 0 (by decide), usize_numeral 3 (by decide)]
      omega)
  let w0_4 := readUOffset t3 0 4 (by
      rw [usize_numeral 0 (by decide), usize_numeral 4 (by decide)]
      omega)
  let w0_5 := readUOffset t3 0 5 (by
      rw [usize_numeral 0 (by decide), usize_numeral 5 (by decide)]
      omega)
  let w0_6 := readUOffset t3 0 6 (by
      rw [usize_numeral 0 (by decide), usize_numeral 6 (by decide)]
      omega)
  let w0_7 := readUOffset t3 0 7 (by
      rw [usize_numeral 0 (by decide), usize_numeral 7 (by decide)]
      omega)
  let x1_0 := add x0_0 x0_8
  let x1_8 := sub x0_0 x0_8
  let x1_1 := add x0_1 x0_9
  let x1_9 := mul w0_1 (sub x0_1 x0_9)
  let x1_2 := add x0_2 x0_10
  let x1_10 := mul w0_2 (sub x0_2 x0_10)
  let x1_3 := add x0_3 x0_11
  let x1_11 := mul w0_3 (sub x0_3 x0_11)
  let x1_4 := add x0_4 x0_12
  let x1_12 := mul w0_4 (sub x0_4 x0_12)
  let x1_5 := add x0_5 x0_13
  let x1_13 := mul w0_5 (sub x0_5 x0_13)
  let x1_6 := add x0_6 x0_14
  let x1_14 := mul w0_6 (sub x0_6 x0_14)
  let x1_7 := add x0_7 x0_15
  let x1_15 := mul w0_7 (sub x0_7 x0_15)
  let w1_1 := readUOffset t2 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let w1_2 := readUOffset t2 0 2 (by
      rw [usize_numeral 0 (by decide), usize_numeral 2 (by decide)]
      omega)
  let w1_3 := readUOffset t2 0 3 (by
      rw [usize_numeral 0 (by decide), usize_numeral 3 (by decide)]
      omega)
  let x2_0 := add x1_0 x1_4
  let x2_4 := sub x1_0 x1_4
  let x2_1 := add x1_1 x1_5
  let x2_5 := mul w1_1 (sub x1_1 x1_5)
  let x2_2 := add x1_2 x1_6
  let x2_6 := mul w1_2 (sub x1_2 x1_6)
  let x2_3 := add x1_3 x1_7
  let x2_7 := mul w1_3 (sub x1_3 x1_7)
  let x2_8 := add x1_8 x1_12
  let x2_12 := sub x1_8 x1_12
  let x2_9 := add x1_9 x1_13
  let x2_13 := mul w1_1 (sub x1_9 x1_13)
  let x2_10 := add x1_10 x1_14
  let x2_14 := mul w1_2 (sub x1_10 x1_14)
  let x2_11 := add x1_11 x1_15
  let x2_15 := mul w1_3 (sub x1_11 x1_15)
  let w2_1 := readUOffset t1 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let x3_0 := add x2_0 x2_2
  let x3_2 := sub x2_0 x2_2
  let x3_1 := add x2_1 x2_3
  let x3_3 := mul w2_1 (sub x2_1 x2_3)
  let x3_4 := add x2_4 x2_6
  let x3_6 := sub x2_4 x2_6
  let x3_5 := add x2_5 x2_7
  let x3_7 := mul w2_1 (sub x2_5 x2_7)
  let x3_8 := add x2_8 x2_10
  let x3_10 := sub x2_8 x2_10
  let x3_9 := add x2_9 x2_11
  let x3_11 := mul w2_1 (sub x2_9 x2_11)
  let x3_12 := add x2_12 x2_14
  let x3_14 := sub x2_12 x2_14
  let x3_13 := add x2_13 x2_15
  let x3_15 := mul w2_1 (sub x2_13 x2_15)
  let x4_0 := add x3_0 x3_1
  let x4_1 := sub x3_0 x3_1
  let x4_2 := add x3_2 x3_3
  let x4_3 := sub x3_2 x3_3
  let x4_4 := add x3_4 x3_5
  let x4_5 := sub x3_4 x3_5
  let x4_6 := add x3_6 x3_7
  let x4_7 := sub x3_6 x3_7
  let x4_8 := add x3_8 x3_9
  let x4_9 := sub x3_8 x3_9
  let x4_10 := add x3_10 x3_11
  let x4_11 := sub x3_10 x3_11
  let x4_12 := add x3_12 x3_13
  let x4_13 := sub x3_12 x3_13
  let x4_14 := add x3_14 x3_15
  let x4_15 := sub x3_14 x3_15
  let z0 := mul nInv x4_0
  let z1 := mul nInv x4_1
  let z2 := mul nInv x4_2
  let z3 := mul nInv x4_3
  let z4 := mul nInv x4_4
  let z5 := mul nInv x4_5
  let z6 := mul nInv x4_6
  let z7 := mul nInv x4_7
  let z8 := mul nInv x4_8
  let z9 := mul nInv x4_9
  let z10 := mul nInv x4_10
  let z11 := mul nInv x4_11
  let z12 := mul nInv x4_12
  let z13 := mul nInv x4_13
  let z14 := mul nInv x4_14
  let z15 := mul nInv x4_15
  write16 b i.toNat z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
def stages (logN : Nat) (tw : Array ByteArray) (a : ByteArray) (nInv : UInt32) (normalize : Bool) :
    ByteArray := Id.run do
  let mut a := a
  let fused := logN ≥ 4 && logN % 2 == 0
  for pass in [:(if fused then logN / 2 - 2 else logN / 2)] do
    let high := logN - 1 - 2 * pass
    let low := high - 1
    let q := 2 ^ low
    for block in [:2 ^ logN / (4 * q)] do
      let base := block * (4 * q)
      a := inner16 (tw.getD high ByteArray.empty) (tw.getD low ByteArray.empty)
        q 0 base (base + q) (base + 2 * q) (base + 3 * q) a
  if fused then
    let t3 := tw.getD 3 ByteArray.empty
    let t2 := tw.getD 2 ByteArray.empty
    let t1 := tw.getD 1 ByteArray.empty
    for block in [:2 ^ logN / 16] do
      let i := block * 16
      if h : 4 * (i + 15) + 3 < a.size ∧ a.size < USize.size ∧
          31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
          7 < t1.size ∧ t1.size < USize.size then
        if normalize then
          a := leaf16Scaled t3 t2 t1 (USize.ofNatLT i (by omega)) nInv a
            (by simpa only [USize.toNat_ofNatLT] using h)
        else
          a := leaf16 t3 t2 t1 (USize.ofNatLT i (by omega)) a
            (by simpa only [USize.toNat_ofNatLT] using h)
  if logN % 2 = 1 then
    for block in [:2 ^ logN / 2] do
      let x := read a (2 * block)
      let y := read a (2 * block + 1)
      a := write (write a (2 * block) (add x y)) (2 * block + 1) (sub x y)
  return a
@[specialize] def generate (n : Nat) (f : Nat → UInt32) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity (4 * n)
  for i in [:n] do a := push a (f i)
  return a
@[noinline] def splitStepLeft (a w : @& ByteArray) (i j : USize) (out : ByteArray)
    (h : 4 * (i.toNat + 15) + 3 < a.size ∧ 4 * (j.toNat + 15) + 3 < a.size ∧
      4 * (i.toNat + 15) + 3 < w.size ∧ a.size < USize.size ∧ w.size < USize.size) : ByteArray :=
  let y0 := add (readUOffset a i 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (readUOffset a j 0 (by
      rw [usize_numeral 0 (by decide)]
      omega))
  let y1 := add (readUOffset a i 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (readUOffset a j 1 (by
      rw [usize_numeral 1 (by decide)]
      omega))
  let y2 := add (readUOffset a i 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (readUOffset a j 2 (by
      rw [usize_numeral 2 (by decide)]
      omega))
  let y3 := add (readUOffset a i 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (readUOffset a j 3 (by
      rw [usize_numeral 3 (by decide)]
      omega))
  let y4 := add (readUOffset a i 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (readUOffset a j 4 (by
      rw [usize_numeral 4 (by decide)]
      omega))
  let y5 := add (readUOffset a i 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (readUOffset a j 5 (by
      rw [usize_numeral 5 (by decide)]
      omega))
  let y6 := add (readUOffset a i 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (readUOffset a j 6 (by
      rw [usize_numeral 6 (by decide)]
      omega))
  let y7 := add (readUOffset a i 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (readUOffset a j 7 (by
      rw [usize_numeral 7 (by decide)]
      omega))
  let y8 := add (readUOffset a i 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (readUOffset a j 8 (by
      rw [usize_numeral 8 (by decide)]
      omega))
  let y9 := add (readUOffset a i 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (readUOffset a j 9 (by
      rw [usize_numeral 9 (by decide)]
      omega))
  let y10 := add (readUOffset a i 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (readUOffset a j 10 (by
      rw [usize_numeral 10 (by decide)]
      omega))
  let y11 := add (readUOffset a i 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (readUOffset a j 11 (by
      rw [usize_numeral 11 (by decide)]
      omega))
  let y12 := add (readUOffset a i 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (readUOffset a j 12 (by
      rw [usize_numeral 12 (by decide)]
      omega))
  let y13 := add (readUOffset a i 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (readUOffset a j 13 (by
      rw [usize_numeral 13 (by decide)]
      omega))
  let y14 := add (readUOffset a i 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (readUOffset a j 14 (by
      rw [usize_numeral 14 (by decide)]
      omega))
  let y15 := add (readUOffset a i 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (readUOffset a j 15 (by
      rw [usize_numeral 15 (by decide)]
      omega))
  push16 out y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
def splitLeft (a w : ByteArray) (half : Nat) : ByteArray := Id.run do
  if half % 16 != 0 then return generate half (fun i ↦ add (read a i) (read a (i + half)))
  let mut out := ByteArray.emptyWithCapacity (4 * half)
  for block in [:half / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < a.size ∧ 4 * (i + half + 15) + 3 < a.size ∧
        4 * (i + 15) + 3 < w.size ∧ a.size < USize.size ∧ w.size < USize.size then
      out := splitStepLeft a w (USize.ofNatLT i (by omega))
        (USize.ofNatLT (i + half) (by omega)) out (by simpa only [USize.toNat_ofNatLT] using h)
    else return generate half (fun i ↦ add (read a i) (read a (i + half)))
  return out
@[noinline] def splitStepRight (a w : @& ByteArray) (i j : USize) (out : ByteArray)
    (h : 4 * (i.toNat + 15) + 3 < a.size ∧ 4 * (j.toNat + 15) + 3 < a.size ∧
      4 * (i.toNat + 15) + 3 < w.size ∧ a.size < USize.size ∧ w.size < USize.size) : ByteArray :=
  let y0 := mul (readUOffset w i 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (sub (readUOffset a i 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)) (readUOffset a j 0 (by
      rw [usize_numeral 0 (by decide)]
      omega)))
  let y1 := mul (readUOffset w i 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (sub (readUOffset a i 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)) (readUOffset a j 1 (by
      rw [usize_numeral 1 (by decide)]
      omega)))
  let y2 := mul (readUOffset w i 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (sub (readUOffset a i 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)) (readUOffset a j 2 (by
      rw [usize_numeral 2 (by decide)]
      omega)))
  let y3 := mul (readUOffset w i 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (sub (readUOffset a i 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)) (readUOffset a j 3 (by
      rw [usize_numeral 3 (by decide)]
      omega)))
  let y4 := mul (readUOffset w i 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (sub (readUOffset a i 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)) (readUOffset a j 4 (by
      rw [usize_numeral 4 (by decide)]
      omega)))
  let y5 := mul (readUOffset w i 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (sub (readUOffset a i 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)) (readUOffset a j 5 (by
      rw [usize_numeral 5 (by decide)]
      omega)))
  let y6 := mul (readUOffset w i 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (sub (readUOffset a i 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)) (readUOffset a j 6 (by
      rw [usize_numeral 6 (by decide)]
      omega)))
  let y7 := mul (readUOffset w i 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (sub (readUOffset a i 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)) (readUOffset a j 7 (by
      rw [usize_numeral 7 (by decide)]
      omega)))
  let y8 := mul (readUOffset w i 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (sub (readUOffset a i 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)) (readUOffset a j 8 (by
      rw [usize_numeral 8 (by decide)]
      omega)))
  let y9 := mul (readUOffset w i 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (sub (readUOffset a i 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)) (readUOffset a j 9 (by
      rw [usize_numeral 9 (by decide)]
      omega)))
  let y10 := mul (readUOffset w i 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (sub (readUOffset a i 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)) (readUOffset a j 10 (by
      rw [usize_numeral 10 (by decide)]
      omega)))
  let y11 := mul (readUOffset w i 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (sub (readUOffset a i 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)) (readUOffset a j 11 (by
      rw [usize_numeral 11 (by decide)]
      omega)))
  let y12 := mul (readUOffset w i 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (sub (readUOffset a i 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)) (readUOffset a j 12 (by
      rw [usize_numeral 12 (by decide)]
      omega)))
  let y13 := mul (readUOffset w i 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (sub (readUOffset a i 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)) (readUOffset a j 13 (by
      rw [usize_numeral 13 (by decide)]
      omega)))
  let y14 := mul (readUOffset w i 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (sub (readUOffset a i 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)) (readUOffset a j 14 (by
      rw [usize_numeral 14 (by decide)]
      omega)))
  let y15 := mul (readUOffset w i 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (sub (readUOffset a i 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)) (readUOffset a j 15 (by
      rw [usize_numeral 15 (by decide)]
      omega)))
  push16 out y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
def splitRight (a w : ByteArray) (half : Nat) : ByteArray := Id.run do
  if half % 16 != 0 then return generate half (fun i ↦ mul (read w i) (sub (read a i) (read a (i
    + half))))
  let mut out := ByteArray.emptyWithCapacity (4 * half)
  for block in [:half / 16] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < a.size ∧ 4 * (i + half + 15) + 3 < a.size ∧
        4 * (i + 15) + 3 < w.size ∧ a.size < USize.size ∧ w.size < USize.size then
      out := splitStepRight a w (USize.ofNatLT i (by omega))
        (USize.ofNatLT (i + half) (by omega)) out (by simpa only [USize.toNat_ofNatLT] using h)
    else return generate half (fun i ↦ mul (read w i) (sub (read a i) (read a (i + half))))
  return out
def splitTask (tw : Array ByteArray) (logN : Nat) (a : ByteArray) (nInv : UInt32) (normalize :
    Bool) : Nat → Task ByteArray
  | 0 => Task.spawn fun _ ↦ stages logN tw a nInv normalize
  | depth + 1 =>
    if logN = 0 then Task.pure a else
    let half := 2 ^ (logN - 1)
    let w := tw.getD (logN - 1) ByteArray.empty
    let left := (Task.spawn fun _ ↦ splitLeft a w half).bind
      (sync := true) (fun lo ↦ splitTask tw (logN - 1) lo nInv normalize depth)
    let right := (Task.spawn fun _ ↦ splitRight a w half).bind
      (sync := true) (fun hi ↦ splitTask tw (logN - 1) hi nInv normalize depth)
    left.bind (sync := true) fun lo ↦ right.map (sync := true) fun hi ↦ lo ++ hi
@[inline] def fieldAtOffset (a : @& Array KoalaBear.Fast.Field) (i o : USize)
    (h : i.toNat + o.toNat < a.size ∧ a.size < USize.size) : UInt32 :=
  a.uget (i + o) (by
    rw [USize.toNat_add]
    rw [Nat.mod_eq_of_lt (show i.toNat + o.toNat < USize.size by omega)]
    exact h.1) |>.val
theorem elementOffsetBound (i n o : Nat) (h : i + 15 < n) (ho : o ≤ 15) : i + o < n := by omega
theorem wordOffsetBound (i n o : Nat) (h : 4 * (i + 15) + 3 < n) (ho : o ≤ 15) :
    4 * (i + o) + 3 < n := by omega
@[noinline] def splitInputStepLeft (a : @& Array KoalaBear.Fast.Field) (i j : USize) (out :
  ByteArray)
    (h : i.toNat + 15 < a.size ∧ j.toNat + 15 < a.size ∧ a.size < USize.size) : ByteArray :=
  let x0 := fieldAtOffset a i 0 (by
      rw [usize_numeral 0 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z0 := fieldAtOffset a j 0 (by
      rw [usize_numeral 0 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y0 := add x0 z0
  let x1 := fieldAtOffset a i 1 (by
      rw [usize_numeral 1 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z1 := fieldAtOffset a j 1 (by
      rw [usize_numeral 1 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y1 := add x1 z1
  let x2 := fieldAtOffset a i 2 (by
      rw [usize_numeral 2 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z2 := fieldAtOffset a j 2 (by
      rw [usize_numeral 2 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y2 := add x2 z2
  let x3 := fieldAtOffset a i 3 (by
      rw [usize_numeral 3 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z3 := fieldAtOffset a j 3 (by
      rw [usize_numeral 3 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y3 := add x3 z3
  let x4 := fieldAtOffset a i 4 (by
      rw [usize_numeral 4 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z4 := fieldAtOffset a j 4 (by
      rw [usize_numeral 4 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y4 := add x4 z4
  let x5 := fieldAtOffset a i 5 (by
      rw [usize_numeral 5 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z5 := fieldAtOffset a j 5 (by
      rw [usize_numeral 5 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y5 := add x5 z5
  let x6 := fieldAtOffset a i 6 (by
      rw [usize_numeral 6 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z6 := fieldAtOffset a j 6 (by
      rw [usize_numeral 6 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y6 := add x6 z6
  let x7 := fieldAtOffset a i 7 (by
      rw [usize_numeral 7 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z7 := fieldAtOffset a j 7 (by
      rw [usize_numeral 7 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y7 := add x7 z7
  let x8 := fieldAtOffset a i 8 (by
      rw [usize_numeral 8 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z8 := fieldAtOffset a j 8 (by
      rw [usize_numeral 8 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y8 := add x8 z8
  let x9 := fieldAtOffset a i 9 (by
      rw [usize_numeral 9 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z9 := fieldAtOffset a j 9 (by
      rw [usize_numeral 9 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y9 := add x9 z9
  let x10 := fieldAtOffset a i 10 (by
      rw [usize_numeral 10 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z10 := fieldAtOffset a j 10 (by
      rw [usize_numeral 10 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y10 := add x10 z10
  let x11 := fieldAtOffset a i 11 (by
      rw [usize_numeral 11 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z11 := fieldAtOffset a j 11 (by
      rw [usize_numeral 11 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y11 := add x11 z11
  let x12 := fieldAtOffset a i 12 (by
      rw [usize_numeral 12 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z12 := fieldAtOffset a j 12 (by
      rw [usize_numeral 12 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y12 := add x12 z12
  let x13 := fieldAtOffset a i 13 (by
      rw [usize_numeral 13 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z13 := fieldAtOffset a j 13 (by
      rw [usize_numeral 13 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y13 := add x13 z13
  let x14 := fieldAtOffset a i 14 (by
      rw [usize_numeral 14 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z14 := fieldAtOffset a j 14 (by
      rw [usize_numeral 14 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y14 := add x14 z14
  let x15 := fieldAtOffset a i 15 (by
      rw [usize_numeral 15 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2⟩)
  let z15 := fieldAtOffset a j 15 (by
      rw [usize_numeral 15 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2⟩)
  let y15 := add x15 z15
  push16 out y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
def splitInputLeft (a : Array KoalaBear.Fast.Field) (half : Nat) : ByteArray := Id.run do
  if half % 16 != 0 then return splitLeft (encode a) ByteArray.empty half
  let mut out := ByteArray.emptyWithCapacity (4 * half)
  for block in [:half / 16] do
    let i := 16 * block
    if h : i + 15 < a.size ∧ i + half + 15 < a.size ∧ a.size < USize.size then
      out := splitInputStepLeft a (USize.ofNatLT i (by omega))
        (USize.ofNatLT (i + half) (by omega)) out (by simpa only [USize.toNat_ofNatLT] using h)
    else return splitLeft (encode a) ByteArray.empty half
  return out
@[noinline] def splitInputStepRight (a : @& Array KoalaBear.Fast.Field) (w : @& ByteArray) (i j :
  USize) (out : ByteArray)
    (h : i.toNat + 15 < a.size ∧ j.toNat + 15 < a.size ∧ a.size < USize.size ∧ 4 * (i.toNat + 15)
      + 3 < w.size ∧ w.size < USize.size) : ByteArray :=
  let x0 := fieldAtOffset a i 0 (by
      rw [usize_numeral 0 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z0 := fieldAtOffset a j 0 (by
      rw [usize_numeral 0 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y0 := mul (readUOffset w i 0 (by
      rw [usize_numeral 0 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x0 z0)
  let x1 := fieldAtOffset a i 1 (by
      rw [usize_numeral 1 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z1 := fieldAtOffset a j 1 (by
      rw [usize_numeral 1 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y1 := mul (readUOffset w i 1 (by
      rw [usize_numeral 1 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x1 z1)
  let x2 := fieldAtOffset a i 2 (by
      rw [usize_numeral 2 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z2 := fieldAtOffset a j 2 (by
      rw [usize_numeral 2 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y2 := mul (readUOffset w i 2 (by
      rw [usize_numeral 2 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x2 z2)
  let x3 := fieldAtOffset a i 3 (by
      rw [usize_numeral 3 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z3 := fieldAtOffset a j 3 (by
      rw [usize_numeral 3 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y3 := mul (readUOffset w i 3 (by
      rw [usize_numeral 3 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x3 z3)
  let x4 := fieldAtOffset a i 4 (by
      rw [usize_numeral 4 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z4 := fieldAtOffset a j 4 (by
      rw [usize_numeral 4 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y4 := mul (readUOffset w i 4 (by
      rw [usize_numeral 4 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x4 z4)
  let x5 := fieldAtOffset a i 5 (by
      rw [usize_numeral 5 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z5 := fieldAtOffset a j 5 (by
      rw [usize_numeral 5 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y5 := mul (readUOffset w i 5 (by
      rw [usize_numeral 5 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x5 z5)
  let x6 := fieldAtOffset a i 6 (by
      rw [usize_numeral 6 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z6 := fieldAtOffset a j 6 (by
      rw [usize_numeral 6 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y6 := mul (readUOffset w i 6 (by
      rw [usize_numeral 6 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x6 z6)
  let x7 := fieldAtOffset a i 7 (by
      rw [usize_numeral 7 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z7 := fieldAtOffset a j 7 (by
      rw [usize_numeral 7 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y7 := mul (readUOffset w i 7 (by
      rw [usize_numeral 7 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x7 z7)
  let x8 := fieldAtOffset a i 8 (by
      rw [usize_numeral 8 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z8 := fieldAtOffset a j 8 (by
      rw [usize_numeral 8 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y8 := mul (readUOffset w i 8 (by
      rw [usize_numeral 8 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x8 z8)
  let x9 := fieldAtOffset a i 9 (by
      rw [usize_numeral 9 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z9 := fieldAtOffset a j 9 (by
      rw [usize_numeral 9 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y9 := mul (readUOffset w i 9 (by
      rw [usize_numeral 9 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x9 z9)
  let x10 := fieldAtOffset a i 10 (by
      rw [usize_numeral 10 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z10 := fieldAtOffset a j 10 (by
      rw [usize_numeral 10 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y10 := mul (readUOffset w i 10 (by
      rw [usize_numeral 10 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x10 z10)
  let x11 := fieldAtOffset a i 11 (by
      rw [usize_numeral 11 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z11 := fieldAtOffset a j 11 (by
      rw [usize_numeral 11 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y11 := mul (readUOffset w i 11 (by
      rw [usize_numeral 11 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x11 z11)
  let x12 := fieldAtOffset a i 12 (by
      rw [usize_numeral 12 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z12 := fieldAtOffset a j 12 (by
      rw [usize_numeral 12 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y12 := mul (readUOffset w i 12 (by
      rw [usize_numeral 12 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x12 z12)
  let x13 := fieldAtOffset a i 13 (by
      rw [usize_numeral 13 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z13 := fieldAtOffset a j 13 (by
      rw [usize_numeral 13 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y13 := mul (readUOffset w i 13 (by
      rw [usize_numeral 13 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x13 z13)
  let x14 := fieldAtOffset a i 14 (by
      rw [usize_numeral 14 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z14 := fieldAtOffset a j 14 (by
      rw [usize_numeral 14 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y14 := mul (readUOffset w i 14 (by
      rw [usize_numeral 14 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x14 z14)
  let x15 := fieldAtOffset a i 15 (by
      rw [usize_numeral 15 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.1 (by decide), h.2.2.1⟩)
  let z15 := fieldAtOffset a j 15 (by
      rw [usize_numeral 15 (by decide)]
      exact ⟨elementOffsetBound _ _ _ h.2.1 (by decide), h.2.2.1⟩)
  let y15 := mul (readUOffset w i 15 (by
      rw [usize_numeral 15 (by decide)]
      exact ⟨wordOffsetBound _ _ _ h.2.2.2.1 (by decide), h.2.2.2.2⟩)) (sub x15 z15)
  push16 out y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
def splitInputRight (a : Array KoalaBear.Fast.Field) (w : ByteArray) (half : Nat) : ByteArray :=
  Id.run do
  if half % 16 != 0 then return splitRight (encode a) w half
  let mut out := ByteArray.emptyWithCapacity (4 * half)
  for block in [:half / 16] do
    let i := 16 * block
    if h : i + 15 < a.size ∧ i + half + 15 < a.size ∧ a.size < USize.size ∧ 4 * (i + 15) + 3 <
      w.size ∧ w.size < USize.size then
      out := splitInputStepRight a w (USize.ofNatLT i (by omega))
        (USize.ofNatLT (i + half) (by omega)) out (by simpa only [USize.toNat_ofNatLT] using h)
    else return splitRight (encode a) w half
  return out
/-- Perform the first split directly from the public field array. -/
def splitInputTask (tw : Array ByteArray) (logN : Nat)
    (a : Array KoalaBear.Fast.Field) (nInv : UInt32) (normalize : Bool) (depth : Nat) : Task
      ByteArray :=
  if depth = 0 ∨ logN < 6 then splitTask tw logN (encode a) nInv normalize depth else
  let half := 2 ^ (logN - 1)
  let w := tw.getD (logN - 1) ByteArray.empty
  let left := (Task.spawn fun _ ↦ splitInputLeft a half).bind
    (sync := true) fun lo ↦ splitTask tw (logN - 1) lo nInv normalize (depth - 1)
  let right := (Task.spawn fun _ ↦ splitInputRight a w half).bind
    (sync := true) fun hi ↦ splitTask tw (logN - 1) hi nInv normalize (depth - 1)
  left.bind (sync := true) fun lo ↦ right.map (sync := true) fun hi ↦ lo ++ hi
@[inline] def reverse32 (x : UInt32) : UInt32 :=
  let x : UInt32 := ((x >>> (1 : UInt32)) &&& (0x55555555 : UInt32)) ||| ((x &&& (0x55555555 :
    UInt32)) <<< (1 : UInt32))
  let x : UInt32 := ((x >>> (2 : UInt32)) &&& (0x33333333 : UInt32)) ||| ((x &&& (0x33333333 :
    UInt32)) <<< (2 : UInt32))
  let x : UInt32 := ((x >>> (4 : UInt32)) &&& (0x0f0f0f0f : UInt32)) ||| ((x &&& (0x0f0f0f0f :
    UInt32)) <<< (4 : UInt32))
  let x : UInt32 := ((x >>> (8 : UInt32)) &&& (0x00ff00ff : UInt32)) ||| ((x &&& (0x00ff00ff :
    UInt32)) <<< (8 : UInt32))
  (x >>> (16 : UInt32)) ||| (x <<< (16 : UInt32))
@[inline] def readWord (b : @& ByteArray) (i : USize) : UInt32 :=
  readRaw b i 0 true (by intro h; cases h)
@[inline] def fieldOfRaw (x : UInt32) : KoalaBear.Fast.Field := ofWord x
theorem noWrapAddThree (i : USize) (h : i ≤ i + 3) : (i + 3).toNat = i.toNat + 3 := by
  have hi := i.toNat_lt_size
  have hs := USize.le_size
  have hle := USize.le_iff_toNat_le.mp h
  have hx := USize.toNat_add i 3
  change (i + 3).toNat = (i.toNat + (3 : USize).toNat) % USize.size at hx
  have hthree : (3 : USize).toNat = 3 := by
    exact usize_numeral 3 (by decide)
  rw [hthree] at hx
  have hm : i.toNat + 3 < USize.size := by
    by_contra hn
    have hl : i.toNat + 3 < 2 * USize.size := by omega
    have hx' : (i.toNat + 3) % USize.size = i.toNat + 3 - USize.size := Nat.mod_eq_sub_mod
      (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
    rw [hx'] at hx
    omega
  simpa only [Nat.mod_eq_of_lt hm] using hx
@[inline] def setField4Slow (a : Array KoalaBear.Fast.Field) (i : USize) (x0 x1 x2 x3 :
  KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  if h : i.toNat + 3 < a.size ∧ i.toNat + 3 < USize.size then
    have h1 : (i + 1).toNat = i.toNat + 1 := Plan.usize_add_one i (by omega)
    have h2 : (i + 2).toNat = i.toNat + 2 := by
      rw [USize.toNat_add, usize_numeral 2 (by decide)]
      exact Nat.mod_eq_of_lt (show i.toNat + 2 < USize.size by omega)
    have h3 : (i + 3).toNat = i.toNat + 3 := by
      rw [USize.toNat_add, usize_numeral 3 (by decide)]
      exact Nat.mod_eq_of_lt (show i.toNat + 3 < USize.size by omega)
    let a0 := a.uset i x0 (by omega)
    have hs0 : a0.size = a.size := Array.size_uset _
    let a1 := a0.uset (i + 1) x1 (by omega)
    have hs1 : a1.size = a.size := (Array.size_uset _).trans hs0
    let a2 := a1.uset (i + 2) x2 (by omega)
    have hs2 : a2.size = a.size := (Array.size_uset _).trans hs1
    a2.uset (i + 3) x3 (by omega)
  else a
@[inline] def setField4 (a : Array KoalaBear.Fast.Field) (i : USize) (x0 x1 x2 x3 :
  KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  if hu : i ≤ i + 3 ∧ i + 3 < a.usize then
    have h3u := noWrapAddThree i hu.1
    have hsz : a.usize.toNat ≤ a.size := by
      change a.size % USize.size ≤ a.size
      exact Nat.mod_le _ _
    have hlu := USize.lt_iff_toNat_lt.mp hu.2
    have his := (i + 3).toNat_lt_size
    have h : i.toNat + 3 < a.size ∧ i.toNat + 3 < USize.size := by omega
    have h1 : (i + 1).toNat = i.toNat + 1 := Plan.usize_add_one i (by omega)
    have h2 : (i + 2).toNat = i.toNat + 2 := by
      rw [USize.toNat_add, usize_numeral 2 (by decide)]
      exact Nat.mod_eq_of_lt (show i.toNat + 2 < USize.size by omega)
    have h3 : (i + 3).toNat = i.toNat + 3 := by
      rw [USize.toNat_add, usize_numeral 3 (by decide)]
      exact Nat.mod_eq_of_lt (show i.toNat + 3 < USize.size by omega)
    let a0 := a.uset i x0 (by omega)
    have hs0 : a0.size = a.size := Array.size_uset _
    let a1 := a0.uset (i + 1) x1 (by omega)
    have hs1 : a1.size = a.size := (Array.size_uset _).trans hs0
    let a2 := a1.uset (i + 2) x2 (by omega)
    have hs2 : a2.size = a.size := (Array.size_uset _).trans hs1
    a2.uset (i + 3) x3 (by omega)
  else setField4Slow a i x0 x1 x2 x3
@[noinline] def decodeTile (b : @& ByteArray) (base stride outBase : USize) (nInv : UInt32)
  (inverse : Bool) (out : Array KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  let x0 := readWord b (base + 0 * stride)
  let x0 := fieldOfRaw (if inverse then mul nInv x0 else x0)
  let x1 := readWord b (base + 2 * stride)
  let x1 := fieldOfRaw (if inverse then mul nInv x1 else x1)
  let x2 := readWord b (base + 1 * stride)
  let x2 := fieldOfRaw (if inverse then mul nInv x2 else x2)
  let x3 := readWord b (base + 3 * stride)
  let x3 := fieldOfRaw (if inverse then mul nInv x3 else x3)
  setField4 out outBase x0 x1 x2 x3
def decode (logN : Nat) (b : ByteArray) (nInv : UInt32) (inverse : Bool) : Array
    KoalaBear.Fast.Field :=
  let shift := (32 - logN).toUInt32
  tabulate (fun i : Fin (2 ^ logN) ↦
    let j := (reverse32 i.val.toUInt32 >>> shift).toNat
    let x := read b j
    let x := if inverse then mul nInv x else x
    if h : x.toNat < KoalaBear.fieldSize then ⟨x, h⟩ else 0)
def decodeTiled (logN : Nat) (b : ByteArray) (nInv : UInt32) (inverse : Bool) : Array
    KoalaBear.Fast.Field := Id.run do
  if logN < 6 then return decode logN b nInv inverse
  let n := 2 ^ logN
  let stride := (n / 4).toUSize
  let shift := (32 - (logN - 6)).toUInt32
  let mut out := Array.replicate n (0 : KoalaBear.Fast.Field)
  for m in [:n / 64] do
    let revM := if logN == 6 then 0 else (reverse32 m.toUInt32 >>> shift).toNat
    for d in [:16] do
      let outBase := (reverse32 d.toUInt32 >>> (28 : UInt32)).toNat.toUSize * (n / 16).toUSize +
        (revM * 4).toUSize
      out := decodeTile b (m * 16 + d).toUSize stride outBase nInv inverse out
  return out
def splitChunks (tw : Array ByteArray) (logN : Nat) (a : ByteArray) (nInv : UInt32) (normalize :
    Bool) : Nat → Task (Array ByteArray)
  | 0 => Task.spawn fun _ ↦ #[stages logN tw a nInv normalize]
  | depth + 1 =>
    if logN = 0 then Task.pure #[a] else
    let half := 2 ^ (logN - 1)
    let w := tw.getD (logN - 1) ByteArray.empty
    let left := (Task.spawn fun _ ↦ splitLeft a w half).bind
      (sync := true) (fun lo ↦ splitChunks tw (logN - 1) lo nInv normalize depth)
    let right := (Task.spawn fun _ ↦ splitRight a w half).bind
      (sync := true) (fun hi ↦ splitChunks tw (logN - 1) hi nInv normalize depth)
    left.bind (sync := true) fun lo ↦ right.map (sync := true) fun hi ↦ lo ++ hi
def splitInputChunks (tw : Array ByteArray) (logN : Nat)
    (a : Array KoalaBear.Fast.Field) (nInv : UInt32) (normalize : Bool) (depth : Nat) : Task
      (Array ByteArray) :=
  if depth = 0 ∨ logN < 6 then splitChunks tw logN (encode a) nInv normalize depth else
  let half := 2 ^ (logN - 1)
  let w := tw.getD (logN - 1) ByteArray.empty
  let left := (Task.spawn fun _ ↦ splitInputLeft a half).bind
    (sync := true) fun lo ↦ splitChunks tw (logN - 1) lo nInv normalize (depth - 1)
  let right := (Task.spawn fun _ ↦ splitInputRight a w half).bind
    (sync := true) fun hi ↦ splitChunks tw (logN - 1) hi nInv normalize (depth - 1)
  left.bind (sync := true) fun lo ↦ right.map (sync := true) fun hi ↦ lo ++ hi
/-- Flatten the collected buffers in task order, with one preallocated destination. -/
@[inline] def assembleChunks (capacity : Nat) (chunks : Array ByteArray) : ByteArray :=
  chunks.foldl (fun acc chunk ↦ acc ++ chunk) (ByteArray.emptyWithCapacity capacity)
/-- Buffer capacity does not affect the mathematical contents. -/
theorem assembleChunks_capacity (capacity : Nat) (chunks : Array ByteArray) :
    assembleChunks capacity chunks = assembleChunks 0 chunks := by
  simp only [assembleChunks, ByteArray.emptyWithCapacity]
private theorem foldWords_start (xs : List ByteArray) (a : ByteArray) :
    xs.foldl (fun acc chunk ↦ acc ++ chunk) a =
      a ++ xs.foldl (fun acc chunk ↦ acc ++ chunk) ByteArray.empty := by
  induction xs generalizing a with
  | nil => simp only [List.foldl_nil, ByteArray.append_empty]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (a ++ x), ih (ByteArray.empty ++ x)]
    simp only [ByteArray.empty_append, ByteArray.append_assoc]
/-- Collecting references then flattening preserves each task-tree join. -/
theorem assembleChunks_append (xs ys : Array ByteArray) :
    assembleChunks 0 (xs ++ ys) = assembleChunks 0 xs ++ assembleChunks 0 ys := by
  change (xs ++ ys).foldl (fun acc chunk ↦ acc ++ chunk) ByteArray.empty =
    xs.foldl (fun acc chunk ↦ acc ++ chunk) ByteArray.empty ++
      ys.foldl (fun acc chunk ↦ acc ++ chunk) ByteArray.empty
  rw [Array.foldl_append]
  simp only [← Array.foldl_toList]
  exact foldWords_start ys.toList _
/-- The collected task tree agrees with the original packed-buffer tree. -/
theorem splitChunks_eq (tw : Array ByteArray) (logN : Nat) (a : ByteArray)
    (nInv : UInt32) (normalize : Bool) (depth : Nat) :
    assembleChunks 0 (splitChunks tw logN a nInv normalize depth).get =
      (splitTask tw logN a nInv normalize depth).get := by
  induction depth generalizing logN a with
  | zero => simp only [splitChunks, splitTask, Task.spawn, assembleChunks,
      ← Array.foldl_toList, List.foldl_cons, List.foldl_nil, ByteArray.empty_append,
      ByteArray.emptyWithCapacity_eq_empty]
  | succ depth ih =>
    rw [splitChunks, splitTask]
    split
    · simp only [assembleChunks, ← Array.foldl_toList,
        List.foldl_cons, List.foldl_nil, ByteArray.empty_append,
          ByteArray.emptyWithCapacity_eq_empty]
    · simp only [Task.bind, Task.map, Task.spawn, assembleChunks_append, ih]
/-- Fused input splitting also agrees before any output conversion. -/
theorem splitInputChunks_eq (tw : Array ByteArray) (logN : Nat)
    (a : Array KoalaBear.Fast.Field) (nInv : UInt32) (normalize : Bool) (depth : Nat) :
    assembleChunks 0 (splitInputChunks tw logN a nInv normalize depth).get =
      (splitInputTask tw logN a nInv normalize depth).get := by
  simp only [splitInputChunks, splitInputTask]
  split
  · exact splitChunks_eq ..
  · simp only [Task.bind, Task.map, Task.spawn, assembleChunks_append, splitChunks_eq]
def run (tw : Array ByteArray) (logN depth : Nat)
    (nInv : UInt32) (a : Array KoalaBear.Fast.Field) (inverse : Bool) : Array
      KoalaBear.Fast.Field :=
  let normalize := inverse && logN - depth ≥ 4 && (logN - depth) % 2 == 0
  let chunks := (splitInputChunks tw logN a nInv normalize depth).get
  let b := chunks.foldl (fun acc chunk ↦ acc ++ chunk) (ByteArray.emptyWithCapacity (4 * 2 ^ logN))
  decodeTiled logN b nInv (inverse && !normalize)
/-- Output conversion receives exactly the same packed coefficients as before collection. -/
theorem run_eq_before_collection (tw : Array ByteArray)
    (logN depth : Nat) (nInv : UInt32) (a : Array KoalaBear.Fast.Field) (inverse : Bool) :
    run tw logN depth nInv a inverse =
      let normalize := inverse && logN - depth ≥ 4 && (logN - depth) % 2 == 0
      decodeTiled logN (splitInputTask tw logN a nInv normalize depth).get
        nInv (inverse && !normalize) := by
  let normalize := inverse && logN - depth ≥ 4 && (logN - depth) % 2 == 0
  change decodeTiled logN
    (assembleChunks (4 * 2 ^ logN) (splitInputChunks tw logN a nInv normalize depth).get)
    nInv (inverse && !normalize) = _
  rw [assembleChunks_capacity, splitInputChunks_eq]
end CompPoly.CPolynomial.NTTFast.Packed.Native
