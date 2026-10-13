/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module
public import CompPoly.Univariate.NTTFast.Packed.Arithmetic
public import CompPoly.Data.ByteArray.Packed
public import CompPoly.Univariate.NTTFast.Natural
public import CompPoly.Univariate.NTTFast.Reverse32
/-! # Packed native-storage KoalaBear FFT kernels
All arithmetic, scheduling and storage are Lean. Packed words are read and written with the
`ByteArray` little-endian `UInt32` accessors of `CompPoly.Data.ByteArray.Pack`, Lean core's
proposed `ugetUInt32LE` / `usetUInt32LE`.
-/
@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open CompPoly.PackedRepr (encode)
theorem usize_numeral (n : Nat) (h : n < 4294967296) :
    (OfNat.ofNat n : USize).toNat = n := by
  rw [USize.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le h USize.le_size)
/-- A proved byte range rules out wrapping in the machine-sized byte offset. -/
theorem wordOffset_toNat (i o : USize) (h : 4 * (i.toNat + o.toNat) + 3 < USize.size) :
    ((i + o) * 4).toNat = 4 * (i.toNat + o.toNat) := by
  have hn : i.toNat + o.toNat < USize.size := by omega
  rw [USize.toNat_mul, USize.toNat_add, Nat.mod_eq_of_lt hn,
    usize_numeral 4 (by decide), Nat.mod_eq_of_lt (show (i.toNat + o.toNat) * 4 < USize.size by
      omega)]
  omega
/-- Store word `k` of a batch at byte offset `off + d`, `d = 4 k`, when `k < c`, keeping the
size. -/
@[inline] def putWord {n : Nat} (s : {x : ByteArray // x.size = n}) (off : USize) (c k : Nat)
    (d : USize) (hd : d.toNat = 4 * k) (v : UInt32)
    (h : off.toNat + 4 * c ≤ n ∧ off.toNat + 4 * c < USize.size) :
    {x : ByteArray // x.size = n} :=
  if hk : k < c then
    have hu : (off + d).toNat = off.toNat + 4 * k := by
      have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
      rw [USize.toNat_add, hd, hsize, Nat.mod_eq_of_lt (by omega)]
    ⟨s.1.usetUInt32LE (off + d) v (by rw [hu, s.2]; omega),
      by rw [ByteArray.size_usetUInt32LE, s.2]⟩
  else s
/-- Store the first `c` of sixteen words from byte offset `off`. -/
@[inline] def putWords {n : Nat} (s : {x : ByteArray // x.size = n}) (off : USize) (c : Nat)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32)
    (h : off.toNat + 4 * c ≤ n ∧ off.toNat + 4 * c < USize.size) : ByteArray :=
  let s := putWord s off c 0 0 (by rw [usize_numeral _ (by decide)]) v0 h
  let s := putWord s off c 1 4 (by rw [usize_numeral _ (by decide)]) v1 h
  let s := putWord s off c 2 8 (by rw [usize_numeral _ (by decide)]) v2 h
  let s := putWord s off c 3 12 (by rw [usize_numeral _ (by decide)]) v3 h
  let s := putWord s off c 4 16 (by rw [usize_numeral _ (by decide)]) v4 h
  let s := putWord s off c 5 20 (by rw [usize_numeral _ (by decide)]) v5 h
  let s := putWord s off c 6 24 (by rw [usize_numeral _ (by decide)]) v6 h
  let s := putWord s off c 7 28 (by rw [usize_numeral _ (by decide)]) v7 h
  let s := putWord s off c 8 32 (by rw [usize_numeral _ (by decide)]) v8 h
  let s := putWord s off c 9 36 (by rw [usize_numeral _ (by decide)]) v9 h
  let s := putWord s off c 10 40 (by rw [usize_numeral _ (by decide)]) v10 h
  let s := putWord s off c 11 44 (by rw [usize_numeral _ (by decide)]) v11 h
  let s := putWord s off c 12 48 (by rw [usize_numeral _ (by decide)]) v12 h
  let s := putWord s off c 13 52 (by rw [usize_numeral _ (by decide)]) v13 h
  let s := putWord s off c 14 56 (by rw [usize_numeral _ (by decide)]) v14 h
  (putWord s off c 15 60 (by rw [usize_numeral _ (by decide)]) v15 h).1
theorem size_putWords {n : Nat} (s : {x : ByteArray // x.size = n}) (off : USize) (c : Nat)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) (h) :
    (putWords s off c v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 h).size = n := by
  unfold putWords
  dsimp only
  exact (putWord _ off c 15 60 (by rw [usize_numeral _ (by decide)]) v15 h).property
theorem toNat_usize_le (b : ByteArray) : b.usize.toNat ≤ b.size := by
  simp only [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat']
  exact Nat.mod_le _ _
/-- `x + y` does not wrap. -/
theorem usize_add_toNat_of_le (x y : USize) (h : x ≤ x + y) :
    (x + y).toNat = x.toNat + y.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.le_iff_toNat_le, USize.toNat_add, hsize] at h
  rw [USize.toNat_add, hsize]
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  by_cases hlt : x.toNat + y.toNat < USize.size
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
/-- Overwrite at most sixteen little-endian words, preserving shared inputs. The range checks run
on machine words. -/
@[inline] def storeWords (b : ByteArray) (offset : USize) (count : UInt8)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) : ByteArray :=
  if hc : count.toNat > 16 then b else
  have h4 : (4 * count.toNat).toUSize.toNat = 4 * count.toNat :=
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)
  if h : offset ≤ offset + (4 * count.toNat).toUSize ∧
      offset + (4 * count.toNat).toUSize ≤ b.usize then
    have hn := usize_add_toNat_of_le _ _ h.1
    have hb := toNat_usize_le b
    have he := USize.le_iff_toNat_le.mp h.2
    putWords ⟨b, rfl⟩ offset count.toNat v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
      ⟨by omega, by have := (offset + (4 * count.toNat).toUSize).toNat_lt_size; omega⟩
  else b
/-- Word `i + o`, or zero unless its four bytes are in range. -/
@[inline] def readAt (b : @& ByteArray) (i o : USize) : UInt32 :=
  if h : 4 ≤ b.usize ∧ (i + o) * 4 ≤ b.usize - 4 then
    b.ugetUInt32LE ((i + o) * 4) (by
      have hb := toNat_usize_le b
      rw [USize.le_iff_toNat_le, USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h.1] at h
      rw [usize_numeral 4 (by decide)] at h
      omega)
  else 0
/-- Ordinary reads use the checked word read. -/
@[inline] def read (b : @& ByteArray) (i : @& Nat) : UInt32 :=
  readAt b i.toUSize 0
/-- Single-word writes use the same batch storage primitive. -/
@[inline] def write (b : ByteArray) (i : @& Nat) (v : UInt32) : ByteArray :=
  storeWords b (i.toUSize * 4) 1 v 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
/-- Overwrite sixteen words from word index `i`. -/
@[inline] def write16U (b : ByteArray) (i : USize) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  v14 v15 : UInt32) : ByteArray :=
  storeWords b (i * 4) 16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
/-- A buffer of `n` zero words, for kernels that store their output words in place. -/
def zeroWords (n : Nat) : ByteArray := ByteArray.zeros (4 * n)
/-- Store `f i` up to `f (i + n - 1)` at words `i` up to `i + n - 1`. -/
@[specialize] def generateGo (f : Nat → UInt32) : Nat → Nat → ByteArray → ByteArray
  | 0, _, b => b
  | n + 1, i, b => generateGo f n (i + 1) (write b i (f i))
/-- The words `f 0, …, f (n - 1)`, overwriting a zero buffer word by word. -/
@[specialize] def generate (n : Nat) (f : Nat → UInt32) : ByteArray :=
  if 4 * n < USize.size then generateGo f n 0 (zeroWords n)
  else encode (Array.ofFn fun i : Fin n ↦ f i.val)
/-- Pack a field array. -/
def encodeFields (a : Array KoalaBear.Fast.Field) : ByteArray :=
  generate a.size fun i ↦ (a.getD i 0).val
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
  b.ugetUInt32LE ((i + o) * 4) (by rw [wordOffset_toNat i o (by omega)]; omega)
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
  let b := write16U b i0 y0_0 y0_1 y0_2 y0_3 y0_4 y0_5 y0_6 y0_7 y0_8 y0_9 y0_10 y0_11 y0_12
    y0_13 y0_14 y0_15
  let b := write16U b i1 y1_0 y1_1 y1_2 y1_3 y1_4 y1_5 y1_6 y1_7 y1_8 y1_9 y1_10 y1_11 y1_12
    y1_13 y1_14 y1_15
  let b := write16U b i2 y2_0 y2_1 y2_2 y2_3 y2_4 y2_5 y2_6 y2_7 y2_8 y2_9 y2_10 y2_11 y2_12
    y2_13 y2_14 y2_15
  let b := write16U b i3 y3_0 y3_1 y3_2 y3_3 y3_4 y3_5 y3_6 y3_7 y3_8 y3_9 y3_10 y3_11 y3_12
    y3_13 y3_14 y3_15
  b
/-- Batch stores keep the buffer size. -/
theorem size_storeWords (b : ByteArray) (offset : USize) (count : UInt8)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32) :
    (storeWords b offset count v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
      v15).size = b.size := by
  unfold storeWords
  split
  · rfl
  · split
    · exact size_putWords _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · rfl

/-- The sixteen-cell kernel keeps the buffer size. -/
theorem size_step16 (th tl : ByteArray) (j j1 i0 i1 i2 i3 : USize) (b : ByteArray) (h) :
    (step16 th tl j j1 i0 i1 i2 i3 b h).size = b.size := by
  unfold step16
  simp only [write16U, size_storeWords]

/-- Advancing a machine index by one batch inside a buffer cannot wrap. -/
theorem usize_add16 (i : USize) (n : Nat) (h : i.toNat + 16 ≤ n) (hn : n < USize.size) :
    (i + 16).toNat = i.toNat + 16 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  simp only [USize.toNat_add, USize.reduceToNat, hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- `n` sixteen-cell batches at machine indices whose ranges were checked once. -/
def inner16Loop (th tl : @& ByteArray) : (n : Nat) → (j j1 i0 i1 i2 i3 : USize) →
    (b : ByteArray) → 4 * (i0.toNat + 16 * n) ≤ b.size ∧ 4 * (i1.toNat + 16 * n) ≤ b.size ∧
      4 * (i2.toNat + 16 * n) ≤ b.size ∧ 4 * (i3.toNat + 16 * n) ≤ b.size ∧
      4 * (j1.toNat + 16 * n) ≤ th.size ∧ 4 * (j.toNat + 16 * n) ≤ th.size ∧
      4 * (j.toNat + 16 * n) ≤ tl.size ∧ b.size < USize.size ∧ th.size < USize.size ∧
      tl.size < USize.size → ByteArray
  | 0, _, _, _, _, _, _, b, _ => b
  | n + 1, j, j1, i0, i1, i2, i3, b, h =>
    let b' := step16 th tl j j1 i0 i1 i2 i3 b (by omega)
    inner16Loop th tl n (j + 16) (j1 + 16) (i0 + 16) (i1 + 16) (i2 + 16) (i3 + 16) b' (by
      have hs : b'.size = b.size := size_step16 ..
      have hb := h.2.2.2.2.2.2.2.1
      have ht := h.2.2.2.2.2.2.2.2.1
      rw [hs, usize_add16 j th.size (by omega) ht, usize_add16 j1 th.size (by omega) ht,
        usize_add16 i0 b.size (by omega) hb, usize_add16 i1 b.size (by omega) hb,
        usize_add16 i2 b.size (by omega) hb, usize_add16 i3 b.size (by omega) hb]
      omega)

/-- The radix-four inner loop: whole sixteen-cell batches after one range check, then the
scalar tail. -/
def inner16 (th tl : ByteArray) (q j i0 i1 i2 i3 : Nat) (b : ByteArray) : ByteArray :=
  let n := (q - j) / 16
  if h : 4 * (i0 + 16 * n) ≤ b.size ∧ 4 * (i1 + 16 * n) ≤ b.size ∧
      4 * (i2 + 16 * n) ≤ b.size ∧ 4 * (i3 + 16 * n) ≤ b.size ∧
      4 * (j + q + 16 * n) ≤ th.size ∧ 4 * (j + 16 * n) ≤ th.size ∧
      4 * (j + 16 * n) ≤ tl.size ∧ b.size < USize.size ∧ th.size < USize.size ∧
      tl.size < USize.size then
    inner th tl q (j + 16 * n) (i0 + 16 * n) (i1 + 16 * n) (i2 + 16 * n) (i3 + 16 * n)
      (inner16Loop th tl n (USize.ofNatLT j (by omega)) (USize.ofNatLT (j + q) (by omega))
        (USize.ofNatLT i0 (by omega)) (USize.ofNatLT i1 (by omega))
        (USize.ofNatLT i2 (by omega)) (USize.ofNatLT i3 (by omega)) b
        (by simp only [USize.toNat_ofNatLT]; exact h))
  else inner th tl q j i0 i1 i2 i3 b
/-- Sixteen radix-two DIF butterflies between the words from `i0` and from `i1`, with twiddles
from word `j` of `w`. -/
@[noinline] def pair16 (w : @& ByteArray) (j i0 i1 : USize) (b : ByteArray)
    (h : 4 * (i0.toNat + 15) + 3 < b.size ∧ 4 * (i1.toNat + 15) + 3 < b.size ∧
      4 * (j.toNat + 15) + 3 < w.size ∧ b.size < USize.size ∧ w.size < USize.size) :
    ByteArray :=
  let x0 := readUOffset b i0 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let y0 := readUOffset b i1 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let w0 := readUOffset w j 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1 := readUOffset b i0 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let y1 := readUOffset b i1 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let w1 := readUOffset w j 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2 := readUOffset b i0 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let y2 := readUOffset b i1 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let w2 := readUOffset w j 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3 := readUOffset b i0 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let y3 := readUOffset b i1 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let w3 := readUOffset w j 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x4 := readUOffset b i0 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let y4 := readUOffset b i1 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let w4 := readUOffset w j 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x5 := readUOffset b i0 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let y5 := readUOffset b i1 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let w5 := readUOffset w j 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x6 := readUOffset b i0 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let y6 := readUOffset b i1 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let w6 := readUOffset w j 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x7 := readUOffset b i0 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let y7 := readUOffset b i1 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let w7 := readUOffset w j 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x8 := readUOffset b i0 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let y8 := readUOffset b i1 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let w8 := readUOffset w j 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x9 := readUOffset b i0 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let y9 := readUOffset b i1 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let w9 := readUOffset w j 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x10 := readUOffset b i0 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let y10 := readUOffset b i1 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let w10 := readUOffset w j 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x11 := readUOffset b i0 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let y11 := readUOffset b i1 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let w11 := readUOffset w j 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x12 := readUOffset b i0 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let y12 := readUOffset b i1 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let w12 := readUOffset w j 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x13 := readUOffset b i0 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let y13 := readUOffset b i1 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let w13 := readUOffset w j 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x14 := readUOffset b i0 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let y14 := readUOffset b i1 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let w14 := readUOffset w j 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x15 := readUOffset b i0 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let y15 := readUOffset b i1 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let w15 := readUOffset w j 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let b := write16U b i0
    (add x0 y0) (add x1 y1) (add x2 y2) (add x3 y3) (add x4 y4) (add x5 y5) (add x6 y6) (add x7 y7)
    (add x8 y8) (add x9 y9) (add x10 y10) (add x11 y11) (add x12 y12) (add x13 y13) (add x14 y14)
    (add x15 y15)
  write16U b i1
    (mul w0 (sub x0 y0)) (mul w1 (sub x1 y1)) (mul w2 (sub x2 y2)) (mul w3 (sub x3 y3))
    (mul w4 (sub x4 y4)) (mul w5 (sub x5 y5)) (mul w6 (sub x6 y6)) (mul w7 (sub x7 y7))
    (mul w8 (sub x8 y8)) (mul w9 (sub x9 y9)) (mul w10 (sub x10 y10)) (mul w11 (sub x11 y11))
    (mul w12 (sub x12 y12)) (mul w13 (sub x13 y13)) (mul w14 (sub x14 y14)) (mul w15 (sub x15 y15))

theorem size_pair16 (w : ByteArray) (j i0 i1 : USize) (b : ByteArray) (h) :
    (pair16 w j i0 i1 b h).size = b.size := by
  unfold pair16
  simp only [write16U, size_storeWords]

/-- `n` batches of sixteen radix-two butterflies after one range check. -/
def pair16Loop (w : @& ByteArray) : (n : Nat) → (j i0 i1 : USize) → (b : ByteArray) →
    4 * (i0.toNat + 16 * n) ≤ b.size ∧ 4 * (i1.toNat + 16 * n) ≤ b.size ∧
      4 * (j.toNat + 16 * n) ≤ w.size ∧ b.size < USize.size ∧ w.size < USize.size → ByteArray
  | 0, _, _, _, b, _ => b
  | n + 1, j, i0, i1, b, h =>
    let b' := pair16 w j i0 i1 b (by omega)
    pair16Loop w n (j + 16) (i0 + 16) (i1 + 16) b' (by
      have hs : b'.size = b.size := size_pair16 ..
      rw [hs, usize_add16 j w.size (by omega) h.2.2.2.2, usize_add16 i0 b.size (by omega) h.2.2.2.1,
        usize_add16 i1 b.size (by omega) h.2.2.2.1]
      omega)

/-- Radix-two DIF butterflies `j, …, q - 1` between the words from `i0` and from `i1`, with
twiddles from word `j` of `w`: the scalar loop. -/
def pairInner (w : @& ByteArray) (q j i0 i1 : Nat) (b : ByteArray) : ByteArray :=
  if j < q then
    let x := read b i0
    let y := read b i1
    pairInner w q (j + 1) (i0 + 1) (i1 + 1)
      (write (write b i0 (add x y)) i1 (mul (read w j) (sub x y)))
  else b
termination_by q - j

/-- The radix-two inner loop: whole sixteen-butterfly batches after one range check, then the
scalar tail. -/
def pairs (w : @& ByteArray) (q j i0 i1 : Nat) (b : ByteArray) : ByteArray :=
  let n := (q - j) / 16
  if h : 4 * (i0 + 16 * n) ≤ b.size ∧ 4 * (i1 + 16 * n) ≤ b.size ∧ 4 * (j + 16 * n) ≤ w.size ∧
      b.size < USize.size ∧ w.size < USize.size then
    pairInner w q (j + 16 * n) (i0 + 16 * n) (i1 + 16 * n)
      (pair16Loop w n (USize.ofNatLT j (by omega)) (USize.ofNatLT i0 (by omega))
        (USize.ofNatLT i1 (by omega)) b (by simp only [USize.toNat_ofNatLT]; exact h))
  else pairInner w q j i0 i1 b
@[inline] def readWord (b : @& ByteArray) (i : USize) : UInt32 :=
  readAt b i 0
def decode (logN : Nat) (b : ByteArray) (nInv : UInt32) (inverse : Bool) : Array
    KoalaBear.Fast.Field :=
  let shift := (32 - logN).toUInt32
  tabulate (fun i : Fin (2 ^ logN) ↦
    let j := (reverse32 i.val.toUInt32 >>> shift).toNat
    let x := read b j
    let x := if inverse then mul nInv x else x
    if h : x.toNat < KoalaBear.fieldSize then ⟨x, h⟩ else 0)
end CompPoly.CPolynomial.NTTFast.Packed.Native
