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
import CompPoly.Univariate.NTTFast.Packed.Unrolled
/-! # Packed native-storage FFT kernels over 32-bit Montgomery fields
All arithmetic, scheduling and storage are Lean. Packed words are read and written with the
`ByteArray` little-endian `UInt32` accessors of `CompPoly.Data.ByteArray.Pack`, Lean core's
proposed `ugetUInt32LE` / `usetUInt32LE`.
-/
@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

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
/-- A buffer of `n` bytes. -/
abbrev Buf (n : Nat) : Type := { x : ByteArray // x.size = n }

/-- Overwrite eight words of a buffer from byte offset `o`, with the range proved instead of
checked. -/
@[inline] def store8 {n : Nat} (b : Buf n) (o : USize) (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32)
    (h : o.toNat + 4 * 8 ≤ n ∧ o.toNat + 4 * 8 < USize.size) : Buf n :=
  ⟨putWords b o 8 v0 v1 v2 v3 v4 v5 v6 v7 0 0 0 0 0 0 0 0 h, size_putWords ..⟩

/-- The proved store is the checked one. -/
theorem store8_val {n : Nat} (b : Buf n) (o : USize) (v0 v1 v2 v3 v4 v5 v6 v7 : UInt32) (h)
    (hs : n < USize.size) :
    (store8 b o v0 v1 v2 v3 v4 v5 v6 v7 h).1 =
      storeWords b.1 o 8 v0 v1 v2 v3 v4 v5 v6 v7 0 0 0 0 0 0 0 0 := by
  obtain ⟨b, rfl⟩ := b
  have h8 : (8 : UInt8).toNat = 8 := rfl
  have h32 : (32 : Nat).toUSize.toNat = 32 :=
    USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)
  have hu : b.usize.toNat = b.size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]
  have hadd : (o + (32 : Nat).toUSize).toNat = o.toNat + 32 := by
    have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
    rw [USize.toNat_add, h32, hsize, Nat.mod_eq_of_lt (by omega)]
  unfold storeWords
  split
  · rename_i hc
    rw [h8] at hc
    omega
  · split
    · simp only [h8, store8]
    · rename_i hn
      exfalso
      apply hn
      rw [h8, USize.le_iff_toNat_le, USize.le_iff_toNat_le, hadd, hu]
      omega

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
def encodeFields (a : Array (FastField p)) : ByteArray :=
  generate a.size fun i ↦ (a.getD i 0).val
@[specialize]
def inner (p : ℕ) [Mont32Field p] (th tl : ByteArray) (q j i0 i1 i2 i3 : Nat)
    (b : ByteArray) : ByteArray :=
  if j < q then
    let x0 := read b i0
    let x1 := read b i1
    let x2 := read b i2
    let x3 := read b i3
    let a0 := add p x0 x2
    let a1 := add p x1 x3
    let a2 := mul p (read th j) (sub p x0 x2)
    let a3 := mul p (read th (j + q)) (sub p x1 x3)
    let b := write b i0 (add p a0 a1)
    let b := write b i1 (mul p (read tl j) (sub p a0 a1))
    let b := write b i2 (add p a2 a3)
    let b := write b i3 (mul p (read tl j) (sub p a2 a3))
    inner p th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) b
  else b
termination_by q - j
decreasing_by omega
@[inline] def readUOffset (b : @& ByteArray) (i : USize) (o : USize)
    (h : 4 * (i.toNat + o.toNat) + 3 < b.size ∧ b.size < USize.size) : UInt32 :=
  b.ugetUInt32LE ((i + o) * 4) (by rw [wordOffset_toNat i o (by omega)]; omega)
/-- The word at byte offset `o` of `b` written back unchanged. The result is exclusive, so a
kernel that starts from it lets the compiler drop the exclusivity checks of its later stores: its
loads then interleave with them instead of being held, spilled, until the first one. -/
@[inline] def touch (b : ByteArray) (o : USize) (h : o.toNat + 4 ≤ b.size) : Buf b.size :=
  ⟨b.usetUInt32LE o (b.ugetUInt32LE o h) h, ByteArray.size_usetUInt32LE ..⟩

theorem touch_eq (b : ByteArray) (o : USize) (h) : (touch b o h).1 = b :=
  PackedRepr.setUInt32LE!_getUInt32LE! b o.toNat h

/-- The last word of a buffer of at least four bytes fits it. -/
theorem lastWord_bound (b : ByteArray) (h : 4 ≤ b.usize) : (b.usize - 4).toNat + 4 ≤ b.size := by
  have hb := toNat_usize_le b
  rw [USize.le_iff_toNat_le, usize_numeral 4 (by decide)] at h
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, usize_numeral 4 (by decide)]; omega),
    usize_numeral 4 (by decide)]
  omega

/-- The buffer with its last word written back unchanged: exclusive, like `touch`, and away from
the words a kernel reads, so that its loads do not wait for the store. -/
@[inline] def touchLast (b : ByteArray) (h : 4 ≤ b.usize) : Buf b.size :=
  touch b (b.usize - 4) (lastWord_bound b h)

@[noinline, specialize]
def step16 (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (j j1 i0 i1 i2 i3 : USize) (b : ByteArray)
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
  step16_words%
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
    (step16 p th tl j j1 i0 i1 i2 i3 b h).size = b.size := by
  unfold step16
  simp only [write16U, size_storeWords]

/-- Advancing a machine index by one batch inside a buffer cannot wrap. -/
theorem usize_add16 (i : USize) (n : Nat) (h : i.toNat + 16 ≤ n) (hn : n < USize.size) :
    (i + 16).toNat = i.toNat + 16 := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  simp only [USize.toNat_add, USize.reduceToNat, hsize]
  exact Nat.mod_eq_of_lt (by omega)

/-- `n` sixteen-cell batches at machine indices whose ranges were checked once. -/
@[specialize]
def inner16Loop (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) : (n : Nat) →
    (j j1 i0 i1 i2 i3 : USize) →
    (b : ByteArray) → 4 * (i0.toNat + 16 * n) ≤ b.size ∧ 4 * (i1.toNat + 16 * n) ≤ b.size ∧
      4 * (i2.toNat + 16 * n) ≤ b.size ∧ 4 * (i3.toNat + 16 * n) ≤ b.size ∧
      4 * (j1.toNat + 16 * n) ≤ th.size ∧ 4 * (j.toNat + 16 * n) ≤ th.size ∧
      4 * (j.toNat + 16 * n) ≤ tl.size ∧ b.size < USize.size ∧ th.size < USize.size ∧
      tl.size < USize.size → ByteArray
  | 0, _, _, _, _, _, _, b, _ => b
  | n + 1, j, j1, i0, i1, i2, i3, b, h =>
    let b' := step16 p th tl j j1 i0 i1 i2 i3 b (by omega)
    inner16Loop p th tl n (j + 16) (j1 + 16) (i0 + 16) (i1 + 16) (i2 + 16) (i3 + 16) b' (by
      have hs : b'.size = b.size := size_step16 ..
      have hb := h.2.2.2.2.2.2.2.1
      have ht := h.2.2.2.2.2.2.2.2.1
      rw [hs, usize_add16 j th.size (by omega) ht, usize_add16 j1 th.size (by omega) ht,
        usize_add16 i0 b.size (by omega) hb, usize_add16 i1 b.size (by omega) hb,
        usize_add16 i2 b.size (by omega) hb, usize_add16 i3 b.size (by omega) hb]
      omega)

/-- The batch loop keeps the buffer size. -/
theorem size_inner16Loop (th tl : ByteArray) : ∀ (n : Nat) (j j1 i0 i1 i2 i3 : USize)
    (b : ByteArray) (h), (inner16Loop p th tl n j j1 i0 i1 i2 i3 b h).size = b.size
  | 0, _, _, _, _, _, _, _, _ => rfl
  | n + 1, j, j1, i0, i1, i2, i3, b, h => by
    rw [inner16Loop, size_inner16Loop th tl n, size_step16]

/-- `x + y` does not wrap below the machine word size. -/
theorem usize_add_toNat (x y : USize) (h : x.toNat + y.toNat < USize.size) :
    (x + y).toNat = x.toNat + y.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, hsize, Nat.mod_eq_of_lt h]

/-- `k * y` does not wrap below the machine word size. -/
theorem usize_mul_toNat (k : Nat) (y : USize) (hk : k < 4294967296)
    (h : k * y.toNat < USize.size) : (OfNat.ofNat k * y : USize).toNat = k * y.toNat := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, usize_numeral k hk, hsize, Nat.mod_eq_of_lt h]

/-- `count` radix-four blocks of quarter `q = 16 n` from word `base`, each in `n` batches of
sixteen cells, after one range check for all of them. -/
@[specialize]
def blocks16Loop (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (n : Nat) (q : USize) :
    (count : Nat) → (base : USize) → (b : ByteArray) →
    4 * (base.toNat + 4 * q.toNat * count) ≤ b.size ∧ 16 * n = q.toNat ∧
      4 * (2 * q.toNat) ≤ th.size ∧ 4 * q.toNat ≤ tl.size ∧ b.size < USize.size ∧
      th.size < USize.size ∧ tl.size < USize.size → ByteArray
  | 0, _, b, _ => b
  | count + 1, base, b, h =>
    have hc : 4 * q.toNat ≤ 4 * q.toNat * (count + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h1 : (base + q).toNat = base.toNat + q.toNat := usize_add_toNat _ _ (by omega)
    have h2 : (base + 2 * q).toNat = base.toNat + 2 * q.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_toNat 2 q (by decide) (by omega)]; omega),
        usize_mul_toNat 2 q (by decide) (by omega)]
    have h3 : (base + 3 * q).toNat = base.toNat + 3 * q.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_toNat 3 q (by decide) (by omega)]; omega),
        usize_mul_toNat 3 q (by decide) (by omega)]
    have h4 : (base + 4 * q).toNat = base.toNat + 4 * q.toNat := by
      rw [usize_add_toNat _ _ (by rw [usize_mul_toNat 4 q (by decide) (by omega)]; omega),
        usize_mul_toNat 4 q (by decide) (by omega)]
    let b' := inner16Loop p th tl n 0 q base (base + q) (base + 2 * q) (base + 3 * q) b (by
      rw [h1, h2, h3, USize.toNat_zero]
      omega)
    blocks16Loop p th tl n q count (base + 4 * q) b' (by
      rw [size_inner16Loop, h4, Nat.mul_succ] at *
      omega)

/-- The radix-four inner loop: whole sixteen-cell batches after one range check, then the
scalar tail. -/
@[specialize]
def inner16 (p : ℕ) [Mont32Field p] (th tl : ByteArray) (q j i0 i1 i2 i3 : Nat)
    (b : ByteArray) : ByteArray :=
  let n := (q - j) / 16
  if h : 4 * (i0 + 16 * n) ≤ b.size ∧ 4 * (i1 + 16 * n) ≤ b.size ∧
      4 * (i2 + 16 * n) ≤ b.size ∧ 4 * (i3 + 16 * n) ≤ b.size ∧
      4 * (j + q + 16 * n) ≤ th.size ∧ 4 * (j + 16 * n) ≤ th.size ∧
      4 * (j + 16 * n) ≤ tl.size ∧ b.size < USize.size ∧ th.size < USize.size ∧
      tl.size < USize.size then
    inner p th tl q (j + 16 * n) (i0 + 16 * n) (i1 + 16 * n) (i2 + 16 * n) (i3 + 16 * n)
      (inner16Loop p th tl n (USize.ofNatLT j (by omega)) (USize.ofNatLT (j + q) (by omega))
        (USize.ofNatLT i0 (by omega)) (USize.ofNatLT i1 (by omega))
        (USize.ofNatLT i2 (by omega)) (USize.ofNatLT i3 (by omega)) b
        (by simp only [USize.toNat_ofNatLT]; exact h))
  else inner p th tl q j i0 i1 i2 i3 b
/-- Sixteen radix-two DIF butterflies between the words from `i0` and from `i1`, with twiddles
from word `j` of `w`. -/
@[noinline, specialize]
def pair16 (p : ℕ) [Mont32Field p] (w : @& ByteArray) (j i0 i1 : USize) (b : ByteArray)
    (h : 4 * (i0.toNat + 15) + 3 < b.size ∧ 4 * (i1.toNat + 15) + 3 < b.size ∧
      4 * (j.toNat + 15) + 3 < w.size ∧ b.size < USize.size ∧ w.size < USize.size) :
    ByteArray :=
  pair16_words%

theorem size_pair16 (w : ByteArray) (j i0 i1 : USize) (b : ByteArray) (h) :
    (pair16 p w j i0 i1 b h).size = b.size := by
  unfold pair16
  simp only [write16U, size_storeWords]

/-- `n` batches of sixteen radix-two butterflies after one range check. -/
@[specialize]
def pair16Loop (p : ℕ) [Mont32Field p] (w : @& ByteArray) : (n : Nat) → (j i0 i1 : USize) →
    (b : ByteArray) →
    4 * (i0.toNat + 16 * n) ≤ b.size ∧ 4 * (i1.toNat + 16 * n) ≤ b.size ∧
      4 * (j.toNat + 16 * n) ≤ w.size ∧ b.size < USize.size ∧ w.size < USize.size → ByteArray
  | 0, _, _, _, b, _ => b
  | n + 1, j, i0, i1, b, h =>
    let b' := pair16 p w j i0 i1 b (by omega)
    pair16Loop p w n (j + 16) (i0 + 16) (i1 + 16) b' (by
      have hs : b'.size = b.size := size_pair16 ..
      rw [hs, usize_add16 j w.size (by omega) h.2.2.2.2, usize_add16 i0 b.size (by omega) h.2.2.2.1,
        usize_add16 i1 b.size (by omega) h.2.2.2.1]
      omega)

/-- Radix-two DIF butterflies `j, …, q - 1` between the words from `i0` and from `i1`, with
twiddles from word `j` of `w`: the scalar loop. -/
@[specialize]
def pairInner (p : ℕ) [Mont32Field p] (w : @& ByteArray) (q j i0 i1 : Nat)
    (b : ByteArray) : ByteArray :=
  if j < q then
    let x := read b i0
    let y := read b i1
    pairInner p w q (j + 1) (i0 + 1) (i1 + 1)
      (write (write b i0 (add p x y)) i1 (mul p (read w j) (sub p x y)))
  else b
termination_by q - j

/-- The radix-two inner loop: whole sixteen-butterfly batches after one range check, then the
scalar tail. -/
@[specialize]
def pairs (p : ℕ) [Mont32Field p] (w : @& ByteArray) (q j i0 i1 : Nat)
    (b : ByteArray) : ByteArray :=
  let n := (q - j) / 16
  if h : 4 * (i0 + 16 * n) ≤ b.size ∧ 4 * (i1 + 16 * n) ≤ b.size ∧ 4 * (j + 16 * n) ≤ w.size ∧
      b.size < USize.size ∧ w.size < USize.size then
    pairInner p w q (j + 16 * n) (i0 + 16 * n) (i1 + 16 * n)
      (pair16Loop p w n (USize.ofNatLT j (by omega)) (USize.ofNatLT i0 (by omega))
        (USize.ofNatLT i1 (by omega)) b (by simp only [USize.toNat_ofNatLT]; exact h))
  else pairInner p w q j i0 i1 b
@[inline] def readWord (b : @& ByteArray) (i : USize) : UInt32 :=
  readAt b i 0
@[specialize] def decode (p : ℕ) [Mont32Field p] (logN : Nat) (b : ByteArray) (nInv : UInt32)
    (inverse : Bool) : Array (FastField p) :=
  let shift := (32 - logN).toUInt32
  tabulate (fun i : Fin (2 ^ logN) ↦
    let j := (reverse32 i.val.toUInt32 >>> shift).toNat
    let x := read b j
    let x := if inverse then mul p nInv x else x
    if h : x.toNat < p then ⟨x, h⟩ else 0)
end CompPoly.CPolynomial.NTTFast.Packed.Native
