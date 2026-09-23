/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Arithmetic
public import CompPoly.Fields.Binary.Tower.Fast
public import CompPoly.Data.Bytes.CanonicalNat

/-!
# Serialization of the binary tower

A level-`k` tower element `ConcreteBTField k` is its `2 ^ k` low-first tower-basis coordinates.
Its canonical natural is that bit pattern read as an integer and its encoding the little-endian
bytes of the pattern, `bytesFor (2 ^ 2 ^ k)` of them: one byte at level three, sixteen at level
seven. `FastBT128`, the two-limb level-seven carrier, agrees with `ConcreteBTField 7` through
`toConcrete` (`toList_toBytes_toConcrete`, `toByteArray_toConcrete`).

These are tower-basis coordinates. `AesField` at eight bits and `ConcreteBF128Ghash` at 128 bits
use different bases, and their encodings are not interchangeable with these.
-/

@[expose] public section

namespace ConcreteBinaryTower

open CompPoly

namespace ConcreteBTField

instance (k : ℕ) : CanonicalNat (ConcreteBTField k) :=
  CanonicalNat.ofBitVec toBitVec ofBitVec ofBitVec_toBitVec toBitVec_ofBitVec

instance (k : ℕ) : ByteCodec (ConcreteBTField k) := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound (k : ℕ) :
    CanonicalNat.bound (ConcreteBTField k) = 2 ^ 2 ^ k := rfl

@[simp] theorem canonicalNat_toNat {k : ℕ} (x : ConcreteBTField k) :
    CanonicalNat.toNat x = x.toNat := rfl

theorem byteCodec_width (k : ℕ) :
    ByteCodec.width (ConcreteBTField k) = Bytes.bytesFor (2 ^ 2 ^ k) := rfl

/-- A level-`k` element takes `⌈2 ^ k / 8⌉` bytes: one byte at level three, sixteen at
level seven. -/
theorem byteCodec_width_eq (k : ℕ) :
    ByteCodec.width (ConcreteBTField k) = (2 ^ k + 7) / 8 := by
  rw [byteCodec_width, Bytes.bytesFor_two_pow (Nat.two_pow_pos k)]

@[simp] theorem byteCodec_width_three : ByteCodec.width (ConcreteBTField 3) = 1 := by
  rw [byteCodec_width_eq]
  norm_num

@[simp] theorem byteCodec_width_seven : ByteCodec.width (ConcreteBTField 7) = 16 := by
  rw [byteCodec_width_eq]
  norm_num

end ConcreteBTField

namespace Fast.FastBT128

/-- The two limbs read as a `2 ^ 7`-bit word, `lo` first. The width is written `2 ^ 7` so that
the carrier's codec has the same width term as `ConcreteBTField 7`. -/
def toBitVec (v : FastBT128) : BitVec (2 ^ 7) := BitVec.ofNat (2 ^ 7) v.toNat

/-- Split a `2 ^ 7`-bit word into two limbs. -/
def ofBitVec (b : BitVec (2 ^ 7)) : FastBT128 := ofNat b.toNat

theorem toNat_lt (v : FastBT128) : v.toNat < 2 ^ 2 ^ 7 := by
  unfold FastBT128.toNat
  have hlo := v.lo.toNat_lt
  have hhi := v.hi.toNat_lt
  omega

theorem toNat_ofNat (n : ℕ) : (ofNat n).toNat = n % 2 ^ 2 ^ 7 := by
  simp only [ofNat, FastBT128.toNat, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  omega

theorem ofNat_toNat (v : FastBT128) : ofNat v.toNat = v := by
  obtain ⟨lo, hi⟩ := v
  simp only [ofNat, FastBT128.toNat, Nat.shiftRight_eq_div_pow, FastBT128.mk.injEq]
  have hlo := lo.toNat_lt
  have hhi := hi.toNat_lt
  constructor
  · rw [← UInt64.toNat_inj, UInt64.toNat_ofNat']
    omega
  · rw [← UInt64.toNat_inj, UInt64.toNat_ofNat']
    omega

theorem ofBitVec_toBitVec (v : FastBT128) : ofBitVec (toBitVec v) = v := by
  rw [ofBitVec, toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt v), ofNat_toNat]

theorem toBitVec_ofBitVec (b : BitVec (2 ^ 7)) : toBitVec (ofBitVec b) = b := by
  rw [toBitVec, ofBitVec, toNat_ofNat, Nat.mod_eq_of_lt b.isLt, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

instance : CanonicalNat FastBT128 :=
  CanonicalNat.ofBitVec toBitVec ofBitVec ofBitVec_toBitVec toBitVec_ofBitVec

instance : ByteCodec FastBT128 := ByteCodec.ofCanonicalNat _

@[simp] theorem canonicalNat_bound : CanonicalNat.bound FastBT128 = 2 ^ 2 ^ 7 := rfl

@[simp] theorem canonicalNat_toNat (v : FastBT128) : CanonicalNat.toNat v = v.toNat := by
  show (BitVec.ofNat (2 ^ 7) v.toNat).toNat = v.toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toNat_lt v)]

@[simp] theorem byteCodec_width : ByteCodec.width FastBT128 = 16 := by
  show Bytes.bytesFor (2 ^ 2 ^ 7) = 16
  rw [Bytes.bytesFor_two_pow (by norm_num)]
  norm_num

/-- The fast carrier and the level-seven tower field encode the same element identically.

Stated on the byte lists: the two codecs' widths are both `bytesFor (2 ^ 2 ^ 7)`, but through
different instance paths, and a `Vector`-typed statement would ask the kernel to identify them
by evaluation, which sends it into `Nat.log2`'s well-founded recursion. Rewriting each width to
`16` through its own width lemma avoids that. -/
theorem toList_toBytes_toConcrete (v : FastBT128) :
    (ByteCodec.toBytes (toConcrete v)).toList = (ByteCodec.toBytes v).toList := by
  have h : CanonicalNat.toNat (toConcrete v) = CanonicalNat.toNat v := by
    rw [canonicalNat_toNat, ConcreteBTField.canonicalNat_toNat, toNat_toConcrete]
  change (Bytes.toVecLE (ByteCodec.width (ConcreteBTField 7))
      (CanonicalNat.toNat (toConcrete v))).toList
    = (Bytes.toVecLE (ByteCodec.width FastBT128) (CanonicalNat.toNat v)).toList
  rw [Bytes.toList_toVecLE, Bytes.toList_toVecLE, ConcreteBTField.byteCodec_width_seven,
    byteCodec_width, h]

/-- The same agreement as a `ByteArray` equality, the form a transcript sees. -/
theorem toByteArray_toConcrete (v : FastBT128) :
    ByteCodec.toByteArray (toConcrete v) = ByteCodec.toByteArray v := by
  have h := toList_toBytes_toConcrete v
  simp only [Vector.toList] at h
  unfold ByteCodec.toByteArray
  rw [Array.toList_inj.mp h]

end Fast.FastBT128

end ConcreteBinaryTower
