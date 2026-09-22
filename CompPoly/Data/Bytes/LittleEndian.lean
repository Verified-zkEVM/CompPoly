/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Little-endian byte encodings of naturals

The one encoder every fixed-width serialization in CompPoly is built from: a natural number
becomes exactly `w` bytes, least significant first, and `w` bytes become a natural.

* `toListLE w n` / `ofListLE` on `List UInt8`, with the round-trip laws
  `ofListLE_toListLE` (as `n % 256 ^ w`, hence exact below `256 ^ w`) and
  `toListLE_ofListLE`, and the concatenation law `ofListLE_append`.
* `toVecLE` / `ofVecLE` and `toByteArrayLE` / `ofByteArrayLE`, the same maps on `Vector UInt8 w`
  and `ByteArray`.
* `bytesFor bound`, the number of bytes needed to hold every natural below `bound`, with
  `le_pow_bytesFor : bound ≤ 256 ^ bytesFor bound`. It is `Nat.log2`-based so that the kernel
  evaluates it on numerals by `decide`.

The layout is the one arkworks and plonky3 use for field elements: the canonical integer,
little-endian, padded to a fixed width.
-/

@[expose] public section

namespace CompPoly.Bytes

/-! ## Lists -/

/-- The `w` little-endian bytes of `n`; bits above `8 * w` are dropped. -/
def toListLE : ℕ → ℕ → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: toListLE w (n / 256)

/-- The natural with the given little-endian bytes. -/
def ofListLE : List UInt8 → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * ofListLE bs

@[simp] theorem toListLE_zero (n : ℕ) : toListLE 0 n = [] := rfl

@[simp] theorem toListLE_succ (w n : ℕ) :
    toListLE (w + 1) n = UInt8.ofNat (n % 256) :: toListLE w (n / 256) := rfl

@[simp] theorem ofListLE_nil : ofListLE [] = 0 := rfl

@[simp] theorem ofListLE_cons (b : UInt8) (bs : List UInt8) :
    ofListLE (b :: bs) = b.toNat + 256 * ofListLE bs := rfl

@[simp] theorem length_toListLE (w n : ℕ) : (toListLE w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp only [toListLE_succ, List.length_cons, ih]

theorem ofListLE_toListLE (w n : ℕ) : ofListLE (toListLE w n) = n % 256 ^ w := by
  induction w generalizing n with
  | zero => simp only [toListLE_zero, ofListLE_nil, pow_zero, Nat.mod_one]
  | succ w ih =>
    have h : n % 256 % 2 ^ 8 = n % 256 :=
      Nat.mod_eq_of_lt (by simpa using Nat.mod_lt n (show 0 < 256 by norm_num))
    rw [toListLE_succ, ofListLE_cons, ih, UInt8.toNat_ofNat', h, pow_succ', Nat.mod_mul]

theorem ofListLE_toListLE_of_lt {w n : ℕ} (h : n < 256 ^ w) : ofListLE (toListLE w n) = n := by
  rw [ofListLE_toListLE, Nat.mod_eq_of_lt h]

theorem ofListLE_lt (l : List UInt8) : ofListLE l < 256 ^ l.length := by
  induction l with
  | nil => simp only [ofListLE_nil, List.length_nil, pow_zero, Nat.lt_one_iff]
  | cons b bs ih =>
    rw [ofListLE_cons, List.length_cons, pow_succ]
    have hb : b.toNat < 256 := b.toNat_lt
    omega

theorem toListLE_ofListLE (l : List UInt8) : toListLE l.length (ofListLE l) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    rw [List.length_cons, toListLE_succ, ofListLE_cons]
    congr 1
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, UInt8.ofNat_toNat]
    · rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hb, Nat.zero_add, ih]

theorem toListLE_inj_of_lt {w n m : ℕ} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : toListLE w n = toListLE w m) : n = m := by
  have := congrArg ofListLE h
  rwa [ofListLE_toListLE_of_lt hn, ofListLE_toListLE_of_lt hm] at this

theorem ofListLE_append (l₁ l₂ : List UInt8) :
    ofListLE (l₁ ++ l₂) = ofListLE l₁ + 256 ^ l₁.length * ofListLE l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, ofListLE_nil, List.length_nil, pow_zero, one_mul, zero_add]
  | cons b bs ih =>
    rw [List.cons_append, ofListLE_cons, ofListLE_cons, ih, List.length_cons, pow_succ]
    ring

/-! ## Widths -/

/-- The number of bytes needed to hold every natural below `bound`: one byte for `bound ≤ 256`,
and in general the least `w` with `bound ≤ 256 ^ w`, except that `bound ≤ 1` still takes one
byte. Defined through `Nat.log2` so that the kernel evaluates it on numerals. -/
def bytesFor (bound : ℕ) : ℕ := (Nat.log2 (bound - 1) + 8) / 8

theorem bytesFor_pos (bound : ℕ) : 0 < bytesFor bound := by
  unfold bytesFor
  omega

theorem le_pow_bytesFor (bound : ℕ) : bound ≤ 256 ^ bytesFor bound := by
  rcases Nat.eq_zero_or_pos bound with rfl | hpos
  · exact Nat.zero_le _
  have h1 : bound - 1 < 2 ^ (Nat.log2 (bound - 1) + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : Nat.log2 (bound - 1) + 1 ≤ 8 * bytesFor bound := by
    unfold bytesFor
    omega
  have h3 : (2 : ℕ) ^ (Nat.log2 (bound - 1) + 1) ≤ 2 ^ (8 * bytesFor bound) :=
    Nat.pow_le_pow_right (by norm_num) h2
  have h4 : (256 : ℕ) ^ bytesFor bound = 2 ^ (8 * bytesFor bound) := by
    rw [pow_mul]
    norm_num
  rw [h4]
  omega

/-- The width of a power of two: `k` bits need `⌈k / 8⌉` bytes. Stated so that a bit-pattern
type's width is a small numeral computation rather than a kernel evaluation of `2 ^ k`. -/
theorem bytesFor_two_pow {k : ℕ} (hk : 0 < k) : bytesFor (2 ^ k) = (k + 7) / 8 := by
  have hlog : Nat.log2 (2 ^ k - 1) = k - 1 := by
    rw [Nat.log2_eq_log_two, Nat.log_eq_iff (Or.inr ⟨by norm_num, ?_⟩)]
    · have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ^ (k - 1) * 2 = 2 ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      constructor
      · omega
      · rw [Nat.sub_add_cancel hk]
        omega
    · have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      omega
  unfold bytesFor
  rw [hlog]
  omega

/-! ## Vectors -/

/-- The `w` little-endian bytes of `n` as a vector. -/
def toVecLE (w n : ℕ) : Vector UInt8 w :=
  ⟨(toListLE w n).toArray, by simp only [List.size_toArray, length_toListLE]⟩

/-- The natural with the given little-endian bytes. -/
def ofVecLE {w : ℕ} (v : Vector UInt8 w) : ℕ := ofListLE v.toList

@[simp] theorem toList_toVecLE (w n : ℕ) : (toVecLE w n).toList = toListLE w n := rfl

theorem ofVecLE_toVecLE (w n : ℕ) : ofVecLE (toVecLE w n) = n % 256 ^ w :=
  ofListLE_toListLE w n

theorem ofVecLE_toVecLE_of_lt {w n : ℕ} (h : n < 256 ^ w) : ofVecLE (toVecLE w n) = n :=
  ofListLE_toListLE_of_lt h

theorem ofVecLE_lt {w : ℕ} (v : Vector UInt8 w) : ofVecLE v < 256 ^ w := by
  have := ofListLE_lt v.toList
  rwa [Vector.length_toList] at this

theorem toVecLE_ofVecLE {w : ℕ} (v : Vector UInt8 w) : toVecLE w (ofVecLE v) = v := by
  rw [← Vector.toList_inj, toList_toVecLE]
  have h := toListLE_ofListLE v.toList
  rwa [Vector.length_toList] at h

theorem toVecLE_inj_of_lt {w n m : ℕ} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : toVecLE w n = toVecLE w m) : n = m :=
  toListLE_inj_of_lt hn hm (by simpa only [← toList_toVecLE] using congrArg Vector.toList h)

/-! ## Byte arrays -/

/-- The `w` little-endian bytes of `n` as a `ByteArray`. -/
def toByteArrayLE (w n : ℕ) : ByteArray := ⟨(toListLE w n).toArray⟩

/-- The natural with the given little-endian bytes. -/
def ofByteArrayLE (b : ByteArray) : ℕ := ofListLE b.data.toList

@[simp] theorem size_toByteArrayLE (w n : ℕ) : (toByteArrayLE w n).size = w := by
  simp only [toByteArrayLE, ByteArray.size, List.size_toArray, length_toListLE]

@[simp] theorem data_toByteArrayLE (w n : ℕ) :
    (toByteArrayLE w n).data = (toListLE w n).toArray := rfl

theorem ofByteArrayLE_toByteArrayLE (w n : ℕ) : ofByteArrayLE (toByteArrayLE w n) = n % 256 ^ w :=
  ofListLE_toListLE w n

theorem ofByteArrayLE_toByteArrayLE_of_lt {w n : ℕ} (h : n < 256 ^ w) :
    ofByteArrayLE (toByteArrayLE w n) = n :=
  ofListLE_toListLE_of_lt h

theorem toByteArrayLE_inj_of_lt {w n m : ℕ} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : toByteArrayLE w n = toByteArrayLE w m) : n = m := by
  apply toListLE_inj_of_lt hn hm
  have := congrArg (fun b : ByteArray => b.data.toList) h
  simpa only [data_toByteArrayLE, List.toList_toArray] using this

end CompPoly.Bytes
