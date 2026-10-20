/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.Data.ByteArray.Basic
import Init.Data.ByteArray.Lemmas

/-!
# Little-endian `UInt32` load/store on `ByteArray` (backport)

The little-endian `UInt32` accessors of Lean core's `Init.Data.ByteArray.Pack`, from
[lean4#14053](https://github.com/leanprover/lean4/pull/14053), with the same names, signatures
and Lean definitions. They read or write a `UInt32` at a byte offset of a `ByteArray` with a
single native load or store.

* `getUInt32LE!` / `setUInt32LE!`: `Nat` offset, no proof. All-or-nothing on bounds: a read
  returns `0` and a write leaves the array unchanged unless the whole four-byte window fits.
  These are the proof-level specification; the proof-carrying variants below are definitionally
  equal to them.
* `getUInt32LE` / `setUInt32LE`: `Nat` offset with an in-bounds proof.
* `ugetUInt32LE` / `usetUInt32LE`: `USize` offset with an in-bounds proof, for hot loops.

Until a toolchain ships them, their C is inlined here. It differs from the PR's byte-shift
loops in two ways that matter for kernels issuing many adjacent loads and stores, such as the
packed NTT:

* Loads and stores use a fixed four-byte `memcpy`, byte-swapped on big-endian hosts. The
  byte-shift form let clang's vectorizer turn adjacent loads into shuffle sequences.
* After a store, the C states that the array is still unshared (`__builtin_assume`), so the
  compiler keeps one sharing check for a run of stores instead of one per store.

Delete this module when the toolchain provides `Init.Data.ByteArray.Pack`.
-/

@[expose] public section

namespace ByteArray

/-- Reads the little-endian `UInt32` at byte offset `off`, or `0` if `off + 4 > a.size`. -/
@[extern c inline "({ b_lean_obj_arg a = #1, i = #2; size_t sz = lean_sarray_size(a), k;
  uint32_t r = 0; if (lean_is_scalar(i) && sz >= 4 && (k = lean_unbox(i)) <= sz - 4) {
  __builtin_memcpy(&r, lean_sarray_cptr(a) + k, 4);
  if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) r = __builtin_bswap32(r); } r; })"]
def getUInt32LE! (a : @& ByteArray) (off : @& Nat) : UInt32 :=
  if off + 4 ≤ a.size then
    (a.get! off).toUInt32 |||
    (a.get! (off+1)).toUInt32 <<< 0x8 |||
    (a.get! (off+2)).toUInt32 <<< 0x10 |||
    (a.get! (off+3)).toUInt32 <<< 0x18
  else 0

/-- Writes `v` as a little-endian `UInt32` at byte offset `off`; unchanged if `off + 4 > a.size`. -/
@[extern c inline "({ lean_object *r = #1; b_lean_obj_arg i = #2; uint32_t v = #3;
  if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v = __builtin_bswap32(v);
  size_t sz = lean_sarray_size(r), k; if (lean_is_scalar(i) && sz >= 4 &&
  (k = lean_unbox(i)) <= sz - 4) { r = lean_sarray_ensure_exclusive(r);
  __builtin_memcpy(lean_sarray_cptr(r) + k, &v, 4); __builtin_assume(r->m_rc == 1); } r; })"]
def setUInt32LE! (a : ByteArray) (off : @& Nat) (v : UInt32) : ByteArray :=
  if off + 4 ≤ a.size then
    (((a.set! off v.toUInt8).set! (off+1) (v >>> 0x8).toUInt8).set! (off+2)
      (v >>> 0x10).toUInt8).set! (off+3) (v >>> 0x18).toUInt8
  else a

/-- Reads the little-endian `UInt32` at byte offset `i`. Requires the window to be in bounds. -/
@[extern c inline "({ uint32_t r; __builtin_memcpy(&r, lean_sarray_cptr(#1) + lean_unbox(#2), 4);
  __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__ ? __builtin_bswap32(r) : r; })"]
def getUInt32LE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 4 ≤ a.size := by get_elem_tactic) →
    UInt32
  | a, i, _ => a.getUInt32LE! i

/-- Reads the little-endian `UInt32` at byte offset `i` (`USize`). Requires the window to be in
bounds. -/
@[extern c inline "({ uint32_t r; __builtin_memcpy(&r, lean_sarray_cptr(#1) + #2, 4);
  __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__ ? __builtin_bswap32(r) : r; })"]
def ugetUInt32LE : (a : @& ByteArray) → (i : USize) →
    (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) → UInt32
  | a, i, _ => a.getUInt32LE! i.toNat

/-- Writes `v` as a little-endian `UInt32` at byte offset `i`. Requires the window to be in
bounds. -/
@[extern c inline "({ lean_object *r = #1; uint32_t v = #3;
  if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v = __builtin_bswap32(v);
  r = lean_sarray_ensure_exclusive(r);
  __builtin_memcpy(lean_sarray_cptr(r) + lean_unbox(#2), &v, 4);
  __builtin_assume(r->m_rc == 1); r; })"]
def setUInt32LE : (a : ByteArray) → (i : @& Nat) → (v : UInt32) →
    (h : i + 4 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt32LE! i v

/-- Writes `v` as a little-endian `UInt32` at byte offset `i` (`USize`). Requires the window to
be in bounds. -/
@[extern c inline "({ lean_object *r = #1; uint32_t v = #3;
  if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v = __builtin_bswap32(v);
  r = lean_sarray_ensure_exclusive(r);
  __builtin_memcpy(lean_sarray_cptr(r) + #2, &v, 4); __builtin_assume(r->m_rc == 1); r; })"]
def usetUInt32LE : (a : ByteArray) → (i : USize) → (v : UInt32) →
    (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt32LE! i.toNat v

/-! ### Lemmas -/

theorem get!_eq_getElem! (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]
    simp only [get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (show i < a.data.size from h), Option.getD_some]
    rfl
  · rw [getElem!_neg a i h]
    simp only [get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (show a.data.size ≤ i by simp only [size] at h; omega),
      Option.getD_none]

@[simp] theorem size_setUInt32LE! (a : ByteArray) (off : Nat) (v : UInt32) :
    (a.setUInt32LE! off v).size = a.size := by unfold setUInt32LE!; split <;> simp

@[simp] theorem size_usetUInt32LE (a : ByteArray) (i : USize) (v : UInt32) (h) :
    (a.usetUInt32LE i v h).size = a.size := size_setUInt32LE! a i.toNat v

theorem getUInt32LE!_setUInt32LE!_self (a : ByteArray) (off : Nat) (v : UInt32)
    (h : off + 4 ≤ a.size) : (a.setUInt32LE! off v).getUInt32LE! off = v := by
  unfold getUInt32LE! setUInt32LE!
  rw [ite_eq_left h]
  simp only [size_set!, get!_eq_getElem!]
  rw [ite_eq_left h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;> by_cases h1 : i < 16 <;> by_cases h2 : i < 24 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

theorem getElem!_setUInt32LE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt32)
    (h : j < o ∨ o + 4 ≤ j) : (a.setUInt32LE! o v)[j]! = a[j]! := by
  unfold setUInt32LE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getUInt32LE!_setUInt32LE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt32)
    (h₂ : o₂ + 4 ≤ a.size) (hd : o₂ + 4 ≤ o₁ ∨ o₁ + 4 ≤ o₂) :
    (a.setUInt32LE! o₁ v).getUInt32LE! o₂ = a.getUInt32LE! o₂ := by
  unfold getUInt32LE!
  simp only [size_setUInt32LE!, get!_eq_getElem!]
  rw [ite_eq_left h₂, ite_eq_left h₂,
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega)]

end ByteArray
