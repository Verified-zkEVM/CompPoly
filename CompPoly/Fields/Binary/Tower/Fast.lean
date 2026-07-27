/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Binary.Tower.Concrete.Field
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Tactic.LinearCombination

/-!
# Fast Binary Tower Arithmetic

Packed machine-word implementation of `ConcreteBTField` arithmetic with the same bit
layout: a level-`k` element is the low `2 ^ 2 ^ k` bits of one `UInt64` for `k ≤ 6`, and a
pair of limbs at level 7. Multiplication is Karatsuba with an `O(width)`
multiply-by-generator reduction instead of the fourth recursive product in `concrete_mul`.

This module carries the runtime ladder, range bounds, the bounded carrier `FastBT` with
its additive algebra (transported along the injective `toConcrete` bridge), `Mul`
instances per usable width, and the proof that multiplication agrees with `concrete_mul`
(`mulRec_correct`, transported per width as `toConcrete_mul_bt*`). `Ring`/`Field`
instance assembly and the squaring/inversion proofs land in a follow-up.
-/

namespace ConcreteBinaryTower.Fast

/-! ## Raw word operations

Names carry the bit width of the operands (`mul8` multiplies level-3 values held in the
low 8 bits); `mulByZk` multiplies a level-`k` value by its tower generator `Z k`. Each
multiplication rung computes the three Karatsuba half-products `p0 = a₀b₀`, `p2 = a₁b₁`,
`p1 = (a₀+a₁)(b₀+b₁)` and recombines as `lo = p0 + p2`, `hi = p1 + lo + Z·p2`. Squaring
uses that the cross term vanishes in characteristic 2; inversion is the same quadratic
descent as `concrete_inv`. Inputs are assumed in range (upper bits zero). The `sq*`/`inv*`
rungs are runtime-only for now; their recursive twins, bounds, and correctness proofs land
with the follow-up correctness step. -/

/-- GF(4) multiplication (level 1). -/
@[inline] def mul2 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 1
  let a1 := a >>> 1
  let b0 := b &&& 1
  let b1 := b >>> 1
  let p0 := a0 &&& b0
  let p2 := a1 &&& b1
  let p1 := (a0 ^^^ a1) &&& (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ p2) <<< 1) ||| lo

/-- Multiplication by the level-1 generator `Z 1`. -/
@[inline] def mulByZ1 (v : UInt64) : UInt64 :=
  let v0 := v &&& 1
  let v1 := v >>> 1
  ((v0 ^^^ v1) <<< 1) ||| v1

/-- GF(4) squaring. -/
@[inline] def sq2 (v : UInt64) : UInt64 :=
  let v0 := v &&& 1
  let v1 := v >>> 1
  (v1 <<< 1) ||| (v0 ^^^ v1)

/-- GF(4) inversion (`0 ↦ 0`). -/
@[inline] def inv2 (v : UInt64) : UInt64 :=
  if v < 2 then v else v ^^^ 1

/-- GF(2^4) multiplication (level 2). -/
@[inline] def mul4 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0x3
  let a1 := a >>> 2
  let b0 := b &&& 0x3
  let b1 := b >>> 2
  let p0 := mul2 a0 b0
  let p2 := mul2 a1 b1
  let p1 := mul2 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ1 p2) <<< 2) ||| lo

/-- Multiplication by the level-2 generator `Z 2`. -/
@[inline] def mulByZ2 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0x3
  let v1 := v >>> 2
  ((v0 ^^^ mulByZ1 v1) <<< 2) ||| v1

/-- GF(2^4) squaring. -/
@[inline] def sq4 (v : UInt64) : UInt64 :=
  let s0 := sq2 (v &&& 0x3)
  let s1 := sq2 (v >>> 2)
  ((mulByZ1 s1) <<< 2) ||| (s0 ^^^ s1)

/-- GF(2^4) inversion (`0 ↦ 0`). -/
@[inline] def inv4 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0x3
  let v1 := v >>> 2
  let next := v0 ^^^ mulByZ1 v1
  let delta := mul2 v0 next ^^^ sq2 v1
  let d := inv2 delta
  ((mul2 d v1) <<< 2) ||| (mul2 d next)

/-- GF(2^8) multiplication (level 3). -/
@[inline] def mul8 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xF
  let a1 := a >>> 4
  let b0 := b &&& 0xF
  let b1 := b >>> 4
  let p0 := mul4 a0 b0
  let p2 := mul4 a1 b1
  let p1 := mul4 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ2 p2) <<< 4) ||| lo

/-- Multiplication by the level-3 generator `Z 3`. -/
@[inline] def mulByZ3 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xF
  let v1 := v >>> 4
  ((v0 ^^^ mulByZ2 v1) <<< 4) ||| v1

/-- GF(2^8) squaring. -/
@[inline] def sq8 (v : UInt64) : UInt64 :=
  let s0 := sq4 (v &&& 0xF)
  let s1 := sq4 (v >>> 4)
  ((mulByZ2 s1) <<< 4) ||| (s0 ^^^ s1)

/-- GF(2^8) inversion (`0 ↦ 0`). -/
@[inline] def inv8 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xF
  let v1 := v >>> 4
  let next := v0 ^^^ mulByZ2 v1
  let delta := mul4 v0 next ^^^ sq4 v1
  let d := inv4 delta
  ((mul4 d v1) <<< 4) ||| (mul4 d next)

/-- GF(2^16) multiplication (level 4). -/
@[inline] def mul16 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFF
  let a1 := a >>> 8
  let b0 := b &&& 0xFF
  let b1 := b >>> 8
  let p0 := mul8 a0 b0
  let p2 := mul8 a1 b1
  let p1 := mul8 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ3 p2) <<< 8) ||| lo

/-- Multiplication by the level-4 generator `Z 4`. -/
@[inline] def mulByZ4 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFF
  let v1 := v >>> 8
  ((v0 ^^^ mulByZ3 v1) <<< 8) ||| v1

/-- GF(2^16) squaring. -/
@[inline] def sq16 (v : UInt64) : UInt64 :=
  let s0 := sq8 (v &&& 0xFF)
  let s1 := sq8 (v >>> 8)
  ((mulByZ3 s1) <<< 8) ||| (s0 ^^^ s1)

/-- GF(2^16) inversion (`0 ↦ 0`). -/
@[inline] def inv16 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFF
  let v1 := v >>> 8
  let next := v0 ^^^ mulByZ3 v1
  let delta := mul8 v0 next ^^^ sq8 v1
  let d := inv8 delta
  ((mul8 d v1) <<< 8) ||| (mul8 d next)

/-- GF(2^32) multiplication (level 5). Outlined: fully inlining the ladder above this
width exceeds the compiler's recursion depth and bloats code for no measured gain. -/
def mul32 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFFFF
  let a1 := a >>> 16
  let b0 := b &&& 0xFFFF
  let b1 := b >>> 16
  let p0 := mul16 a0 b0
  let p2 := mul16 a1 b1
  let p1 := mul16 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ4 p2) <<< 16) ||| lo

/-- Multiplication by the level-5 generator `Z 5`. -/
@[inline] def mulByZ5 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFF
  let v1 := v >>> 16
  ((v0 ^^^ mulByZ4 v1) <<< 16) ||| v1

/-- GF(2^32) squaring. -/
@[inline] def sq32 (v : UInt64) : UInt64 :=
  let s0 := sq16 (v &&& 0xFFFF)
  let s1 := sq16 (v >>> 16)
  ((mulByZ4 s1) <<< 16) ||| (s0 ^^^ s1)

/-- GF(2^32) inversion (`0 ↦ 0`). -/
def inv32 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFF
  let v1 := v >>> 16
  let next := v0 ^^^ mulByZ4 v1
  let delta := mul16 v0 next ^^^ sq16 v1
  let d := inv16 delta
  ((mul16 d v1) <<< 16) ||| (mul16 d next)

/-- GF(2^64) multiplication (level 6). Outlined, see `mul32`. -/
def mul64 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xFFFFFFFF
  let a1 := a >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let p0 := mul32 a0 b0
  let p2 := mul32 a1 b1
  let p1 := mul32 (a0 ^^^ a1) (b0 ^^^ b1)
  let lo := p0 ^^^ p2
  ((p1 ^^^ lo ^^^ mulByZ5 p2) <<< 32) ||| lo

/-- Multiplication by the level-6 generator `Z 6`. -/
@[inline] def mulByZ6 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  ((v0 ^^^ mulByZ5 v1) <<< 32) ||| v1

/-- GF(2^64) squaring. -/
def sq64 (v : UInt64) : UInt64 :=
  let s0 := sq32 (v &&& 0xFFFFFFFF)
  let s1 := sq32 (v >>> 32)
  ((mulByZ5 s1) <<< 32) ||| (s0 ^^^ s1)

/-- GF(2^64) inversion (`0 ↦ 0`). -/
def inv64 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  let next := v0 ^^^ mulByZ5 v1
  let delta := mul32 v0 next ^^^ sq32 v1
  let d := inv32 delta
  ((mul32 d v1) <<< 32) ||| (mul32 d next)

/-! ## Range bounds

Every operation maps values below `2 ^ s` to values below `2 ^ s`. The bounds feed the
`FastBT` carrier below and double as the skeleton for the follow-up `_toNat` spec proofs.
The shift/mask helpers cross into `ℕ` once; the per-width lemmas chain them. -/

private theorem and_mask_lt (s : ℕ) {a m : UInt64} (hm : m.toNat = 2 ^ s - 1) :
    (a &&& m).toNat < 2 ^ s := by
  rw [UInt64.toNat_and]
  exact Nat.and_lt_two_pow _ (by rw [hm]; exact Nat.sub_lt (Nat.two_pow_pos s) Nat.one_pos)

private theorem xor_lt {x y : UInt64} {s : ℕ} (hx : x.toNat < 2 ^ s) (hy : y.toNat < 2 ^ s) :
    (x ^^^ y).toNat < 2 ^ s := by
  rw [UInt64.toNat_xor]
  exact Nat.xor_lt_two_pow hx hy

private theorem shiftRight_lt (s : ℕ) {a sh : UInt64} {t : ℕ} (hsh : sh.toNat = s)
    (hs : s < 64) (ha : a.toNat < 2 ^ (s + t)) : (a >>> sh).toNat < 2 ^ t := by
  rw [UInt64.toNat_shiftRight, hsh, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact ha)

private theorem join_lt (s : ℕ) {hi lo sh : UInt64} (hsh : sh.toNat = s) (hs : 2 * s ≤ 64)
    (hhi : hi.toNat < 2 ^ s) (hlo : lo.toNat < 2 ^ s) :
    ((hi <<< sh) ||| lo).toNat < 2 ^ (2 * s) := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, hsh, Nat.mod_eq_of_lt (by omega : s < 64)]
  refine Nat.or_lt_two_pow ?_ (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by omega) (by omega)))
  have hval : hi.toNat <<< s < 2 ^ (2 * s) := by
    rw [Nat.shiftLeft_eq, Nat.two_mul, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos s)).mpr hhi
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hval

/-! ### Proof-side recursive twins

The runtime ladder is unrolled for code generation; proofs run over recursive twins
defined by structural recursion on the level, connected to each rung by `rfl`
(`mul8_eq_rec`, ...). Bounds follow by one induction per operation; the follow-up
correctness proofs against `concrete_mul` will ride the same twins. Meaningful for
levels `k ≤ 6` only (one word). -/

/-- Recursive twin of the `mulByZk` ladder. -/
def mulByZRec : ℕ → UInt64 → UInt64
  | 0, v => v
  | k + 1, v =>
    let sh := UInt64.ofNat (2 ^ k)
    let m := ((1 : UInt64) <<< sh) - 1
    let v0 := v &&& m
    let v1 := v >>> sh
    ((v0 ^^^ mulByZRec k v1) <<< sh) ||| v1

/-- Recursive twin of the multiplication ladder. -/
def mulRec : ℕ → UInt64 → UInt64 → UInt64
  | 0, a, b => a &&& b
  | k + 1, a, b =>
    let sh := UInt64.ofNat (2 ^ k)
    let m := ((1 : UInt64) <<< sh) - 1
    let a0 := a &&& m
    let a1 := a >>> sh
    let b0 := b &&& m
    let b1 := b >>> sh
    let p0 := mulRec k a0 b0
    let p2 := mulRec k a1 b1
    let p1 := mulRec k (a0 ^^^ a1) (b0 ^^^ b1)
    let lo := p0 ^^^ p2
    ((p1 ^^^ lo ^^^ mulByZRec k p2) <<< sh) ||| lo

private theorem toNat_ofNat_two_pow {k : ℕ} (hk : k ≤ 5) :
    (UInt64.ofNat (2 ^ k)).toNat = 2 ^ k :=
  UInt64.toNat_ofNat_of_lt'
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by norm_num [UInt64.size]))

private theorem toNat_mask_two_pow {k : ℕ} (hk : k ≤ 5) :
    (((1 : UInt64) <<< UInt64.ofNat (2 ^ k)) - 1).toNat = 2 ^ 2 ^ k - 1 := by
  have h32 : 2 ^ k ≤ 32 := by
    calc 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) hk
      _ = 32 := rfl
  have hpow : 2 ^ 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) h32
  have hshift : ((1 : UInt64) <<< UInt64.ofNat (2 ^ k)).toNat = 2 ^ 2 ^ k := by
    rw [UInt64.toNat_shiftLeft, toNat_ofNat_two_pow hk,
      show (1 : UInt64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 ^ k < 64), Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hpow (by norm_num))
  have hle : (1 : UInt64) ≤ (1 : UInt64) <<< UInt64.ofNat (2 ^ k) := by
    rw [UInt64.le_iff_toNat_le, hshift]
    exact Nat.two_pow_pos _
  rw [UInt64.toNat_sub_of_le _ _ hle, hshift]
  rfl

/-- The arithmetic facts every inductive step needs about the half-width `2 ^ k`. -/
private theorem rec_step_bounds {k : ℕ} (hk : k + 1 ≤ 6) :
    k ≤ 5 ∧ 2 * 2 ^ k ≤ 64 ∧ 2 ^ k + 2 ^ k = 2 ^ (k + 1) ∧
      (2 : ℕ) ^ 2 ^ (k + 1) = 2 ^ (2 * 2 ^ k) := by
  have hk5 : k ≤ 5 := by omega
  have h32 : 2 ^ k ≤ 32 := Nat.pow_le_pow_right (by omega) hk5
  exact ⟨hk5, by omega, by rw [Nat.pow_succ]; omega, by rw [Nat.pow_succ, Nat.mul_comm]⟩

/-- One-word `mulByZ` bound, by induction on the level. -/
theorem mulByZRec_lt : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64),
    v.toNat < 2 ^ 2 ^ k → (mulByZRec k v).toNat < 2 ^ 2 ^ k
  | 0, _, _, hv => hv
  | k + 1, hk, v, hv => by
    obtain ⟨hk5, h2s, hsplit, hpow⟩ := rec_step_bounds hk
    have hv' : v.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact hv
    have hv0 := and_mask_lt (2 ^ k) (a := v) (toNat_mask_two_pow hk5)
    have hv1 := shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) hv'
    have hrec := mulByZRec_lt k (by omega) _ hv1
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s (xor_lt hv0 hrec) hv1

/-- One-word multiplication bound, by induction on the level. -/
theorem mulRec_lt : ∀ (k : ℕ), k ≤ 6 → ∀ (a b : UInt64),
    a.toNat < 2 ^ 2 ^ k → b.toNat < 2 ^ 2 ^ k → (mulRec k a b).toNat < 2 ^ 2 ^ k
  | 0, _, a, b, ha, _ => by
    show (a &&& b).toNat < 2 ^ 2 ^ 0
    exact Nat.lt_of_le_of_lt (by rw [UInt64.toNat_and]; exact Nat.and_le_left) ha
  | k + 1, hk, a, b, ha, hb => by
    obtain ⟨hk5, h2s, hsplit, hpow⟩ := rec_step_bounds hk
    have ha' : a.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact ha
    have hb' : b.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact hb
    have ha0 := and_mask_lt (2 ^ k) (a := a) (toNat_mask_two_pow hk5)
    have ha1 := shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) ha'
    have hb0 := and_mask_lt (2 ^ k) (a := b) (toNat_mask_two_pow hk5)
    have hb1 := shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) hb'
    have hp0 := mulRec_lt k (by omega) _ _ ha0 hb0
    have hp2 := mulRec_lt k (by omega) _ _ ha1 hb1
    have hp1 := mulRec_lt k (by omega) _ _ (xor_lt ha0 ha1) (xor_lt hb0 hb1)
    have hlo := xor_lt hp0 hp2
    have hz := mulByZRec_lt k (by omega) _ hp2
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s
      (xor_lt (xor_lt hp1 hlo) hz) hlo

/-! ### Rung-twin bridges and per-width bounds -/

theorem mulByZ1_eq_rec (v : UInt64) : mulByZ1 v = mulByZRec 1 v := rfl
theorem mulByZ2_eq_rec (v : UInt64) : mulByZ2 v = mulByZRec 2 v := rfl
theorem mulByZ3_eq_rec (v : UInt64) : mulByZ3 v = mulByZRec 3 v := rfl
theorem mulByZ4_eq_rec (v : UInt64) : mulByZ4 v = mulByZRec 4 v := rfl
theorem mulByZ5_eq_rec (v : UInt64) : mulByZ5 v = mulByZRec 5 v := rfl

theorem mul2_eq_rec (a b : UInt64) : mul2 a b = mulRec 1 a b := rfl

theorem mul4_eq_rec (a b : UInt64) : mul4 a b = mulRec 2 a b := by
  conv_rhs => rw [mulRec]
  simp only [← mul2_eq_rec, ← mulByZ1_eq_rec]
  rfl

theorem mul8_eq_rec (a b : UInt64) : mul8 a b = mulRec 3 a b := by
  conv_rhs => rw [mulRec]
  simp only [← mul4_eq_rec, ← mulByZ2_eq_rec]
  rfl

theorem mul16_eq_rec (a b : UInt64) : mul16 a b = mulRec 4 a b := by
  conv_rhs => rw [mulRec]
  simp only [← mul8_eq_rec, ← mulByZ3_eq_rec]
  rfl

theorem mul32_eq_rec (a b : UInt64) : mul32 a b = mulRec 5 a b := by
  conv_rhs => rw [mulRec]
  simp only [← mul16_eq_rec, ← mulByZ4_eq_rec]
  rfl

theorem mul64_eq_rec (a b : UInt64) : mul64 a b = mulRec 6 a b := by
  conv_rhs => rw [mulRec]
  simp only [← mul32_eq_rec, ← mulByZ5_eq_rec]
  rfl


theorem mul8_lt {a b : UInt64} (ha : a.toNat < 2 ^ 8) (hb : b.toNat < 2 ^ 8) :
    (mul8 a b).toNat < 2 ^ 8 := by
  rw [mul8_eq_rec]; exact mulRec_lt 3 (by omega) a b ha hb

theorem mul16_lt {a b : UInt64} (ha : a.toNat < 2 ^ 16) (hb : b.toNat < 2 ^ 16) :
    (mul16 a b).toNat < 2 ^ 16 := by
  rw [mul16_eq_rec]; exact mulRec_lt 4 (by omega) a b ha hb

theorem mul32_lt {a b : UInt64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (mul32 a b).toNat < 2 ^ 32 := by
  rw [mul32_eq_rec]; exact mulRec_lt 5 (by omega) a b ha hb

theorem mulByZ3_lt {v : UInt64} (hv : v.toNat < 2 ^ 8) : (mulByZ3 v).toNat < 2 ^ 8 := by
  rw [mulByZ3_eq_rec]; exact mulByZRec_lt 3 (by omega) v hv

theorem mulByZ4_lt {v : UInt64} (hv : v.toNat < 2 ^ 16) : (mulByZ4 v).toNat < 2 ^ 16 := by
  rw [mulByZ4_eq_rec]; exact mulByZRec_lt 4 (by omega) v hv

theorem mulByZ5_lt {v : UInt64} (hv : v.toNat < 2 ^ 32) : (mulByZ5 v).toNat < 2 ^ 32 := by
  rw [mulByZ5_eq_rec]; exact mulByZRec_lt 5 (by omega) v hv

/-! ## Multiplicative correctness

`mulByZRec` and `mulRec` agree with `concrete_mul` on in-range words, by induction on
the level. Statements are phrased through `fromNat`, so the spec side reasons inside
`ConcreteBTField` with its `Field` and `CharP 2` instances; the rung bridges then carry
the result to the unrolled ladder and the carrier below. -/

private theorem toNat_fromNat {k n : ℕ} (h : n < 2 ^ 2 ^ k) :
    BitVec.toNat (fromNat (k := k) n) = n := by
  show (BitVec.ofNat (2 ^ k) n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem shiftRight_toNat {k : ℕ} (hk : k ≤ 5) (a : UInt64) :
    (a >>> UInt64.ofNat (2 ^ k)).toNat = a.toNat >>> 2 ^ k := by
  have h32 : 2 ^ k ≤ 32 := Nat.pow_le_pow_right (by omega) hk
  rw [UInt64.toNat_shiftRight, toNat_ofNat_two_pow hk, Nat.mod_eq_of_lt (by omega)]

private theorem and_mask_toNat {k : ℕ} (hk : k ≤ 5) (a : UInt64) :
    (a &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat
      = a.toNat &&& (2 ^ 2 ^ k - 1) := by
  rw [UInt64.toNat_and, toNat_mask_two_pow hk]

private theorem join_word_toNat {k : ℕ} (hk : k + 1 ≤ 6) {hi : UInt64}
    (hhi : hi.toNat < 2 ^ 2 ^ k) (lo : UInt64) :
    ((hi <<< UInt64.ofNat (2 ^ k)) ||| lo).toNat = hi.toNat <<< 2 ^ k ||| lo.toNat := by
  obtain ⟨hk5, h2s, hsplit, hpow⟩ := rec_step_bounds hk
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, toNat_ofNat_two_pow hk5,
    Nat.mod_eq_of_lt (show 2 ^ k < 64 by omega),
    Nat.mod_eq_of_lt (show hi.toNat <<< 2 ^ k < 2 ^ 64 by
      rw [Nat.shiftLeft_eq]
      calc hi.toNat * 2 ^ 2 ^ k
          < 2 ^ 2 ^ k * 2 ^ 2 ^ k := (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
        _ = 2 ^ (2 * 2 ^ k) := by rw [Nat.two_mul, Nat.pow_add]
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h2s)]

private theorem nat_join_shiftRight {H L s : ℕ} (hL : L < 2 ^ s) :
    (H <<< s ||| L) >>> s = H := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mul_comm H (2 ^ s), Nat.mul_add_div (Nat.two_pow_pos s), Nat.div_eq_of_lt hL,
    Nat.add_zero]

private theorem nat_join_and {H L s : ℕ} (hL : L < 2 ^ s) :
    (H <<< s ||| L) &&& (2 ^ s - 1) = L := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
    Nat.mul_comm H (2 ^ s), Nat.mul_add_mod, Nat.mod_eq_of_lt hL]

private theorem fromNat_xor {k : ℕ} (x y : UInt64) :
    fromNat (k := k) (x ^^^ y).toNat = fromNat x.toNat + fromNat y.toNat := by
  rw [UInt64.toNat_xor]
  exact sum_fromNat_eq_from_xor_Nat _ _

private theorem fromNat_join {k : ℕ} (hk : k + 1 ≤ 6) {hi lo : UInt64}
    (hhi : hi.toNat < 2 ^ 2 ^ k) (hlo : lo.toNat < 2 ^ 2 ^ k) :
    fromNat (k := k + 1) ((hi <<< UInt64.ofNat (2 ^ k)) ||| lo).toNat
      = (《 fromNat (k := k) hi.toNat, fromNat (k := k) lo.toNat 》 :
          ConcreteBTField (k + 1)) := by
  obtain ⟨hk5, h2s, hsplit, hpow⟩ := rec_step_bounds hk
  have hX := join_word_toNat hk hhi lo
  have hXlt : ((hi <<< UInt64.ofNat (2 ^ k)) ||| lo).toNat < 2 ^ 2 ^ (k + 1) := by
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s hhi hlo
  refine (join_eq_bitvec_iff_fromNat (Nat.succ_pos k) _ _ _).mpr ⟨?_, ?_⟩
  · simp only [Nat.succ_sub_one]
    congr 1
    rw [toNat_fromNat hXlt, hX, nat_join_shiftRight hlo]
  · simp only [Nat.succ_sub_one]
    congr 1
    rw [toNat_fromNat hXlt, hX, nat_join_and hlo]

private theorem split_fromNat {k : ℕ} (hk : k + 1 ≤ 6) {a : UInt64}
    (ha : a.toNat < 2 ^ 2 ^ (k + 1)) :
    split (Nat.succ_pos k) (fromNat (k := k + 1) a.toNat)
      = (fromNat (k := k) (a >>> UInt64.ofNat (2 ^ k)).toNat,
         fromNat (k := k) (a &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat) := by
  have hk5 : k ≤ 5 := by omega
  refine (split_bitvec_eq_iff_fromNat (Nat.succ_pos k) _ _ _).mpr ⟨?_, ?_⟩
  · simp only [Nat.succ_sub_one]
    congr 1
    rw [shiftRight_toNat hk5, toNat_fromNat ha]
  · simp only [Nat.succ_sub_one]
    congr 1
    rw [and_mask_toNat hk5, toNat_fromNat ha]

private theorem two_eq_zero (k : ℕ) : (2 : ConcreteBTField k) = 0 := by
  simpa using CharP.cast_eq_zero (ConcreteBTField k) 2

/-- `concrete_mul`'s one-level structure theorem, restated with all indices at the
half level `k` (the original lives at `k + 1 - 1`, which blocks syntactic rewriting). -/
private theorem concrete_mul_step {k : ℕ} (a b : ConcreteBTField (k + 1))
    {a₁ a₀ b₁ b₀ : ConcreteBTField k}
    (ha : (a₁, a₀) = split (Nat.succ_pos k) a) (hb : (b₁, b₀) = split (Nat.succ_pos k) b) :
    concrete_mul a b
      = (《 concrete_mul a₀ b₁ + concrete_mul b₀ a₁
            + concrete_mul (concrete_mul a₁ b₁) (Z k),
          concrete_mul a₀ b₀ + concrete_mul a₁ b₁ 》 : ConcreteBTField (k + 1)) :=
  (getBTFResult (k + 1)).mul_eq a b (Nat.succ_pos k) ha hb

/-- `mulByZRec` computes multiplication by the level generator on the spec side. -/
theorem mulByZRec_correct : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64), v.toNat < 2 ^ 2 ^ k →
    fromNat (k := k) (mulByZRec k v).toNat = concrete_mul (fromNat v.toNat) (Z k)
  | 0, _, v, hv => by
    show fromNat (k := 0) v.toNat = concrete_mul (fromNat v.toNat) (Z 0)
    rw [show Z 0 = ConcreteBinaryTower.one from rfl, concrete_mul_one0]
  | k + 1, hk, v, hv => by
    obtain ⟨hk5, h2s, hsplit, hpow⟩ := rec_step_bounds hk
    have hv' : v.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact hv
    have hv0 := and_mask_lt (2 ^ k) (a := v) (toNat_mask_two_pow hk5)
    have hv1 := shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) hv'
    have hz := mulByZRec_lt k (by omega) _ hv1
    have hmul : ∀ (x y : ConcreteBTField k), concrete_mul x y = x * y := fun _ _ => rfl
    have hIH := mulByZRec_correct k (by omega) (v >>> UInt64.ofNat (2 ^ k)) hv1
    have hZsplit : ((one : ConcreteBTField k), (zero : ConcreteBTField k))
        = split (Nat.succ_pos k) (Z (k + 1)) := (split_Z (Nat.succ_pos k)).symm
    have hme := concrete_mul_step (fromNat v.toNat) (Z (k + 1))
      (split_fromNat hk hv).symm hZsplit
    simp only [mulByZRec]
    rw [fromNat_join hk (xor_lt hv0 hz) hv1]
    rw [fromNat_xor]
    rw [hIH]
    refine Eq.trans ?_ hme.symm
    simp only [hmul, one_is_1, zero_is_0, mul_one, mul_zero, zero_mul, add_zero, zero_add]

/-- `mulRec` agrees with `concrete_mul` on in-range words. -/
theorem mulRec_correct : ∀ (k : ℕ), k ≤ 6 → ∀ (a b : UInt64),
    a.toNat < 2 ^ 2 ^ k → b.toNat < 2 ^ 2 ^ k →
    fromNat (k := k) (mulRec k a b).toNat = concrete_mul (fromNat a.toNat) (fromNat b.toNat)
  | 0, _, a, b, ha, hb => by
    have ha' : a = 0 ∨ a = 1 := by
      rcases (by omega : a.toNat = 0 ∨ a.toNat = 1) with h | h
      · exact Or.inl (UInt64.toNat_inj.mp h)
      · exact Or.inr (UInt64.toNat_inj.mp h)
    have hb' : b = 0 ∨ b = 1 := by
      rcases (by omega : b.toNat = 0 ∨ b.toNat = 1) with h | h
      · exact Or.inl (UInt64.toNat_inj.mp h)
      · exact Or.inr (UInt64.toNat_inj.mp h)
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · show ConcreteBinaryTower.zero = concrete_mul zero zero
      rw [concrete_zero_mul0]
    · show ConcreteBinaryTower.zero = concrete_mul zero one
      rw [concrete_zero_mul0]
    · show ConcreteBinaryTower.zero = concrete_mul one zero
      rw [concrete_mul_zero0]
    · show ConcreteBinaryTower.one = concrete_mul one one
      rw [concrete_mul_one0]
  | k + 1, hk, a, b, ha, hb => by
    obtain ⟨hk5, h2s, hsplit, hpow⟩ := rec_step_bounds hk
    have ha' : a.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact ha
    have hb' : b.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact hb
    have ha0 := and_mask_lt (2 ^ k) (a := a) (toNat_mask_two_pow hk5)
    have ha1 := shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) ha'
    have hb0 := and_mask_lt (2 ^ k) (a := b) (toNat_mask_two_pow hk5)
    have hb1 := shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) hb'
    have hp0 := mulRec_lt k (by omega) _ _ ha0 hb0
    have hp2 := mulRec_lt k (by omega) _ _ ha1 hb1
    have hp1 := mulRec_lt k (by omega) _ _ (xor_lt ha0 ha1) (xor_lt hb0 hb1)
    have hz := mulByZRec_lt k (by omega) _ hp2
    have hmul : ∀ (x y : ConcreteBTField k), concrete_mul x y = x * y := fun _ _ => rfl
    have hZ := mulByZRec_correct k (by omega) _ hp2
    have h00 := mulRec_correct k (by omega) _ _ ha0 hb0
    have h11 := mulRec_correct k (by omega) _ _ ha1 hb1
    have hss := mulRec_correct k (by omega) _ _ (xor_lt ha0 ha1) (xor_lt hb0 hb1)
    have hme := concrete_mul_step (fromNat a.toNat) (fromNat b.toNat)
      (split_fromNat hk ha).symm (split_fromNat hk hb).symm
    simp only [mulRec]
    rw [fromNat_join hk (xor_lt (xor_lt hp1 (xor_lt hp0 hp2)) hz) (xor_lt hp0 hp2)]
    simp only [fromNat_xor]
    rw [hZ]
    rw [h00]
    rw [h11]
    rw [hss]
    refine Eq.trans ?_ hme.symm
    simp only [hmul, fromNat_xor]
    refine congrArg₂ (fun x y : ConcreteBTField k => (《 x, y 》 : ConcreteBTField (k + 1))) ?_ ?_
    · linear_combination (fromNat (k := k) (a &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat
          * fromNat (k := k) (b &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat
        + fromNat (k := k) (a >>> UInt64.ofNat (2 ^ k)).toNat
          * fromNat (k := k) (b >>> UInt64.ofNat (2 ^ k)).toNat) * two_eq_zero k
    · rfl

/-! ## Carrier -/

/-- A level-`k` tower field element in packed form: the low `2 ^ 2 ^ k` bits of a
machine word, upper bits zero. Same bit layout as `ConcreteBTField k`, so conversion
preserves `toNat`. The bound is vacuous at `k = 6`; widths above 64 bits use
`FastBT128`. -/
structure FastBT (k : ℕ) where
  val : UInt64
  isLt : val.toNat < 2 ^ 2 ^ k

instance {k : ℕ} : DecidableEq (FastBT k) := fun a b =>
  decidable_of_iff (a.val = b.val) (by cases a; cases b; simp only [FastBT.mk.injEq])

/-- Truncating constructor from `ℕ`. -/
@[inline] def ofNat (k n : ℕ) : FastBT k :=
  .mk (UInt64.ofNat (n % 2 ^ 2 ^ k)) <| by
    show n % 2 ^ 2 ^ k % 2 ^ 64 < 2 ^ 2 ^ k
    exact Nat.mod_lt_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- The canonical value of a packed element. -/
def FastBT.toNat {k : ℕ} (x : FastBT k) : ℕ := x.val.toNat

variable {k : ℕ}

def zero : FastBT k := .mk 0 (Nat.two_pow_pos _)

def one : FastBT k := .mk 1 (Nat.one_lt_two_pow_iff.mpr (Nat.two_pow_pos k).ne')

instance : Zero (FastBT k) := ⟨zero⟩
instance : One (FastBT k) := ⟨one⟩

/-- Addition is bitwise XOR. -/
@[inline] def add (a b : FastBT k) : FastBT k := .mk (a.val ^^^ b.val) (xor_lt a.isLt b.isLt)

instance : Add (FastBT k) where add

instance : Neg (FastBT k) := ⟨id⟩
instance : Sub (FastBT k) where sub a b := a + b
instance : SMul ℕ (FastBT k) := ⟨fun n x => if n % 2 = 0 then 0 else x⟩
instance : SMul ℤ (FastBT k) := ⟨fun n x => if n % 2 = 0 then 0 else x⟩

@[simp] theorem val_zero : (0 : FastBT k).val = 0 := rfl
@[simp] theorem val_one : (1 : FastBT k).val = 1 := rfl
@[simp] theorem val_add (a b : FastBT k) : (a + b).val = a.val ^^^ b.val := rfl
@[simp] theorem neg_def (a : FastBT k) : -a = a := rfl
@[simp] theorem sub_def (a b : FastBT k) : a - b = a + b := rfl

/-! ## Conversions -/

/-- The bridge into the `BitVec` model; bit layouts agree, so this is `toNat`-exact. -/
def toConcrete (x : FastBT k) : ConcreteBTField k := fromNat x.val.toNat

/-- Master bridge lemma: `toConcrete` preserves the numeric value. -/
@[simp] theorem toConcrete_toNat (x : FastBT k) :
    BitVec.toNat (toConcrete x) = x.val.toNat := by
  show (BitVec.ofNat (2 ^ k) x.val.toNat).toNat = x.val.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

theorem toConcrete_injective : Function.Injective (toConcrete (k := k)) := by
  intro a b h
  have hval : a.val = b.val := by
    have := congrArg BitVec.toNat h
    rw [toConcrete_toNat, toConcrete_toNat] at this
    exact UInt64.toNat_inj.mp this
  cases a; cases b
  simp only [FastBT.mk.injEq]
  exact hval

@[simp] theorem toConcrete_zero : toConcrete (0 : FastBT k) = 0 := by
  rw [← zero_is_0]
  show fromNat (0 : UInt64).toNat = ConcreteBinaryTower.zero
  rfl

@[simp] theorem toConcrete_one : toConcrete (1 : FastBT k) = 1 := by
  rw [← one_is_1]
  show fromNat (1 : UInt64).toNat = ConcreteBinaryTower.one
  rfl

@[simp] theorem toConcrete_add (a b : FastBT k) :
    toConcrete (a + b) = toConcrete a + toConcrete b := by
  show fromNat ((a + b).val.toNat) = _
  rw [val_add, UInt64.toNat_xor]
  exact sum_fromNat_eq_from_xor_Nat _ _

@[simp] theorem toConcrete_neg (a : FastBT k) : toConcrete (-a) = -(toConcrete a) := rfl

@[simp] theorem toConcrete_sub (a b : FastBT k) :
    toConcrete (a - b) = toConcrete a - toConcrete b := by
  rw [sub_def, toConcrete_add, sub_eq_add_neg, ← toConcrete_neg, neg_def]

private theorem toConcrete_if_zero {p : Prop} [Decidable p] (x : FastBT k) :
    toConcrete (if p then 0 else x) = if p then ConcreteBinaryTower.zero else toConcrete x := by
  by_cases h : p
  · rw [if_pos h, if_pos h, toConcrete_zero]
    exact zero_is_0.symm
  · rw [if_neg h, if_neg h]

theorem toConcrete_nsmul (n : ℕ) (x : FastBT k) :
    toConcrete (n • x) = n • toConcrete x := toConcrete_if_zero x

theorem toConcrete_zsmul (n : ℤ) (x : FastBT k) :
    toConcrete (n • x) = n • toConcrete x := toConcrete_if_zero x

instance : AddCommGroup (FastBT k) :=
  toConcrete_injective.addCommGroup toConcrete toConcrete_zero toConcrete_add
    toConcrete_neg toConcrete_sub (fun x n => toConcrete_nsmul n x)
    (fun x n => toConcrete_zsmul n x)

/-! ## Multiplication

`Mul` instances per usable width; the bounds come from the range lemmas above.
Correctness against `concrete_mul` (and with it `CommRing`/`Field` instances via
transport) is the follow-up. -/

/-- Level-3 elements, GF(2^8). -/
abbrev BT8 := FastBT 3
/-- Level-4 elements, GF(2^16). -/
abbrev BT16 := FastBT 4
/-- Level-5 elements, GF(2^32). -/
abbrev BT32 := FastBT 5
/-- Level-6 elements, GF(2^64). -/
abbrev BT64 := FastBT 6

/-- GF(2^8) carrier multiplication. -/
@[inline] def BT8.mul (a b : BT8) : BT8 := .mk (mul8 a.val b.val) (mul8_lt a.isLt b.isLt)
/-- GF(2^16) carrier multiplication. -/
@[inline] def BT16.mul (a b : BT16) : BT16 := .mk (mul16 a.val b.val) (mul16_lt a.isLt b.isLt)
/-- GF(2^32) carrier multiplication. -/
@[inline] def BT32.mul (a b : BT32) : BT32 := .mk (mul32 a.val b.val) (mul32_lt a.isLt b.isLt)
/-- GF(2^64) carrier multiplication. -/
@[inline] def BT64.mul (a b : BT64) : BT64 := .mk (mul64 a.val b.val) (UInt64.toNat_lt _)

instance : Mul BT8 := ⟨BT8.mul⟩
instance : Mul BT16 := ⟨BT16.mul⟩
instance : Mul BT32 := ⟨BT32.mul⟩
instance : Mul BT64 := ⟨BT64.mul⟩

@[simp] theorem val_mul_bt8 (a b : BT8) : (a * b).val = mul8 a.val b.val := rfl
@[simp] theorem val_mul_bt16 (a b : BT16) : (a * b).val = mul16 a.val b.val := rfl
@[simp] theorem val_mul_bt32 (a b : BT32) : (a * b).val = mul32 a.val b.val := rfl
@[simp] theorem val_mul_bt64 (a b : BT64) : (a * b).val = mul64 a.val b.val := rfl

@[simp] theorem toConcrete_mul_bt8 (a b : BT8) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul8 a.val b.val).toNat = _
  rw [mul8_eq_rec]
  exact mulRec_correct 3 (by omega) a.val b.val a.isLt b.isLt

@[simp] theorem toConcrete_mul_bt16 (a b : BT16) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul16 a.val b.val).toNat = _
  rw [mul16_eq_rec]
  exact mulRec_correct 4 (by omega) a.val b.val a.isLt b.isLt

@[simp] theorem toConcrete_mul_bt32 (a b : BT32) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul32 a.val b.val).toNat = _
  rw [mul32_eq_rec]
  exact mulRec_correct 5 (by omega) a.val b.val a.isLt b.isLt

@[simp] theorem toConcrete_mul_bt64 (a b : BT64) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul64 a.val b.val).toNat = _
  rw [mul64_eq_rec]
  exact mulRec_correct 6 (by omega) a.val b.val a.isLt b.isLt

/-- Multiply by the level generator `Z k`. One-word levels only (`k ≤ 6`); the level is
matched at compile time for literal `k`, so per-width call sites pay no dispatch. -/
@[inline] def FastBT.mulByZ {k : ℕ} (a : FastBT k) (_hk : k ≤ 6 := by omega) : FastBT k :=
  match k, a with
  | 0, a => a
  | 1, a => .mk (mulByZ1 a.val) (by rw [mulByZ1_eq_rec]; exact mulByZRec_lt 1 (by omega) _ a.isLt)
  | 2, a => .mk (mulByZ2 a.val) (by rw [mulByZ2_eq_rec]; exact mulByZRec_lt 2 (by omega) _ a.isLt)
  | 3, a => .mk (mulByZ3 a.val) (mulByZ3_lt a.isLt)
  | 4, a => .mk (mulByZ4 a.val) (mulByZ4_lt a.isLt)
  | 5, a => .mk (mulByZ5 a.val) (mulByZ5_lt a.isLt)
  | 6, a => .mk (mulByZ6 a.val) (UInt64.toNat_lt _)
  | _ + 7, a => a

/-! ## Level 7: GF(2^128)

The tower split falls exactly on the limb boundary, so the halves are the limbs.
Runtime operations only; the algebraic instances follow with the correctness proofs. -/

/-- A level-7 tower field element as two limbs, `lo` the low half. -/
structure FastBT128 where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, Inhabited

namespace FastBT128

instance : Zero FastBT128 := ⟨0, 0⟩
instance : One FastBT128 := ⟨1, 0⟩

/-- Addition is limbwise XOR. -/
@[inline] def add (a b : FastBT128) : FastBT128 := ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

/-- Multiplication: Karatsuba over the limbs with a `Z 6` generator reduction. -/
@[inline] def mul (a b : FastBT128) : FastBT128 :=
  let p0 := mul64 a.lo b.lo
  let p2 := mul64 a.hi b.hi
  let p1 := mul64 (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
  let lo := p0 ^^^ p2
  ⟨lo, p1 ^^^ lo ^^^ mulByZ6 p2⟩

instance : Add FastBT128 := ⟨add⟩
instance : Neg FastBT128 := ⟨id⟩
instance : Sub FastBT128 where sub a b := a + b
instance : Mul FastBT128 := ⟨mul⟩

/-- Multiply by the level-7 generator `Z 7`: swap halves, fold `Z 6` into the new high. -/
@[inline] def mulByZ (v : FastBT128) : FastBT128 := ⟨v.hi, v.lo ^^^ mulByZ6 v.hi⟩

/-- Squaring: the Karatsuba cross term vanishes in characteristic 2. -/
@[inline] def square (v : FastBT128) : FastBT128 :=
  let s0 := sq64 v.lo
  let s1 := sq64 v.hi
  ⟨s0 ^^^ s1, mulByZ6 s1⟩

/-- Inversion by quadratic descent (`0 ↦ 0`); same recursion as `concrete_inv`. -/
@[inline] def inv (v : FastBT128) : FastBT128 :=
  let next := v.lo ^^^ mulByZ6 v.hi
  let delta := mul64 v.lo next ^^^ sq64 v.hi
  let d := inv64 delta
  ⟨mul64 d next, mul64 d v.hi⟩

/-- Truncating constructor from `ℕ`, low limb first. -/
def ofNat (n : ℕ) : FastBT128 := ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64)⟩

/-- The canonical value of a two-limb element. -/
def toNat (v : FastBT128) : ℕ := v.lo.toNat + v.hi.toNat * 2 ^ 64

end FastBT128

end ConcreteBinaryTower.Fast
