/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Binary.Tower.Concrete.Field
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Tactic.LinearCombination

/-!
# Fast Binary Tower Arithmetic

Packed machine-word implementation of `ConcreteBTField` arithmetic with the same bit
layout: a level-`k` element is the low `2 ^ 2 ^ k` bits of one `UInt64` for `k ≤ 6`, and
a pair of limbs at level 7. Multiplication is Karatsuba with an `O(width)`
multiply-by-generator reduction; mul, square, and inverse are proven against the
concrete tower by induction over recursive twins, giving `Field` instances at each
one-word width and at the two-limb GF(2^128), with bundled ring isomorphisms onto the
concrete tower (`ringEquivBT*`, `FastBT128.ringEquiv`).
-/

namespace ConcreteBinaryTower.Fast

/-! ## Raw word operations

Names carry the operand bit width (`mul8` multiplies level-3 values in the low 8 bits);
`mulByZk` multiplies by the tower generator `Z k`. A multiplication rung recombines the
Karatsuba half-products `p0 = a₀b₀`, `p2 = a₁b₁`, `p1 = (a₀+a₁)(b₀+b₁)` as
`lo = p0 + p2`, `hi = p1 + lo + Z·p2`; squaring drops the cross term; inversion is the
quadratic descent of `concrete_inv`. Inputs are assumed in range. -/

/-- GF(4) multiplication (level 1). `Z 0 = 1` collapses the generic recombination
`hi = p1 + lo + Z·p2` to `hi = p1 + p0`, saving a xor on the ladder's hottest rung. -/
@[inline] def mul2 (a b : UInt64) : UInt64 :=
  let a0 := a &&& 1
  let a1 := a >>> 1
  let b0 := b &&& 1
  let b1 := b >>> 1
  let p0 := a0 &&& b0
  let p2 := a1 &&& b1
  let p1 := (a0 ^^^ a1) &&& (b0 ^^^ b1)
  ((p1 ^^^ p0) <<< 1) ||| (p0 ^^^ p2)

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

/-- GF(4) inversion (`0 ↦ 0`), in the shape of the recursive twin so `inv2_eq_rec`
is `rfl`. -/
@[inline] def inv2 (v : UInt64) : UInt64 :=
  let v0 := v &&& 1
  let v1 := v >>> 1
  let next := v0 ^^^ v1
  let delta := (v0 &&& next) ^^^ v1
  ((delta &&& v1) <<< 1) ||| (delta &&& next)

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

/-- GF(2^32) multiplication (level 5). Outlined: inlining the whole ladder above this
width exceeds the compiler's recursion depth. -/
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
@[inline] def inv32 (v : UInt64) : UInt64 :=
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
@[inline] def sq64 (v : UInt64) : UInt64 :=
  let s0 := sq32 (v &&& 0xFFFFFFFF)
  let s1 := sq32 (v >>> 32)
  ((mulByZ5 s1) <<< 32) ||| (s0 ^^^ s1)

/-- GF(2^64) inversion (`0 ↦ 0`). -/
@[inline] def inv64 (v : UInt64) : UInt64 :=
  let v0 := v &&& 0xFFFFFFFF
  let v1 := v >>> 32
  let next := v0 ^^^ mulByZ5 v1
  let delta := mul32 v0 next ^^^ sq32 v1
  let d := inv32 delta
  ((mul32 d v1) <<< 32) ||| (mul32 d next)

/-! ## Range bounds

Every operation maps values below `2 ^ s` to values below `2 ^ s`; the shift/mask
helpers cross into `ℕ` once and the per-width lemmas chain them. -/

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

The runtime ladder is unrolled for code generation; proofs run over structurally
recursive twins, connected to each rung by `rfl` bridges (`mul8_eq_rec`, ...) and
meaningful for `k ≤ 6` (one word). -/

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

/-- Recursive twin of the squaring ladder; level 0 is the identity (`v² = v` in GF(2)). -/
def sqRec : ℕ → UInt64 → UInt64
  | 0, v => v
  | k + 1, v =>
    let sh := UInt64.ofNat (2 ^ k)
    let m := ((1 : UInt64) <<< sh) - 1
    let s0 := sqRec k (v &&& m)
    let s1 := sqRec k (v >>> sh)
    ((mulByZRec k s1) <<< sh) ||| (s0 ^^^ s1)

/-- Recursive twin of the inversion ladder; level 0 is the identity. -/
def invRec : ℕ → UInt64 → UInt64
  | 0, v => v
  | k + 1, v =>
    let sh := UInt64.ofNat (2 ^ k)
    let m := ((1 : UInt64) <<< sh) - 1
    let v0 := v &&& m
    let v1 := v >>> sh
    let next := v0 ^^^ mulByZRec k v1
    let delta := mulRec k v0 next ^^^ sqRec k v1
    let d := invRec k delta
    ((mulRec k d v1) <<< sh) ||| (mulRec k d next)

/-! One-step unfoldings as `rfl` theorems, so proofs rewrite with these instead of
realizing each twin's equation lemmas over and over. -/

private theorem mulByZRec_succ (k : ℕ) (v : UInt64) :
    mulByZRec (k + 1) v =
      let sh := UInt64.ofNat (2 ^ k)
      let m := ((1 : UInt64) <<< sh) - 1
      let v0 := v &&& m
      let v1 := v >>> sh
      ((v0 ^^^ mulByZRec k v1) <<< sh) ||| v1 := rfl

private theorem mulRec_succ (k : ℕ) (a b : UInt64) :
    mulRec (k + 1) a b =
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
      ((p1 ^^^ lo ^^^ mulByZRec k p2) <<< sh) ||| lo := rfl

private theorem sqRec_succ (k : ℕ) (v : UInt64) :
    sqRec (k + 1) v =
      let sh := UInt64.ofNat (2 ^ k)
      let m := ((1 : UInt64) <<< sh) - 1
      let s0 := sqRec k (v &&& m)
      let s1 := sqRec k (v >>> sh)
      ((mulByZRec k s1) <<< sh) ||| (s0 ^^^ s1) := rfl

private theorem invRec_succ (k : ℕ) (v : UInt64) :
    invRec (k + 1) v =
      let sh := UInt64.ofNat (2 ^ k)
      let m := ((1 : UInt64) <<< sh) - 1
      let v0 := v &&& m
      let v1 := v >>> sh
      let next := v0 ^^^ mulByZRec k v1
      let delta := mulRec k v0 next ^^^ sqRec k v1
      let d := invRec k delta
      ((mulRec k d v1) <<< sh) ||| (mulRec k d next) := rfl

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

/-- Both halves of an in-range word are in range at the half level. -/
private theorem half_lt {k : ℕ} (hk : k + 1 ≤ 6) {v : UInt64}
    (hv : v.toNat < 2 ^ 2 ^ (k + 1)) :
    (v >>> UInt64.ofNat (2 ^ k)).toNat < 2 ^ 2 ^ k
      ∧ (v &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat < 2 ^ 2 ^ k := by
  obtain ⟨hk5, h2s, hsplit, _⟩ := rec_step_bounds hk
  have hv' : v.toNat < 2 ^ (2 ^ k + 2 ^ k) := by rw [hsplit]; exact hv
  exact ⟨shiftRight_lt (2 ^ k) (toNat_ofNat_two_pow hk5) (by omega) hv',
    and_mask_lt (2 ^ k) (toNat_mask_two_pow hk5)⟩

/-- One-word `mulByZ` bound, by induction on the level. -/
theorem mulByZRec_lt : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64),
    v.toNat < 2 ^ 2 ^ k → (mulByZRec k v).toNat < 2 ^ 2 ^ k
  | 0, _, _, hv => hv
  | k + 1, hk, v, hv => by
    obtain ⟨hk5, h2s, _, hpow⟩ := rec_step_bounds hk
    obtain ⟨hv1, hv0⟩ := half_lt hk hv
    have hrec := mulByZRec_lt k (Nat.le_of_succ_le hk) _ hv1
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s (xor_lt hv0 hrec) hv1

/-- One-word multiplication bound, by induction on the level. -/
theorem mulRec_lt : ∀ (k : ℕ), k ≤ 6 → ∀ (a b : UInt64),
    a.toNat < 2 ^ 2 ^ k → b.toNat < 2 ^ 2 ^ k → (mulRec k a b).toNat < 2 ^ 2 ^ k
  | 0, _, a, b, ha, _ => by
    show (a &&& b).toNat < 2 ^ 2 ^ 0
    exact Nat.lt_of_le_of_lt (by rw [UInt64.toNat_and]; exact Nat.and_le_left) ha
  | k + 1, hk, a, b, ha, hb => by
    obtain ⟨hk5, h2s, _, hpow⟩ := rec_step_bounds hk
    have hk6 : k ≤ 6 := Nat.le_of_succ_le hk
    obtain ⟨ha1, ha0⟩ := half_lt hk ha
    obtain ⟨hb1, hb0⟩ := half_lt hk hb
    have hp0 := mulRec_lt k hk6 _ _ ha0 hb0
    have hp2 := mulRec_lt k hk6 _ _ ha1 hb1
    have hp1 := mulRec_lt k hk6 _ _ (xor_lt ha0 ha1) (xor_lt hb0 hb1)
    have hlo := xor_lt hp0 hp2
    have hz := mulByZRec_lt k hk6 _ hp2
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s
      (xor_lt (xor_lt hp1 hlo) hz) hlo

/-- One-word squaring bound, by induction on the level. -/
theorem sqRec_lt : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64),
    v.toNat < 2 ^ 2 ^ k → (sqRec k v).toNat < 2 ^ 2 ^ k
  | 0, _, _, hv => hv
  | k + 1, hk, v, hv => by
    obtain ⟨hk5, h2s, _, hpow⟩ := rec_step_bounds hk
    have hk6 : k ≤ 6 := Nat.le_of_succ_le hk
    obtain ⟨hv1, hv0⟩ := half_lt hk hv
    have hs0 := sqRec_lt k hk6 _ hv0
    have hs1 := sqRec_lt k hk6 _ hv1
    have hz := mulByZRec_lt k hk6 _ hs1
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s hz (xor_lt hs0 hs1)

/-- One-word inversion bound, by induction on the level. -/
theorem invRec_lt : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64),
    v.toNat < 2 ^ 2 ^ k → (invRec k v).toNat < 2 ^ 2 ^ k
  | 0, _, _, hv => hv
  | k + 1, hk, v, hv => by
    obtain ⟨hk5, h2s, _, hpow⟩ := rec_step_bounds hk
    have hk6 : k ≤ 6 := Nat.le_of_succ_le hk
    obtain ⟨hv1, hv0⟩ := half_lt hk hv
    have hnext := xor_lt hv0 (mulByZRec_lt k hk6 _ hv1)
    have hdel := xor_lt (mulRec_lt k hk6 _ _ hv0 hnext) (sqRec_lt k hk6 _ hv1)
    have hd := invRec_lt k hk6 _ hdel
    rw [hpow]
    exact join_lt (2 ^ k) (toNat_ofNat_two_pow hk5) h2s
      (mulRec_lt k hk6 _ _ hd hv1) (mulRec_lt k hk6 _ _ hd hnext)

/-! ### Rung-twin bridges and per-width bounds -/

theorem mulByZ1_eq_rec (v : UInt64) : mulByZ1 v = mulByZRec 1 v := rfl
theorem mulByZ2_eq_rec (v : UInt64) : mulByZ2 v = mulByZRec 2 v := rfl
theorem mulByZ3_eq_rec (v : UInt64) : mulByZ3 v = mulByZRec 3 v := rfl
theorem mulByZ4_eq_rec (v : UInt64) : mulByZ4 v = mulByZRec 4 v := rfl
theorem mulByZ5_eq_rec (v : UInt64) : mulByZ5 v = mulByZRec 5 v := rfl

theorem mulByZ6_eq_rec (v : UInt64) : mulByZ6 v = mulByZRec 6 v := by
  conv_rhs => rw [mulByZRec_succ]
  simp only [← mulByZ5_eq_rec]
  rfl

private theorem xor_xor_cancel (x y z : UInt64) : x ^^^ (y ^^^ z) ^^^ z = x ^^^ y :=
  UInt64.toNat_inj.mp (by
    simp only [UInt64.toNat_xor]
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])

theorem mul2_eq_rec (a b : UInt64) : mul2 a b = mulRec 1 a b := by
  simp only [mul2, mulRec, mulByZRec]
  rw [xor_xor_cancel]
  rfl

theorem mul4_eq_rec (a b : UInt64) : mul4 a b = mulRec 2 a b := by
  conv_rhs => rw [mulRec_succ]
  simp only [← mul2_eq_rec, ← mulByZ1_eq_rec]
  rfl

theorem mul8_eq_rec (a b : UInt64) : mul8 a b = mulRec 3 a b := by
  conv_rhs => rw [mulRec_succ]
  simp only [← mul4_eq_rec, ← mulByZ2_eq_rec]
  rfl

theorem mul16_eq_rec (a b : UInt64) : mul16 a b = mulRec 4 a b := by
  conv_rhs => rw [mulRec_succ]
  simp only [← mul8_eq_rec, ← mulByZ3_eq_rec]
  rfl

theorem mul32_eq_rec (a b : UInt64) : mul32 a b = mulRec 5 a b := by
  conv_rhs => rw [mulRec_succ]
  simp only [← mul16_eq_rec, ← mulByZ4_eq_rec]
  rfl

theorem mul64_eq_rec (a b : UInt64) : mul64 a b = mulRec 6 a b := by
  conv_rhs => rw [mulRec_succ]
  simp only [← mul32_eq_rec, ← mulByZ5_eq_rec]
  rfl

theorem sq2_eq_rec (v : UInt64) : sq2 v = sqRec 1 v := rfl

theorem sq4_eq_rec (v : UInt64) : sq4 v = sqRec 2 v := by
  conv_rhs => rw [sqRec_succ]
  simp only [← sq2_eq_rec, ← mulByZ1_eq_rec]
  rfl

theorem sq8_eq_rec (v : UInt64) : sq8 v = sqRec 3 v := by
  conv_rhs => rw [sqRec_succ]
  simp only [← sq4_eq_rec, ← mulByZ2_eq_rec]
  rfl

theorem sq16_eq_rec (v : UInt64) : sq16 v = sqRec 4 v := by
  conv_rhs => rw [sqRec_succ]
  simp only [← sq8_eq_rec, ← mulByZ3_eq_rec]
  rfl

theorem sq32_eq_rec (v : UInt64) : sq32 v = sqRec 5 v := by
  conv_rhs => rw [sqRec_succ]
  simp only [← sq16_eq_rec, ← mulByZ4_eq_rec]
  rfl

theorem sq64_eq_rec (v : UInt64) : sq64 v = sqRec 6 v := by
  conv_rhs => rw [sqRec_succ]
  simp only [← sq32_eq_rec, ← mulByZ5_eq_rec]
  rfl

theorem inv2_eq_rec (v : UInt64) : inv2 v = invRec 1 v := rfl

theorem inv4_eq_rec (v : UInt64) : inv4 v = invRec 2 v := by
  conv_rhs => rw [invRec_succ]
  simp only [← mul2_eq_rec, ← sq2_eq_rec, ← mulByZ1_eq_rec, ← inv2_eq_rec]
  rfl

theorem inv8_eq_rec (v : UInt64) : inv8 v = invRec 3 v := by
  conv_rhs => rw [invRec_succ]
  simp only [← mul4_eq_rec, ← sq4_eq_rec, ← mulByZ2_eq_rec, ← inv4_eq_rec]
  rfl

theorem inv16_eq_rec (v : UInt64) : inv16 v = invRec 4 v := by
  conv_rhs => rw [invRec_succ]
  simp only [← mul8_eq_rec, ← sq8_eq_rec, ← mulByZ3_eq_rec, ← inv8_eq_rec]
  rfl

theorem inv32_eq_rec (v : UInt64) : inv32 v = invRec 5 v := by
  conv_rhs => rw [invRec_succ]
  simp only [← mul16_eq_rec, ← sq16_eq_rec, ← mulByZ4_eq_rec, ← inv16_eq_rec]
  rfl

theorem inv64_eq_rec (v : UInt64) : inv64 v = invRec 6 v := by
  conv_rhs => rw [invRec_succ]
  simp only [← mul32_eq_rec, ← sq32_eq_rec, ← mulByZ5_eq_rec, ← inv32_eq_rec]
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

theorem sq8_lt {v : UInt64} (hv : v.toNat < 2 ^ 8) : (sq8 v).toNat < 2 ^ 8 := by
  rw [sq8_eq_rec]; exact sqRec_lt 3 (by omega) v hv

theorem sq16_lt {v : UInt64} (hv : v.toNat < 2 ^ 16) : (sq16 v).toNat < 2 ^ 16 := by
  rw [sq16_eq_rec]; exact sqRec_lt 4 (by omega) v hv

theorem sq32_lt {v : UInt64} (hv : v.toNat < 2 ^ 32) : (sq32 v).toNat < 2 ^ 32 := by
  rw [sq32_eq_rec]; exact sqRec_lt 5 (by omega) v hv

theorem inv8_lt {v : UInt64} (hv : v.toNat < 2 ^ 8) : (inv8 v).toNat < 2 ^ 8 := by
  rw [inv8_eq_rec]; exact invRec_lt 3 (by omega) v hv

theorem inv16_lt {v : UInt64} (hv : v.toNat < 2 ^ 16) : (inv16 v).toNat < 2 ^ 16 := by
  rw [inv16_eq_rec]; exact invRec_lt 4 (by omega) v hv

theorem inv32_lt {v : UInt64} (hv : v.toNat < 2 ^ 32) : (inv32 v).toNat < 2 ^ 32 := by
  rw [inv32_eq_rec]; exact invRec_lt 5 (by omega) v hv

/-! ## Correctness against the spec

The twins agree with `concrete_mul` / `concrete_inv` on in-range words, by induction on
the level; statements go through `fromNat` so the spec side reasons inside
`ConcreteBTField`. -/

private theorem toNat_fromNat {k n : ℕ} (h : n < 2 ^ 2 ^ k) :
    BitVec.toNat (fromNat (k := k) n) = n := by
  show (BitVec.ofNat (2 ^ k) n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

private theorem fromNat_toNat {k : ℕ} (x : ConcreteBTField k) : fromNat x.toNat = x :=
  BitVec.eq_of_toNat_eq (toNat_fromNat x.isLt)

private theorem eq_zero_or_one {v : UInt64} (hv : v.toNat < 2 ^ 2 ^ 0) : v = 0 ∨ v = 1 := by
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1) with h | h
  · exact Or.inl (UInt64.toNat_inj.mp h)
  · exact Or.inr (UInt64.toNat_inj.mp h)

private theorem fromNat_zero {k : ℕ} :
    fromNat (k := k) (0 : UInt64).toNat = (0 : ConcreteBTField k) := rfl

private theorem fromNat_one {k : ℕ} :
    fromNat (k := k) (1 : UInt64).toNat = (1 : ConcreteBTField k) := rfl

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

private theorem concrete_mul_eq_mul {k : ℕ} (x y : ConcreteBTField k) :
    concrete_mul x y = x * y := rfl

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
    obtain ⟨hv1, hv0⟩ := half_lt hk hv
    have hz := mulByZRec_lt k (Nat.le_of_succ_le hk) _ hv1
    have hIH := mulByZRec_correct k (Nat.le_of_succ_le hk) (v >>> UInt64.ofNat (2 ^ k)) hv1
    have hZsplit : ((one : ConcreteBTField k), (zero : ConcreteBTField k))
        = split (Nat.succ_pos k) (Z (k + 1)) := (split_Z (Nat.succ_pos k)).symm
    have hme := concrete_mul_step (fromNat v.toNat) (Z (k + 1))
      (split_fromNat hk hv).symm hZsplit
    simp only [mulByZRec_succ]
    rw [fromNat_join hk (xor_lt hv0 hz) hv1, fromNat_xor, hIH]
    refine Eq.trans ?_ hme.symm
    simp only [concrete_mul_eq_mul, one_is_1, zero_is_0, mul_one, mul_zero, zero_mul,
      add_zero, zero_add]

/-- `mulRec` agrees with `concrete_mul` on in-range words. -/
theorem mulRec_correct : ∀ (k : ℕ), k ≤ 6 → ∀ (a b : UInt64),
    a.toNat < 2 ^ 2 ^ k → b.toNat < 2 ^ 2 ^ k →
    fromNat (k := k) (mulRec k a b).toNat = concrete_mul (fromNat a.toNat) (fromNat b.toNat)
  | 0, _, a, b, ha, hb => by
    rcases eq_zero_or_one ha with rfl | rfl <;> rcases eq_zero_or_one hb with rfl | rfl
    · show ConcreteBinaryTower.zero = concrete_mul zero zero
      rw [concrete_zero_mul0]
    · show ConcreteBinaryTower.zero = concrete_mul zero one
      rw [concrete_zero_mul0]
    · show ConcreteBinaryTower.zero = concrete_mul one zero
      rw [concrete_mul_zero0]
    · show ConcreteBinaryTower.one = concrete_mul one one
      rw [concrete_mul_one0]
  | k + 1, hk, a, b, ha, hb => by
    have hk6 : k ≤ 6 := Nat.le_of_succ_le hk
    obtain ⟨ha1, ha0⟩ := half_lt hk ha
    obtain ⟨hb1, hb0⟩ := half_lt hk hb
    have hp0 := mulRec_lt k hk6 _ _ ha0 hb0
    have hp2 := mulRec_lt k hk6 _ _ ha1 hb1
    have hp1 := mulRec_lt k hk6 _ _ (xor_lt ha0 ha1) (xor_lt hb0 hb1)
    have hz := mulByZRec_lt k hk6 _ hp2
    have hZ := mulByZRec_correct k hk6 _ hp2
    have h00 := mulRec_correct k hk6 _ _ ha0 hb0
    have h11 := mulRec_correct k hk6 _ _ ha1 hb1
    have hss := mulRec_correct k hk6 _ _ (xor_lt ha0 ha1) (xor_lt hb0 hb1)
    have hme := concrete_mul_step (fromNat a.toNat) (fromNat b.toNat)
      (split_fromNat hk ha).symm (split_fromNat hk hb).symm
    simp only [mulRec_succ]
    rw [fromNat_join hk (xor_lt (xor_lt hp1 (xor_lt hp0 hp2)) hz) (xor_lt hp0 hp2)]
    simp only [fromNat_xor]
    rw [hZ, h00, h11, hss]
    refine Eq.trans ?_ hme.symm
    simp only [concrete_mul_eq_mul, fromNat_xor]
    refine congrArg₂ (fun x y : ConcreteBTField k => (《 x, y 》 : ConcreteBTField (k + 1))) ?_ ?_
    · linear_combination (fromNat (k := k) (a &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat
          * fromNat (k := k) (b &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat
        + fromNat (k := k) (a >>> UInt64.ofNat (2 ^ k)).toNat
          * fromNat (k := k) (b >>> UInt64.ofNat (2 ^ k)).toNat)
        * CharTwo.two_eq_zero (R := ConcreteBTField k)
    · rfl

/-- `sqRec` computes the spec square on in-range words. -/
theorem sqRec_correct : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64), v.toNat < 2 ^ 2 ^ k →
    fromNat (k := k) (sqRec k v).toNat = concrete_mul (fromNat v.toNat) (fromNat v.toNat)
  | 0, hk, v, hv => by
    have h := mulRec_correct 0 hk v v hv hv
    rwa [show mulRec 0 v v = v from UInt64.and_self] at h
  | k + 1, hk, v, hv => by
    have hk6 : k ≤ 6 := Nat.le_of_succ_le hk
    obtain ⟨hv1, hv0⟩ := half_lt hk hv
    have hs0 := sqRec_lt k hk6 _ hv0
    have hs1 := sqRec_lt k hk6 _ hv1
    have hz := mulByZRec_lt k hk6 _ hs1
    have hZ := mulByZRec_correct k hk6 _ hs1
    have h0 := sqRec_correct k hk6 _ hv0
    have h1 := sqRec_correct k hk6 _ hv1
    have hme := concrete_mul_step (fromNat v.toNat) (fromNat v.toNat)
      (split_fromNat hk hv).symm (split_fromNat hk hv).symm
    simp only [sqRec_succ]
    rw [fromNat_join hk hz (xor_lt hs0 hs1), fromNat_xor, hZ, h0, h1]
    refine Eq.trans ?_ hme.symm
    simp only [concrete_mul_eq_mul]
    rw [← two_mul, CharTwo.two_eq_zero (R := ConcreteBTField k), zero_mul, zero_add]

private theorem split_zero' {k : ℕ} : split (Nat.succ_pos k) (0 : ConcreteBTField (k + 1))
    = ((0 : ConcreteBTField k), (0 : ConcreteBTField k)) := split_zero (Nat.succ_pos k)

private theorem split_one' {k : ℕ} : split (Nat.succ_pos k) (1 : ConcreteBTField (k + 1))
    = ((0 : ConcreteBTField k), (1 : ConcreteBTField k)) := split_one (Nat.succ_pos k)

/-- `concrete_inv`'s one-level descent, restated at the half level `k`; the `a = 0`
and `a = 1` branches satisfy the same formula. -/
private theorem concrete_inv_step {k : ℕ} (a : ConcreteBTField (k + 1))
    {a₁ a₀ : ConcreteBTField k} (ha : (a₁, a₀) = split (Nat.succ_pos k) a) :
    concrete_inv a
      = (《 (concrete_mul
              (concrete_inv (concrete_mul a₀ (a₀ + concrete_mul a₁ (Z k))
                + concrete_mul a₁ a₁)) a₁ : ConcreteBTField k),
            (concrete_mul
              (concrete_inv (concrete_mul a₀ (a₀ + concrete_mul a₁ (Z k))
                + concrete_mul a₁ a₁)) (a₀ + concrete_mul a₁ (Z k)) : ConcreteBTField k) 》 :
          ConcreteBTField (k + 1)) := by
  by_cases h0 : a = 0
  · subst h0
    rw [split_zero'] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [concrete_inv_zero]
    simp only [concrete_mul_eq_mul, zero_mul, mul_zero, add_zero]
    simp only [← zero_is_0]
    exact (join_zero_zero (Nat.succ_pos k)).symm
  by_cases h1 : a = 1
  · subst h1
    rw [split_one'] at ha
    obtain ⟨rfl, rfl⟩ := ha
    simp only [concrete_mul_eq_mul, zero_mul, mul_zero, mul_one, add_zero, concrete_inv_one]
    simp only [← zero_is_0, ← one_is_1]
    exact (join_zero_one (Nat.succ_pos k)).symm
  · rw [concrete_inv, dif_neg (Nat.succ_ne_zero k), dif_neg h0, dif_neg h1]
    simp_rw [← ha]
    rfl

/-- `invRec` agrees with `concrete_inv` on in-range words. -/
theorem invRec_correct : ∀ (k : ℕ), k ≤ 6 → ∀ (v : UInt64), v.toNat < 2 ^ 2 ^ k →
    fromNat (k := k) (invRec k v).toNat = concrete_inv (fromNat v.toNat)
  | 0, _, v, hv => by
    simp only [invRec]
    rcases eq_zero_or_one hv with rfl | rfl
    · rw [fromNat_zero, concrete_inv_zero]
    · rw [fromNat_one, concrete_inv_one]
  | k + 1, hk, v, hv => by
    have hk6 : k ≤ 6 := Nat.le_of_succ_le hk
    obtain ⟨hv1, hv0⟩ := half_lt hk hv
    have hnext := xor_lt hv0 (mulByZRec_lt k hk6 _ hv1)
    have hdel := xor_lt (mulRec_lt k hk6 _ _ hv0 hnext) (sqRec_lt k hk6 _ hv1)
    have hd := invRec_lt k hk6 _ hdel
    have hZ := mulByZRec_correct k hk6 _ hv1
    have hIH := invRec_correct k hk6 _ hdel
    have hm0 := mulRec_correct k hk6 _ _ hv0 hnext
    have hsq := sqRec_correct k hk6 _ hv1
    have hout1 := mulRec_correct k hk6 _ _ hd hv1
    have hout0 := mulRec_correct k hk6 _ _ hd hnext
    have hme := concrete_inv_step (fromNat v.toNat) (split_fromNat hk hv).symm
    simp only [invRec_succ]
    rw [fromNat_join hk (mulRec_lt k hk6 _ _ hd hv1) (mulRec_lt k hk6 _ _ hd hnext),
      hout1, hout0, hIH, fromNat_xor, hm0, hsq, fromNat_xor, hZ]
    exact hme.symm

/-! ## Carrier -/

/-- A level-`k` element in packed form: the low `2 ^ 2 ^ k` bits of a machine word,
sharing the `ConcreteBTField k` bit layout. Widths above 64 bits use `FastBT128`. -/
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
instance : NatCast (FastBT k) := ⟨fun n => if n % 2 = 0 then 0 else 1⟩
instance : IntCast (FastBT k) := ⟨fun n => if n % 2 = 0 then 0 else 1⟩

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

private theorem ofConcrete_val_toNat {k : ℕ} (hk : k ≤ 6) (x : ConcreteBTField k) :
    (UInt64.ofNat x.toNat).toNat = x.toNat := by
  show x.toNat % 2 ^ 64 = x.toNat
  refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt ?_)
  exact Nat.pow_le_pow_right (by omega)
    (Nat.le_trans (Nat.pow_le_pow_right (by omega) hk) (by norm_num))

/-- Repack a concrete element; one-word levels only (`k ≤ 6`). -/
def ofConcrete {k : ℕ} (x : ConcreteBTField k) (hk : k ≤ 6 := by omega) : FastBT k :=
  .mk (UInt64.ofNat x.toNat) <| by rw [ofConcrete_val_toNat hk]; exact x.isLt

@[simp] theorem toConcrete_ofConcrete {k : ℕ} (x : ConcreteBTField k) (hk : k ≤ 6) :
    toConcrete (ofConcrete x hk) = x := by
  show fromNat (UInt64.ofNat x.toNat).toNat = x
  rw [ofConcrete_val_toNat hk]
  exact fromNat_toNat x

@[simp] theorem ofConcrete_toConcrete {k : ℕ} (a : FastBT k) (hk : k ≤ 6) :
    ofConcrete (toConcrete a) hk = a :=
  toConcrete_injective (toConcrete_ofConcrete (toConcrete a) hk)

@[simp] theorem toConcrete_zero : toConcrete (0 : FastBT k) = 0 := fromNat_zero

@[simp] theorem toConcrete_one : toConcrete (1 : FastBT k) = 1 := fromNat_one

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

theorem toConcrete_natCast (n : ℕ) :
    toConcrete (n : FastBT k) = (n : ConcreteBTField k) := by
  rw [CharP.cast_eq_mod (ConcreteBTField k) 2 n]
  show toConcrete (if n % 2 = 0 then 0 else 1) = _
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h2 | h2
  · rw [if_pos h2, toConcrete_zero, h2, Nat.cast_zero]
  · rw [if_neg (by omega), toConcrete_one, h2, Nat.cast_one]

theorem toConcrete_intCast (n : ℤ) :
    toConcrete (n : FastBT k) = (n : ConcreteBTField k) := by
  rw [CharP.intCast_eq_intCast_mod (R := ConcreteBTField k) 2 (a := n), Nat.cast_ofNat]
  show toConcrete (if n % 2 = 0 then 0 else 1) = _
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h2 | h2
  · rw [if_pos h2, toConcrete_zero, h2, Int.cast_zero]
  · rw [if_neg (by omega), toConcrete_one, h2, Int.cast_one]

instance : AddCommGroup (FastBT k) :=
  toConcrete_injective.addCommGroup toConcrete toConcrete_zero toConcrete_add
    toConcrete_neg toConcrete_sub (fun x n => toConcrete_nsmul n x)
    (fun x n => toConcrete_zsmul n x)

/-! ## Field operations

`Mul`/`Inv` instances per usable width with their `toConcrete` transport lemmas;
`fieldOfHoms` assembles the `Field` instances from the injective bridge. -/

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

instance : Inv BT8 := ⟨fun a => .mk (inv8 a.val) (inv8_lt a.isLt)⟩
instance : Inv BT16 := ⟨fun a => .mk (inv16 a.val) (inv16_lt a.isLt)⟩
instance : Inv BT32 := ⟨fun a => .mk (inv32 a.val) (inv32_lt a.isLt)⟩
instance : Inv BT64 := ⟨fun a => .mk (inv64 a.val) (UInt64.toNat_lt _)⟩

@[simp] theorem val_inv_bt8 (a : BT8) : (a⁻¹).val = inv8 a.val := rfl
@[simp] theorem val_inv_bt16 (a : BT16) : (a⁻¹).val = inv16 a.val := rfl
@[simp] theorem val_inv_bt32 (a : BT32) : (a⁻¹).val = inv32 a.val := rfl
@[simp] theorem val_inv_bt64 (a : BT64) : (a⁻¹).val = inv64 a.val := rfl

@[simp] theorem toConcrete_inv_bt8 (a : BT8) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv8 a.val).toNat = _
  rw [inv8_eq_rec]
  exact invRec_correct 3 (by omega) a.val a.isLt

@[simp] theorem toConcrete_inv_bt16 (a : BT16) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv16 a.val).toNat = _
  rw [inv16_eq_rec]
  exact invRec_correct 4 (by omega) a.val a.isLt

@[simp] theorem toConcrete_inv_bt32 (a : BT32) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv32 a.val).toNat = _
  rw [inv32_eq_rec]
  exact invRec_correct 5 (by omega) a.val a.isLt

@[simp] theorem toConcrete_inv_bt64 (a : BT64) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv64 a.val).toNat = _
  rw [inv64_eq_rec]
  exact invRec_correct 6 (by omega) a.val a.isLt

private theorem toConcrete_npowRec {k : ℕ} [Mul (FastBT k)]
    (hmul : ∀ a b : FastBT k, toConcrete (a * b) = toConcrete a * toConcrete b)
    (a : FastBT k) : ∀ (n : ℕ), toConcrete (npowRec n a) = toConcrete a ^ n
  | 0 => by rw [npowRec, pow_zero, toConcrete_one]
  | n + 1 => by rw [npowRec, pow_succ, hmul, toConcrete_npowRec hmul a n]

/-- Assemble a width's `Field` instance from its `toConcrete` multiplication and
inversion lemmas. -/
@[reducible] private def fieldOfHoms {k : ℕ} [Mul (FastBT k)] [Inv (FastBT k)]
    (hmul : ∀ a b : FastBT k, toConcrete (a * b) = toConcrete a * toConcrete b)
    (hinv : ∀ a : FastBT k, toConcrete a⁻¹ = (toConcrete a)⁻¹) : Field (FastBT k) :=
  letI : Pow (FastBT k) ℕ := ⟨fun a n => npowRec n a⟩
  letI cr : CommRing (FastBT k) := toConcrete_injective.commRing toConcrete
    toConcrete_zero toConcrete_one toConcrete_add hmul toConcrete_neg toConcrete_sub
    toConcrete_nsmul toConcrete_zsmul (fun a n => toConcrete_npowRec hmul a n)
    toConcrete_natCast toConcrete_intCast
  { cr with
    inv := Inv.inv
    exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := ConcreteBTField k)
      (by rw [← toConcrete_zero, ← toConcrete_one (k := k), h])⟩
    mul_inv_cancel := fun a ha => toConcrete_injective (by
      rw [hmul, hinv, toConcrete_one]
      exact mul_inv_cancel₀ fun h0 => ha (toConcrete_injective
        (by rw [h0, toConcrete_zero])))
    inv_zero := toConcrete_injective (by rw [hinv, toConcrete_zero, inv_zero])
    qsmul := _
    nnqsmul := _ }

instance : Field BT8 := fieldOfHoms toConcrete_mul_bt8 toConcrete_inv_bt8
instance : Field BT16 := fieldOfHoms toConcrete_mul_bt16 toConcrete_inv_bt16
instance : Field BT32 := fieldOfHoms toConcrete_mul_bt32 toConcrete_inv_bt32
instance : Field BT64 := fieldOfHoms toConcrete_mul_bt64 toConcrete_inv_bt64

@[reducible] private def ringEquivOfHom {k : ℕ} [Mul (FastBT k)] (hk : k ≤ 6)
    (hmul : ∀ a b : FastBT k, toConcrete (a * b) = toConcrete a * toConcrete b) :
    FastBT k ≃+* ConcreteBTField k where
  toFun := toConcrete
  invFun x := ofConcrete x hk
  left_inv a := ofConcrete_toConcrete a hk
  right_inv x := toConcrete_ofConcrete x hk
  map_mul' := hmul
  map_add' := toConcrete_add

/-- Ring isomorphism between `BT8` and the concrete level-3 tower field. -/
def ringEquivBT8 : BT8 ≃+* ConcreteBTField 3 := ringEquivOfHom (by omega) toConcrete_mul_bt8
/-- Ring isomorphism between `BT16` and the concrete level-4 tower field. -/
def ringEquivBT16 : BT16 ≃+* ConcreteBTField 4 := ringEquivOfHom (by omega) toConcrete_mul_bt16
/-- Ring isomorphism between `BT32` and the concrete level-5 tower field. -/
def ringEquivBT32 : BT32 ≃+* ConcreteBTField 5 := ringEquivOfHom (by omega) toConcrete_mul_bt32
/-- Ring isomorphism between `BT64` and the concrete level-6 tower field. -/
def ringEquivBT64 : BT64 ≃+* ConcreteBTField 6 := ringEquivOfHom (by omega) toConcrete_mul_bt64

/-- Multiply by the level generator `Z k`; one-word levels only (`k ≤ 6`). -/
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

theorem FastBT.mulByZ_val : ∀ {k : ℕ} (a : FastBT k) (hk : k ≤ 6),
    (a.mulByZ hk).val = mulByZRec k a.val
  | 0, _, _ => rfl
  | 1, a, _ => mulByZ1_eq_rec a.val
  | 2, a, _ => mulByZ2_eq_rec a.val
  | 3, a, _ => mulByZ3_eq_rec a.val
  | 4, a, _ => mulByZ4_eq_rec a.val
  | 5, a, _ => mulByZ5_eq_rec a.val
  | 6, a, _ => mulByZ6_eq_rec a.val
  | _ + 7, _, hk => absurd hk (by omega)

theorem toConcrete_mulByZ {k : ℕ} (a : FastBT k) (hk : k ≤ 6) :
    toConcrete (a.mulByZ hk) = toConcrete a * Z k := by
  show fromNat (a.mulByZ hk).val.toNat = _
  rw [a.mulByZ_val hk]
  exact mulByZRec_correct k hk a.val a.isLt

/-- Square via the dedicated ladder, cheaper than `a * a`; one-word levels only. -/
@[inline] def FastBT.square {k : ℕ} (a : FastBT k) (_hk : k ≤ 6 := by omega) : FastBT k :=
  match k, a with
  | 0, a => a
  | 1, a => .mk (sq2 a.val) (by rw [sq2_eq_rec]; exact sqRec_lt 1 (by omega) _ a.isLt)
  | 2, a => .mk (sq4 a.val) (by rw [sq4_eq_rec]; exact sqRec_lt 2 (by omega) _ a.isLt)
  | 3, a => .mk (sq8 a.val) (sq8_lt a.isLt)
  | 4, a => .mk (sq16 a.val) (sq16_lt a.isLt)
  | 5, a => .mk (sq32 a.val) (sq32_lt a.isLt)
  | 6, a => .mk (sq64 a.val) (UInt64.toNat_lt _)
  | _ + 7, a => a

theorem FastBT.square_val : ∀ {k : ℕ} (a : FastBT k) (hk : k ≤ 6),
    (a.square hk).val = sqRec k a.val
  | 0, _, _ => rfl
  | 1, a, _ => sq2_eq_rec a.val
  | 2, a, _ => sq4_eq_rec a.val
  | 3, a, _ => sq8_eq_rec a.val
  | 4, a, _ => sq16_eq_rec a.val
  | 5, a, _ => sq32_eq_rec a.val
  | 6, a, _ => sq64_eq_rec a.val
  | _ + 7, _, hk => absurd hk (by omega)

theorem toConcrete_square {k : ℕ} (a : FastBT k) (hk : k ≤ 6) :
    toConcrete (a.square hk) = toConcrete a * toConcrete a := by
  show fromNat (a.square hk).val.toNat = _
  rw [a.square_val hk]
  exact sqRec_correct k hk a.val a.isLt

/-! ## Level 7: GF(2^128)

The tower split falls on the limb boundary, so the halves are the limbs. -/

/-- A level-7 tower field element as two limbs, `lo` the low half. -/
structure FastBT128 where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, Inhabited

private theorem join_add_join {k : ℕ} (a b c d : ConcreteBTField k) :
    (《 a, b 》 : ConcreteBTField (k + 1)) + (《 c, d 》 : ConcreteBTField (k + 1))
      = (《 a + c, b + d 》 : ConcreteBTField (k + 1)) :=
  join_of_split (Nat.succ_pos k) _ _ _
    (split_sum_eq_sum_split (Nat.succ_pos k) _ _ a b c d
      (split_join_eq_split (Nat.succ_pos k) a b) (split_join_eq_split (Nat.succ_pos k) c d))

/-! Width-64 spec forms of the word operations; every `UInt64` is in range at level 6. -/

private theorem fromNat_mul64 (a b : UInt64) :
    fromNat (k := 6) (mul64 a b).toNat = concrete_mul (fromNat a.toNat) (fromNat b.toNat) := by
  rw [mul64_eq_rec]
  exact mulRec_correct 6 le_rfl a b (UInt64.toNat_lt a) (UInt64.toNat_lt b)

private theorem fromNat_sq64 (v : UInt64) :
    fromNat (k := 6) (sq64 v).toNat = concrete_mul (fromNat v.toNat) (fromNat v.toNat) := by
  rw [sq64_eq_rec]
  exact sqRec_correct 6 le_rfl v (UInt64.toNat_lt v)

private theorem fromNat_mulByZ6 (v : UInt64) :
    fromNat (k := 6) (mulByZ6 v).toNat = concrete_mul (fromNat v.toNat) (Z 6) := by
  rw [mulByZ6_eq_rec]
  exact mulByZRec_correct 6 le_rfl v (UInt64.toNat_lt v)

private theorem fromNat_inv64 (v : UInt64) :
    fromNat (k := 6) (inv64 v).toNat = concrete_inv (fromNat v.toNat) := by
  rw [inv64_eq_rec]
  exact invRec_correct 6 le_rfl v (UInt64.toNat_lt v)

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

/-! ### Conversions and algebra

At level 7 the tower halves are the limbs, so `toConcrete` maps into the join directly
and each correctness proof is one application of the level-6 results. -/

instance : SMul ℕ FastBT128 := ⟨fun n x => if n % 2 = 0 then 0 else x⟩
instance : SMul ℤ FastBT128 := ⟨fun n x => if n % 2 = 0 then 0 else x⟩
instance : NatCast FastBT128 := ⟨fun n => if n % 2 = 0 then 0 else 1⟩
instance : IntCast FastBT128 := ⟨fun n => if n % 2 = 0 then 0 else 1⟩
instance : Inv FastBT128 := ⟨inv⟩

@[simp] theorem neg_def (a : FastBT128) : -a = a := rfl
@[simp] theorem sub_def (a b : FastBT128) : a - b = a + b := rfl

/-- The bridge into the `BitVec` model, with the limbs as the tower halves. -/
def toConcrete (v : FastBT128) : ConcreteBTField 7 :=
  (《 fromNat (k := 6) v.hi.toNat, fromNat (k := 6) v.lo.toNat 》 : ConcreteBTField 7)

theorem toConcrete_injective : Function.Injective toConcrete := by
  intro a b h
  obtain ⟨h1, h0⟩ := (join_eq_join_iff (Nat.succ_pos 6) _ _ _ _).mp h
  have hhi : a.hi = b.hi := UInt64.toNat_inj.mp (by
    have h' := congrArg BitVec.toNat h1
    rwa [toNat_fromNat (UInt64.toNat_lt _), toNat_fromNat (UInt64.toNat_lt _)] at h')
  have hlo : a.lo = b.lo := UInt64.toNat_inj.mp (by
    have h' := congrArg BitVec.toNat h0
    rwa [toNat_fromNat (UInt64.toNat_lt _), toNat_fromNat (UInt64.toNat_lt _)] at h')
  cases a; cases b
  simp only [FastBT128.mk.injEq]
  exact ⟨hlo, hhi⟩

@[simp] theorem toConcrete_zero : toConcrete (0 : FastBT128) = 0 := by
  show (《 fromNat (k := 6) (0 : UInt64).toNat, fromNat (k := 6) (0 : UInt64).toNat 》 :
    ConcreteBTField 7) = 0
  rw [fromNat_zero]
  simp only [← zero_is_0]
  exact join_zero_zero (Nat.succ_pos 6)

@[simp] theorem toConcrete_one : toConcrete (1 : FastBT128) = 1 := by
  show (《 fromNat (k := 6) (0 : UInt64).toNat, fromNat (k := 6) (1 : UInt64).toNat 》 :
    ConcreteBTField 7) = 1
  rw [fromNat_zero, fromNat_one]
  simp only [← zero_is_0, ← one_is_1]
  exact join_zero_one (Nat.succ_pos 6)

@[simp] theorem toConcrete_add (a b : FastBT128) :
    toConcrete (a + b) = toConcrete a + toConcrete b := by
  show (《 fromNat (k := 6) (a.hi ^^^ b.hi).toNat, fromNat (k := 6) (a.lo ^^^ b.lo).toNat 》 :
    ConcreteBTField 7) = _
  rw [fromNat_xor, fromNat_xor, ← join_add_join]
  rfl

@[simp] theorem toConcrete_neg (a : FastBT128) : toConcrete (-a) = -(toConcrete a) := rfl

@[simp] theorem toConcrete_sub (a b : FastBT128) :
    toConcrete (a - b) = toConcrete a - toConcrete b := by
  rw [sub_def, toConcrete_add, sub_eq_add_neg, ← toConcrete_neg, neg_def]

private theorem toConcrete_if_zero {p : Prop} [Decidable p] (x : FastBT128) :
    toConcrete (if p then 0 else x) = if p then ConcreteBinaryTower.zero else toConcrete x := by
  by_cases h : p
  · rw [if_pos h, if_pos h, toConcrete_zero]
    exact zero_is_0.symm
  · rw [if_neg h, if_neg h]

theorem toConcrete_nsmul (n : ℕ) (x : FastBT128) :
    toConcrete (n • x) = n • toConcrete x := toConcrete_if_zero x

theorem toConcrete_zsmul (n : ℤ) (x : FastBT128) :
    toConcrete (n • x) = n • toConcrete x := toConcrete_if_zero x

instance : AddCommGroup FastBT128 :=
  toConcrete_injective.addCommGroup toConcrete toConcrete_zero toConcrete_add
    toConcrete_neg toConcrete_sub (fun x n => toConcrete_nsmul n x)
    (fun x n => toConcrete_zsmul n x)

theorem toConcrete_natCast (n : ℕ) :
    toConcrete (n : FastBT128) = (n : ConcreteBTField 7) := by
  rw [CharP.cast_eq_mod (ConcreteBTField 7) 2 n]
  show toConcrete (if n % 2 = 0 then 0 else 1) = _
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h2 | h2
  · rw [if_pos h2, toConcrete_zero, h2, Nat.cast_zero]
  · rw [if_neg (by omega), toConcrete_one, h2, Nat.cast_one]

theorem toConcrete_intCast (n : ℤ) :
    toConcrete (n : FastBT128) = (n : ConcreteBTField 7) := by
  rw [CharP.intCast_eq_intCast_mod (R := ConcreteBTField 7) 2 (a := n), Nat.cast_ofNat]
  show toConcrete (if n % 2 = 0 then 0 else 1) = _
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h2 | h2
  · rw [if_pos h2, toConcrete_zero, h2, Int.cast_zero]
  · rw [if_neg (by omega), toConcrete_one, h2, Int.cast_one]

@[simp] theorem toConcrete_mul (a b : FastBT128) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  have hme := concrete_mul_step (toConcrete a) (toConcrete b)
    (split_of_join (Nat.succ_pos 6) (toConcrete a) (fromNat (k := 6) a.hi.toNat)
      (fromNat (k := 6) a.lo.toNat) rfl)
    (split_of_join (Nat.succ_pos 6) (toConcrete b) (fromNat (k := 6) b.hi.toNat)
      (fromNat (k := 6) b.lo.toNat) rfl)
  show (《 fromNat (k := 6) (mul64 (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
            ^^^ (mul64 a.lo b.lo ^^^ mul64 a.hi b.hi)
            ^^^ mulByZ6 (mul64 a.hi b.hi)).toNat,
          fromNat (k := 6) (mul64 a.lo b.lo ^^^ mul64 a.hi b.hi).toNat 》 :
      ConcreteBTField 7) = _
  simp only [fromNat_xor, fromNat_mul64, fromNat_mulByZ6]
  refine Eq.trans ?_ hme.symm
  simp only [concrete_mul_eq_mul]
  refine congrArg₂ (fun x y : ConcreteBTField 6 => (《 x, y 》 : ConcreteBTField 7)) ?_ ?_
  · linear_combination (fromNat (k := 6) a.lo.toNat * fromNat (k := 6) b.lo.toNat
        + fromNat (k := 6) a.hi.toNat * fromNat (k := 6) b.hi.toNat)
      * CharTwo.two_eq_zero (R := ConcreteBTField 6)
  · rfl

theorem toConcrete_mulByZ (v : FastBT128) :
    toConcrete v.mulByZ = toConcrete v * Z 7 := by
  have hZsplit : ((ConcreteBinaryTower.one : ConcreteBTField 6),
        (ConcreteBinaryTower.zero : ConcreteBTField 6))
      = split (Nat.succ_pos 6) (Z 7) := (split_Z (Nat.succ_pos 6)).symm
  have hme := concrete_mul_step (toConcrete v) (Z 7)
    (split_of_join (Nat.succ_pos 6) (toConcrete v) (fromNat (k := 6) v.hi.toNat)
      (fromNat (k := 6) v.lo.toNat) rfl) hZsplit
  show (《 fromNat (k := 6) (v.lo ^^^ mulByZ6 v.hi).toNat, fromNat (k := 6) v.hi.toNat 》 :
      ConcreteBTField 7) = _
  simp only [fromNat_xor, fromNat_mulByZ6]
  refine Eq.trans ?_ hme.symm
  simp only [concrete_mul_eq_mul, one_is_1, zero_is_0, mul_one, mul_zero, zero_mul,
    add_zero, zero_add]

theorem toConcrete_square (v : FastBT128) :
    toConcrete v.square = toConcrete v * toConcrete v := by
  have hme := concrete_mul_step (toConcrete v) (toConcrete v)
    (split_of_join (Nat.succ_pos 6) (toConcrete v) (fromNat (k := 6) v.hi.toNat)
      (fromNat (k := 6) v.lo.toNat) rfl)
    (split_of_join (Nat.succ_pos 6) (toConcrete v) (fromNat (k := 6) v.hi.toNat)
      (fromNat (k := 6) v.lo.toNat) rfl)
  show (《 fromNat (k := 6) (mulByZ6 (sq64 v.hi)).toNat,
          fromNat (k := 6) (sq64 v.lo ^^^ sq64 v.hi).toNat 》 : ConcreteBTField 7) = _
  simp only [fromNat_xor, fromNat_sq64, fromNat_mulByZ6]
  refine Eq.trans ?_ hme.symm
  simp only [concrete_mul_eq_mul]
  rw [← two_mul, CharTwo.two_eq_zero (R := ConcreteBTField 6), zero_mul, zero_add]

@[simp] theorem toConcrete_inv (v : FastBT128) : toConcrete v⁻¹ = (toConcrete v)⁻¹ := by
  have hme := concrete_inv_step (toConcrete v)
    (split_of_join (Nat.succ_pos 6) (toConcrete v) (fromNat (k := 6) v.hi.toNat)
      (fromNat (k := 6) v.lo.toNat) rfl)
  show (《 fromNat (k := 6)
            (mul64 (inv64 (mul64 v.lo (v.lo ^^^ mulByZ6 v.hi) ^^^ sq64 v.hi)) v.hi).toNat,
          fromNat (k := 6)
            (mul64 (inv64 (mul64 v.lo (v.lo ^^^ mulByZ6 v.hi) ^^^ sq64 v.hi))
              (v.lo ^^^ mulByZ6 v.hi)).toNat 》 : ConcreteBTField 7) = _
  simp only [fromNat_xor, fromNat_mul64, fromNat_sq64, fromNat_mulByZ6, fromNat_inv64]
  exact hme.symm

private theorem toConcrete_npowRec (a : FastBT128) :
    ∀ (n : ℕ), toConcrete (npowRec n a) = toConcrete a ^ n
  | 0 => by rw [npowRec, pow_zero, toConcrete_one]
  | n + 1 => by rw [npowRec, pow_succ, toConcrete_mul, toConcrete_npowRec a n]

instance : Field FastBT128 :=
  letI : Pow FastBT128 ℕ := ⟨fun a n => npowRec n a⟩
  letI cr : CommRing FastBT128 := toConcrete_injective.commRing toConcrete
    toConcrete_zero toConcrete_one toConcrete_add toConcrete_mul toConcrete_neg
    toConcrete_sub toConcrete_nsmul toConcrete_zsmul
    (fun a n => toConcrete_npowRec a n) toConcrete_natCast toConcrete_intCast
  { cr with
    inv := Inv.inv
    exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := ConcreteBTField 7)
      (by rw [← toConcrete_zero, ← toConcrete_one, h])⟩
    mul_inv_cancel := fun a ha => toConcrete_injective (by
      rw [toConcrete_mul, toConcrete_inv, toConcrete_one]
      exact mul_inv_cancel₀ fun h0 => ha (toConcrete_injective
        (by rw [h0, toConcrete_zero])))
    inv_zero := toConcrete_injective (by rw [toConcrete_inv, toConcrete_zero, inv_zero])
    qsmul := _
    nnqsmul := _ }

/-- Repack a concrete level-7 element into limbs. -/
def ofConcrete (x : ConcreteBTField 7) : FastBT128 := ofNat x.toNat

@[simp] theorem toConcrete_ofConcrete (x : ConcreteBTField 7) :
    toConcrete (ofConcrete x) = x := by
  refine ((join_eq_bitvec_iff_fromNat (Nat.succ_pos 6) x _ _).mpr ⟨?_, ?_⟩).symm
  · simp only [Nat.succ_sub_one]
    congr 1
    show (x.toNat >>> 64) % 2 ^ 64 = x.toNat >>> 2 ^ 6
    refine Nat.mod_eq_of_lt ?_
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact x.isLt)
  · simp only [Nat.succ_sub_one]
    congr 1
    show x.toNat % 2 ^ 64 = x.toNat &&& 2 ^ 2 ^ 6 - 1
    rw [Nat.and_two_pow_sub_one_eq_mod]
    rfl

@[simp] theorem ofConcrete_toConcrete (a : FastBT128) : ofConcrete (toConcrete a) = a :=
  toConcrete_injective (toConcrete_ofConcrete (toConcrete a))

/-- Ring isomorphism between `FastBT128` and the concrete level-7 tower field. -/
def ringEquiv : FastBT128 ≃+* ConcreteBTField 7 where
  toFun := toConcrete
  invFun := ofConcrete
  left_inv := ofConcrete_toConcrete
  right_inv := toConcrete_ofConcrete
  map_mul' := toConcrete_mul
  map_add' := toConcrete_add

end FastBT128

end ConcreteBinaryTower.Fast
