/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Field
public import CompPoly.Fields.Binary.Tower.FastDefs
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Tactic.LinearCombination

/-!
# Fast Binary Tower Arithmetic

Packed machine-word implementation of `ConcreteBTField` arithmetic, same bit layout:
one `UInt64` for levels `k ≤ 6`, two limbs at level 7. The runtime definitions live in
the zero-import `FastDefs`; this module proves them correct against the concrete tower
by induction over recursive twins, giving `Field` instances and ring isomorphisms at
every width.
-/

@[expose] public section

namespace ConcreteBinaryTower.Fast

/-! ## Range bounds

Every operation maps values below `2 ^ s` to values below `2 ^ s`; the shift/mask
helpers cross into `ℕ` once and the per-width lemmas chain them. -/

theorem and_mask_lt (s : ℕ) {a m : UInt64} (hm : m.toNat = 2 ^ s - 1) :
    (a &&& m).toNat < 2 ^ s := by
  rw [UInt64.toNat_and]
  exact Nat.and_lt_two_pow _ (by rw [hm]; exact Nat.sub_lt (Nat.two_pow_pos s) Nat.one_pos)

theorem xor_lt {x y : UInt64} {s : ℕ} (hx : x.toNat < 2 ^ s) (hy : y.toNat < 2 ^ s) :
    (x ^^^ y).toNat < 2 ^ s := by
  rw [UInt64.toNat_xor]
  exact Nat.xor_lt_two_pow hx hy

theorem shiftRight_lt (s : ℕ) {a sh : UInt64} {t : ℕ} (hsh : sh.toNat = s)
    (hs : s < 64) (ha : a.toNat < 2 ^ (s + t)) : (a >>> sh).toNat < 2 ^ t := by
  rw [UInt64.toNat_shiftRight, hsh, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact ha)

theorem join_lt (s : ℕ) {hi lo sh : UInt64} (hsh : sh.toNat = s) (hs : 2 * s ≤ 64)
    (hhi : hi.toNat < 2 ^ s) (hlo : lo.toNat < 2 ^ s) :
    ((hi <<< sh) ||| lo).toNat < 2 ^ (2 * s) := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, hsh, Nat.mod_eq_of_lt (by omega : s < 64)]
  refine Nat.or_lt_two_pow ?_ (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by omega) (by omega)))
  have hval : hi.toNat <<< s < 2 ^ (2 * s) := by
    rw [Nat.shiftLeft_eq, Nat.two_mul, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos s)).mpr hhi
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hval

/-- Both half bounds for a literal shift/mask split. -/
theorem half_lit_lt (s : ℕ) (m sh : UInt64) {v : UInt64} (hm : m.toNat = 2 ^ s - 1)
    (hsh : sh.toNat = s) (hs : s < 64) (hv : v.toNat < 2 ^ (s + s)) :
    (v >>> sh).toNat < 2 ^ s ∧ (v &&& m).toNat < 2 ^ s :=
  ⟨shiftRight_lt s hsh hs hv, and_mask_lt s hm⟩

/-- Half bounds of a 16-bit word. -/
theorem half16_lt {v : UInt64} (hv : v.toNat < 2 ^ 16) :
    (v >>> 8).toNat < 2 ^ 8 ∧ (v &&& 0xFF).toNat < 2 ^ 8 :=
  half_lit_lt 8 0xFF 8 (by decide) (by decide) (by omega) hv

/-- Half bounds of a 32-bit word. -/
theorem half32_lt {v : UInt64} (hv : v.toNat < 2 ^ 32) :
    (v >>> 16).toNat < 2 ^ 16 ∧ (v &&& 0xFFFF).toNat < 2 ^ 16 :=
  half_lit_lt 16 0xFFFF 16 (by decide) (by decide) (by omega) hv

/-- Half bounds of a full word. -/
theorem half64_lt (v : UInt64) :
    (v >>> 32).toNat < 2 ^ 32 ∧ (v &&& 0xFFFFFFFF).toNat < 2 ^ 32 :=
  half_lit_lt 32 0xFFFFFFFF 32 (by decide) (by decide) (by omega) (UInt64.toNat_lt v)

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

theorem mulByZRec_succ (k : ℕ) (v : UInt64) :
    mulByZRec (k + 1) v =
      let sh := UInt64.ofNat (2 ^ k)
      let m := ((1 : UInt64) <<< sh) - 1
      let v0 := v &&& m
      let v1 := v >>> sh
      ((v0 ^^^ mulByZRec k v1) <<< sh) ||| v1 := rfl

theorem mulRec_succ (k : ℕ) (a b : UInt64) :
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

theorem sqRec_succ (k : ℕ) (v : UInt64) :
    sqRec (k + 1) v =
      let sh := UInt64.ofNat (2 ^ k)
      let m := ((1 : UInt64) <<< sh) - 1
      let s0 := sqRec k (v &&& m)
      let s1 := sqRec k (v >>> sh)
      ((mulByZRec k s1) <<< sh) ||| (s0 ^^^ s1) := rfl

theorem invRec_succ (k : ℕ) (v : UInt64) :
    invRec (k + 1) v =
      let sh := UInt64.ofNat (2 ^ k)
      let m := ((1 : UInt64) <<< sh) - 1
      let v0 := v &&& m
      let v1 := v >>> sh
      let next := v0 ^^^ mulByZRec k v1
      let delta := mulRec k v0 next ^^^ sqRec k v1
      let d := invRec k delta
      ((mulRec k d v1) <<< sh) ||| (mulRec k d next) := rfl

theorem toNat_ofNat_two_pow {k : ℕ} (hk : k ≤ 5) :
    (UInt64.ofNat (2 ^ k)).toNat = 2 ^ k :=
  UInt64.toNat_ofNat_of_lt'
    (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by norm_num [UInt64.size]))

theorem toNat_mask_two_pow {k : ℕ} (hk : k ≤ 5) :
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
theorem rec_step_bounds {k : ℕ} (hk : k + 1 ≤ 6) :
    k ≤ 5 ∧ 2 * 2 ^ k ≤ 64 ∧ 2 ^ k + 2 ^ k = 2 ^ (k + 1) ∧
      (2 : ℕ) ^ 2 ^ (k + 1) = 2 ^ (2 * 2 ^ k) := by
  have hk5 : k ≤ 5 := by omega
  have h32 : 2 ^ k ≤ 32 := Nat.pow_le_pow_right (by omega) hk5
  exact ⟨hk5, by omega, by rw [Nat.pow_succ]; omega, by rw [Nat.pow_succ, Nat.mul_comm]⟩

/-- Both halves of an in-range word are in range at the half level. -/
theorem half_lt {k : ℕ} (hk : k + 1 ≤ 6) {v : UInt64}
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

theorem xor_xor_cancel (x y z : UInt64) : x ^^^ (y ^^^ z) ^^^ z = x ^^^ y :=
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

/-! ### Table bridges

`getElem_ofFn` turns a table lookup back into the generating ladder call, so each `*T`
rung equals its ladder twin on in-range words and no table is kernel-evaluated. -/

/-- Lookup in a 256-entry `Array.ofFn` table is the generating function. -/
theorem byteTable_get_eq {f : UInt64 → UInt64}
    (hf : ∀ v : UInt64, v.toNat < 2 ^ 8 → (f v).toNat < 2 ^ 8)
    {v : UInt64} (hv : v.toNat < 2 ^ 8) :
    ((⟨Array.ofFn (n := 256) fun i => (f (UInt64.ofNat i)).toUInt8⟩ : ByteArray).get!
      v.toNat).toUInt64 = f v := by
  have hfv : (f v).toNat < 256 := by have := hf v hv; omega
  simp only [ByteArray.get!]
  rw [getElem!_pos _ _ (by simp only [Array.size_ofFn]; omega)]
  simp only [Array.getElem_ofFn]
  rw [UInt64.ofNat_toNat]
  apply UInt64.toNat_inj.mp
  simp only [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, Nat.mod_eq_of_lt hfv]

theorem mul8T_eq_mul8 {a b : UInt64} (ha : a.toNat < 2 ^ 8) (hb : b.toNat < 2 ^ 8) :
    mul8T a b = mul8 a b := by
  have hidx : ((a <<< 8) + b).toNat = a.toNat * 256 + b.toNat := by
    have h8 : ((8 : UInt64).toNat % 64) = 8 := by decide
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, h8, Nat.shiftLeft_eq]
    omega
  have hbound : (mul8 a b).toNat < 256 := by have := mul8_lt ha hb; omega
  rw [mul8T, hidx]
  simp only [mul8Table, ByteArray.get!]
  rw [getElem!_pos _ _ (by simp only [Array.size_ofFn]; omega)]
  simp only [Array.getElem_ofFn]
  have hdiv : (a.toNat * 256 + b.toNat) / 256 = a.toNat := by omega
  have hmod : (a.toNat * 256 + b.toNat) % 256 = b.toNat := by omega
  rw [hdiv, hmod, UInt64.ofNat_toNat, UInt64.ofNat_toNat]
  apply UInt64.toNat_inj.mp
  simp only [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, Nat.mod_eq_of_lt hbound]

theorem mulByZ3T_eq_mulByZ3 {v : UInt64} (hv : v.toNat < 2 ^ 8) :
    mulByZ3T v = mulByZ3 v :=
  byteTable_get_eq (fun _ h => mulByZ3_lt h) hv

theorem sq8T_eq_sq8 {v : UInt64} (hv : v.toNat < 2 ^ 8) : sq8T v = sq8 v :=
  byteTable_get_eq (fun _ h => sq8_lt h) hv

theorem inv8T_eq_inv8 {v : UInt64} (hv : v.toNat < 2 ^ 8) : inv8T v = inv8 v :=
  byteTable_get_eq (fun _ h => inv8_lt h) hv

theorem mul16T_eq_mul16 {a b : UInt64} (ha : a.toNat < 2 ^ 16) (hb : b.toNat < 2 ^ 16) :
    mul16T a b = mul16 a b := by
  obtain ⟨ha1, ha0⟩ := half16_lt ha
  obtain ⟨hb1, hb0⟩ := half16_lt hb
  simp only [mul16T, mul16]
  rw [mul8T_eq_mul8 ha0 hb0, mul8T_eq_mul8 ha1 hb1,
    mul8T_eq_mul8 (xor_lt ha0 ha1) (xor_lt hb0 hb1),
    mulByZ3T_eq_mulByZ3 (mul8_lt ha1 hb1)]

theorem mulByZ4T_eq_mulByZ4 {v : UInt64} (hv : v.toNat < 2 ^ 16) :
    mulByZ4T v = mulByZ4 v := by
  obtain ⟨hv1, -⟩ := half16_lt hv
  simp only [mulByZ4T, mulByZ4]
  rw [mulByZ3T_eq_mulByZ3 hv1]

theorem sq16T_eq_sq16 {v : UInt64} (hv : v.toNat < 2 ^ 16) :
    sq16T v = sq16 v := by
  obtain ⟨hv1, hv0⟩ := half16_lt hv
  simp only [sq16T, sq16]
  rw [sq8T_eq_sq8 hv0, sq8T_eq_sq8 hv1, mulByZ3T_eq_mulByZ3 (sq8_lt hv1)]

theorem inv16T_eq_inv16 {v : UInt64} (hv : v.toNat < 2 ^ 16) :
    inv16T v = inv16 v := by
  obtain ⟨hv1, hv0⟩ := half16_lt hv
  have hnext := xor_lt hv0 (mulByZ3_lt hv1)
  have hdelta := xor_lt (mul8_lt hv0 hnext) (sq8_lt hv1)
  simp only [inv16T, inv16]
  rw [mulByZ3T_eq_mulByZ3 hv1, sq8T_eq_sq8 hv1, mul8T_eq_mul8 hv0 hnext,
    inv8T_eq_inv8 hdelta,
    mul8T_eq_mul8 (inv8_lt hdelta) hv1,
    mul8T_eq_mul8 (inv8_lt hdelta) hnext]

theorem mul32T_eq_mul32 {a b : UInt64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    mul32T a b = mul32 a b := by
  obtain ⟨ha1, ha0⟩ := half32_lt ha
  obtain ⟨hb1, hb0⟩ := half32_lt hb
  simp only [mul32T, mul32]
  rw [mul16T_eq_mul16 ha0 hb0, mul16T_eq_mul16 ha1 hb1,
    mul16T_eq_mul16 (xor_lt ha0 ha1) (xor_lt hb0 hb1),
    mulByZ4T_eq_mulByZ4 (mul16_lt ha1 hb1)]

theorem mulByZ5T_eq_mulByZ5 {v : UInt64} (hv : v.toNat < 2 ^ 32) :
    mulByZ5T v = mulByZ5 v := by
  obtain ⟨hv1, -⟩ := half32_lt hv
  simp only [mulByZ5T, mulByZ5]
  rw [mulByZ4T_eq_mulByZ4 hv1]

theorem sq32T_eq_sq32 {v : UInt64} (hv : v.toNat < 2 ^ 32) :
    sq32T v = sq32 v := by
  obtain ⟨hv1, hv0⟩ := half32_lt hv
  simp only [sq32T, sq32]
  rw [sq16T_eq_sq16 hv0, sq16T_eq_sq16 hv1, mulByZ4T_eq_mulByZ4 (sq16_lt hv1)]

theorem inv32T_eq_inv32 {v : UInt64} (hv : v.toNat < 2 ^ 32) :
    inv32T v = inv32 v := by
  obtain ⟨hv1, hv0⟩ := half32_lt hv
  have hnext := xor_lt hv0 (mulByZ4_lt hv1)
  have hdelta := xor_lt (mul16_lt hv0 hnext) (sq16_lt hv1)
  simp only [inv32T, inv32]
  rw [mulByZ4T_eq_mulByZ4 hv1, sq16T_eq_sq16 hv1, mul16T_eq_mul16 hv0 hnext,
    inv16T_eq_inv16 hdelta,
    mul16T_eq_mul16 (inv16_lt hdelta) hv1,
    mul16T_eq_mul16 (inv16_lt hdelta) hnext]

theorem mul64T_eq_mul64 (a b : UInt64) :
    mul64T a b = mul64 a b := by
  obtain ⟨ha1, ha0⟩ := half64_lt a
  obtain ⟨hb1, hb0⟩ := half64_lt b
  simp only [mul64T, mul64]
  rw [mul32T_eq_mul32 ha0 hb0, mul32T_eq_mul32 ha1 hb1,
    mul32T_eq_mul32 (xor_lt ha0 ha1) (xor_lt hb0 hb1),
    mulByZ5T_eq_mulByZ5 (mul32_lt ha1 hb1)]

theorem mulByZ6T_eq_mulByZ6 (v : UInt64) :
    mulByZ6T v = mulByZ6 v := by
  obtain ⟨hv1, -⟩ := half64_lt v
  simp only [mulByZ6T, mulByZ6]
  rw [mulByZ5T_eq_mulByZ5 hv1]

theorem sq64T_eq_sq64 (v : UInt64) :
    sq64T v = sq64 v := by
  obtain ⟨hv1, hv0⟩ := half64_lt v
  simp only [sq64T, sq64]
  rw [sq32T_eq_sq32 hv0, sq32T_eq_sq32 hv1, mulByZ5T_eq_mulByZ5 (sq32_lt hv1)]

theorem inv64T_eq_inv64 (v : UInt64) :
    inv64T v = inv64 v := by
  obtain ⟨hv1, hv0⟩ := half64_lt v
  have hnext := xor_lt hv0 (mulByZ5_lt hv1)
  have hdelta := xor_lt (mul32_lt hv0 hnext) (sq32_lt hv1)
  simp only [inv64T, inv64]
  rw [mulByZ5T_eq_mulByZ5 hv1, sq32T_eq_sq32 hv1, mul32T_eq_mul32 hv0 hnext,
    inv32T_eq_inv32 hdelta,
    mul32T_eq_mul32 (inv32_lt hdelta) hv1,
    mul32T_eq_mul32 (inv32_lt hdelta) hnext]

/-! ## Correctness against the spec

The twins agree with `concrete_mul` / `concrete_inv` on in-range words, by induction on
the level; statements go through `fromNat` so the spec side reasons inside
`ConcreteBTField`. -/

theorem toNat_fromNat {k n : ℕ} (h : n < 2 ^ 2 ^ k) :
    BitVec.toNat (fromNat (k := k) n) = n := by
  show (BitVec.ofNat (2 ^ k) n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

theorem fromNat_toNat {k : ℕ} (x : ConcreteBTField k) : fromNat x.toNat = x :=
  BitVec.eq_of_toNat_eq (toNat_fromNat x.isLt)

theorem eq_zero_or_one {v : UInt64} (hv : v.toNat < 2 ^ 2 ^ 0) : v = 0 ∨ v = 1 := by
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1) with h | h
  · exact Or.inl (UInt64.toNat_inj.mp h)
  · exact Or.inr (UInt64.toNat_inj.mp h)

theorem fromNat_zero {k : ℕ} :
    fromNat (k := k) (0 : UInt64).toNat = (0 : ConcreteBTField k) := rfl

theorem fromNat_one {k : ℕ} :
    fromNat (k := k) (1 : UInt64).toNat = (1 : ConcreteBTField k) := rfl

theorem shiftRight_toNat {k : ℕ} (hk : k ≤ 5) (a : UInt64) :
    (a >>> UInt64.ofNat (2 ^ k)).toNat = a.toNat >>> 2 ^ k := by
  have h32 : 2 ^ k ≤ 32 := Nat.pow_le_pow_right (by omega) hk
  rw [UInt64.toNat_shiftRight, toNat_ofNat_two_pow hk, Nat.mod_eq_of_lt (by omega)]

theorem and_mask_toNat {k : ℕ} (hk : k ≤ 5) (a : UInt64) :
    (a &&& ((1 : UInt64) <<< UInt64.ofNat (2 ^ k) - 1)).toNat
      = a.toNat &&& (2 ^ 2 ^ k - 1) := by
  rw [UInt64.toNat_and, toNat_mask_two_pow hk]

theorem join_word_toNat {k : ℕ} (hk : k + 1 ≤ 6) {hi : UInt64}
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

theorem nat_join_shiftRight {H L s : ℕ} (hL : L < 2 ^ s) :
    (H <<< s ||| L) >>> s = H := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mul_comm H (2 ^ s), Nat.mul_add_div (Nat.two_pow_pos s), Nat.div_eq_of_lt hL,
    Nat.add_zero]

theorem nat_join_and {H L s : ℕ} (hL : L < 2 ^ s) :
    (H <<< s ||| L) &&& (2 ^ s - 1) = L := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hL, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
    Nat.mul_comm H (2 ^ s), Nat.mul_add_mod, Nat.mod_eq_of_lt hL]

theorem fromNat_xor {k : ℕ} (x y : UInt64) :
    fromNat (k := k) (x ^^^ y).toNat = fromNat x.toNat + fromNat y.toNat := by
  rw [UInt64.toNat_xor]
  exact sum_fromNat_eq_from_xor_Nat _ _

theorem fromNat_join {k : ℕ} (hk : k + 1 ≤ 6) {hi lo : UInt64}
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

theorem split_fromNat {k : ℕ} (hk : k + 1 ≤ 6) {a : UInt64}
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

theorem concrete_mul_eq_mul {k : ℕ} (x y : ConcreteBTField k) :
    concrete_mul x y = x * y := rfl

/-- `concrete_mul`'s one-level structure theorem, restated with all indices at the
half level `k` (the original lives at `k + 1 - 1`, which blocks syntactic rewriting). -/
theorem concrete_mul_step {k : ℕ} (a b : ConcreteBTField (k + 1))
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

theorem split_zero' {k : ℕ} : split (Nat.succ_pos k) (0 : ConcreteBTField (k + 1))
    = ((0 : ConcreteBTField k), (0 : ConcreteBTField k)) := split_zero (Nat.succ_pos k)

theorem split_one' {k : ℕ} : split (Nat.succ_pos k) (1 : ConcreteBTField (k + 1))
    = ((0 : ConcreteBTField k), (1 : ConcreteBTField k)) := split_one (Nat.succ_pos k)

/-- `concrete_inv`'s one-level descent, restated at the half level `k`; the `a = 0`
and `a = 1` branches satisfy the same formula. -/
theorem concrete_inv_step {k : ℕ} (a : ConcreteBTField (k + 1))
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
    BitVec.toNat (toConcrete x) = x.val.toNat := toNat_fromNat x.isLt

theorem toConcrete_injective : Function.Injective (toConcrete (k := k)) := by
  intro a b h
  have hval : a.val = b.val := by
    have := congrArg BitVec.toNat h
    rw [toConcrete_toNat, toConcrete_toNat] at this
    exact UInt64.toNat_inj.mp this
  cases a; cases b
  simp only [FastBT.mk.injEq]
  exact hval

theorem ofConcrete_val_toNat {k : ℕ} (hk : k ≤ 6) (x : ConcreteBTField k) :
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
    toConcrete (a + b) = toConcrete a + toConcrete b := fromNat_xor a.val b.val

@[simp] theorem toConcrete_neg (a : FastBT k) : toConcrete (-a) = -(toConcrete a) := rfl

@[simp] theorem toConcrete_sub (a b : FastBT k) :
    toConcrete (a - b) = toConcrete a - toConcrete b := by
  rw [sub_def, toConcrete_add, sub_eq_add_neg, ← toConcrete_neg, neg_def]

theorem toConcrete_if_zero {p : Prop} [Decidable p] (x : FastBT k) :
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
@[inline] def BT8.mul (a b : BT8) : BT8 :=
  .mk (mul8T a.val b.val) (by rw [mul8T_eq_mul8 a.isLt b.isLt]; exact mul8_lt a.isLt b.isLt)
/-- GF(2^16) carrier multiplication. -/
@[inline] def BT16.mul (a b : BT16) : BT16 :=
  .mk (mul16T a.val b.val) (by rw [mul16T_eq_mul16 a.isLt b.isLt]; exact mul16_lt a.isLt b.isLt)
/-- GF(2^32) carrier multiplication. -/
@[inline] def BT32.mul (a b : BT32) : BT32 :=
  .mk (mul32T a.val b.val) (by rw [mul32T_eq_mul32 a.isLt b.isLt]; exact mul32_lt a.isLt b.isLt)
/-- GF(2^64) carrier multiplication. -/
@[inline] def BT64.mul (a b : BT64) : BT64 := .mk (mul64T a.val b.val) (UInt64.toNat_lt _)

instance : Mul BT8 := ⟨BT8.mul⟩
instance : Mul BT16 := ⟨BT16.mul⟩
instance : Mul BT32 := ⟨BT32.mul⟩
instance : Mul BT64 := ⟨BT64.mul⟩

@[simp] theorem val_mul_bt8 (a b : BT8) : (a * b).val = mul8 a.val b.val :=
  mul8T_eq_mul8 a.isLt b.isLt
@[simp] theorem val_mul_bt16 (a b : BT16) : (a * b).val = mul16 a.val b.val :=
  mul16T_eq_mul16 a.isLt b.isLt
@[simp] theorem val_mul_bt32 (a b : BT32) : (a * b).val = mul32 a.val b.val :=
  mul32T_eq_mul32 a.isLt b.isLt
@[simp] theorem val_mul_bt64 (a b : BT64) : (a * b).val = mul64 a.val b.val :=
  mul64T_eq_mul64 a.val b.val

@[simp] theorem toConcrete_mul_bt8 (a b : BT8) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul8T a.val b.val).toNat = _
  rw [mul8T_eq_mul8 a.isLt b.isLt, mul8_eq_rec]
  exact mulRec_correct 3 (by omega) a.val b.val a.isLt b.isLt

@[simp] theorem toConcrete_mul_bt16 (a b : BT16) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul16T a.val b.val).toNat = _
  rw [mul16T_eq_mul16 a.isLt b.isLt, mul16_eq_rec]
  exact mulRec_correct 4 (by omega) a.val b.val a.isLt b.isLt

@[simp] theorem toConcrete_mul_bt32 (a b : BT32) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul32T a.val b.val).toNat = _
  rw [mul32T_eq_mul32 a.isLt b.isLt, mul32_eq_rec]
  exact mulRec_correct 5 (by omega) a.val b.val a.isLt b.isLt

@[simp] theorem toConcrete_mul_bt64 (a b : BT64) :
    toConcrete (a * b) = toConcrete a * toConcrete b := by
  show fromNat (mul64T a.val b.val).toNat = _
  rw [mul64T_eq_mul64 a.val b.val, mul64_eq_rec]
  exact mulRec_correct 6 (by omega) a.val b.val a.isLt b.isLt

instance : Inv BT8 :=
  ⟨fun a => .mk (inv8T a.val) (by rw [inv8T_eq_inv8 a.isLt]; exact inv8_lt a.isLt)⟩
instance : Inv BT16 :=
  ⟨fun a => .mk (inv16T a.val) (by rw [inv16T_eq_inv16 a.isLt]; exact inv16_lt a.isLt)⟩
instance : Inv BT32 :=
  ⟨fun a => .mk (inv32T a.val) (by rw [inv32T_eq_inv32 a.isLt]; exact inv32_lt a.isLt)⟩
instance : Inv BT64 := ⟨fun a => .mk (inv64T a.val) (UInt64.toNat_lt _)⟩

@[simp] theorem val_inv_bt8 (a : BT8) : (a⁻¹).val = inv8 a.val := inv8T_eq_inv8 a.isLt
@[simp] theorem val_inv_bt16 (a : BT16) : (a⁻¹).val = inv16 a.val := inv16T_eq_inv16 a.isLt
@[simp] theorem val_inv_bt32 (a : BT32) : (a⁻¹).val = inv32 a.val := inv32T_eq_inv32 a.isLt
@[simp] theorem val_inv_bt64 (a : BT64) : (a⁻¹).val = inv64 a.val := inv64T_eq_inv64 a.val

@[simp] theorem toConcrete_inv_bt8 (a : BT8) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv8T a.val).toNat = _
  rw [inv8T_eq_inv8 a.isLt, inv8_eq_rec]
  exact invRec_correct 3 (by omega) a.val a.isLt

@[simp] theorem toConcrete_inv_bt16 (a : BT16) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv16T a.val).toNat = _
  rw [inv16T_eq_inv16 a.isLt, inv16_eq_rec]
  exact invRec_correct 4 (by omega) a.val a.isLt

@[simp] theorem toConcrete_inv_bt32 (a : BT32) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv32T a.val).toNat = _
  rw [inv32T_eq_inv32 a.isLt, inv32_eq_rec]
  exact invRec_correct 5 (by omega) a.val a.isLt

@[simp] theorem toConcrete_inv_bt64 (a : BT64) : toConcrete a⁻¹ = (toConcrete a)⁻¹ := by
  show fromNat (inv64T a.val).toNat = _
  rw [inv64T_eq_inv64 a.val, inv64_eq_rec]
  exact invRec_correct 6 (by omega) a.val a.isLt

theorem toConcrete_npowRec {k : ℕ} [Mul (FastBT k)]
    (hmul : ∀ a b : FastBT k, toConcrete (a * b) = toConcrete a * toConcrete b)
    (a : FastBT k) : ∀ (n : ℕ), toConcrete (npowRec n a) = toConcrete a ^ n
  | 0 => by rw [npowRec, pow_zero, toConcrete_one]
  | n + 1 => by rw [npowRec, pow_succ, hmul, toConcrete_npowRec hmul a n]

/-- Assemble a width's `Field` instance from its `toConcrete` multiplication and
inversion lemmas. -/
@[reducible] def fieldOfHoms {k : ℕ} [Mul (FastBT k)] [Inv (FastBT k)]
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

@[reducible] def ringEquivOfHom {k : ℕ} [Mul (FastBT k)] (hk : k ≤ 6)
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
  | 3, a => .mk (mulByZ3T a.val)
      (by rw [mulByZ3T_eq_mulByZ3 a.isLt]; exact mulByZ3_lt a.isLt)
  | 4, a => .mk (mulByZ4T a.val)
      (by rw [mulByZ4T_eq_mulByZ4 a.isLt]; exact mulByZ4_lt a.isLt)
  | 5, a => .mk (mulByZ5T a.val)
      (by rw [mulByZ5T_eq_mulByZ5 a.isLt]; exact mulByZ5_lt a.isLt)
  | 6, a => .mk (mulByZ6T a.val) (UInt64.toNat_lt _)
  | _ + 7, a => a

theorem FastBT.mulByZ_val : ∀ {k : ℕ} (a : FastBT k) (hk : k ≤ 6),
    (a.mulByZ hk).val = mulByZRec k a.val
  | 0, _, _ => rfl
  | 1, a, _ => mulByZ1_eq_rec a.val
  | 2, a, _ => mulByZ2_eq_rec a.val
  | 3, a, _ => (mulByZ3T_eq_mulByZ3 a.isLt).trans (mulByZ3_eq_rec a.val)
  | 4, a, _ => (mulByZ4T_eq_mulByZ4 a.isLt).trans (mulByZ4_eq_rec a.val)
  | 5, a, _ => (mulByZ5T_eq_mulByZ5 a.isLt).trans (mulByZ5_eq_rec a.val)
  | 6, a, _ => (mulByZ6T_eq_mulByZ6 a.val).trans (mulByZ6_eq_rec a.val)
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
  | 3, a => .mk (sq8T a.val) (by rw [sq8T_eq_sq8 a.isLt]; exact sq8_lt a.isLt)
  | 4, a => .mk (sq16T a.val) (by rw [sq16T_eq_sq16 a.isLt]; exact sq16_lt a.isLt)
  | 5, a => .mk (sq32T a.val) (by rw [sq32T_eq_sq32 a.isLt]; exact sq32_lt a.isLt)
  | 6, a => .mk (sq64T a.val) (UInt64.toNat_lt _)
  | _ + 7, a => a

theorem FastBT.square_val : ∀ {k : ℕ} (a : FastBT k) (hk : k ≤ 6),
    (a.square hk).val = sqRec k a.val
  | 0, _, _ => rfl
  | 1, a, _ => sq2_eq_rec a.val
  | 2, a, _ => sq4_eq_rec a.val
  | 3, a, _ => (sq8T_eq_sq8 a.isLt).trans (sq8_eq_rec a.val)
  | 4, a, _ => (sq16T_eq_sq16 a.isLt).trans (sq16_eq_rec a.val)
  | 5, a, _ => (sq32T_eq_sq32 a.isLt).trans (sq32_eq_rec a.val)
  | 6, a, _ => (sq64T_eq_sq64 a.val).trans (sq64_eq_rec a.val)
  | _ + 7, _, hk => absurd hk (by omega)

theorem toConcrete_square {k : ℕ} (a : FastBT k) (hk : k ≤ 6) :
    toConcrete (a.square hk) = toConcrete a * toConcrete a := by
  show fromNat (a.square hk).val.toNat = _
  rw [a.square_val hk]
  exact sqRec_correct k hk a.val a.isLt

/-! ## Level 7: GF(2^128)

The tower split falls on the limb boundary, so the halves are the limbs. -/

theorem join_add_join {k : ℕ} (a b c d : ConcreteBTField k) :
    (《 a, b 》 : ConcreteBTField (k + 1)) + (《 c, d 》 : ConcreteBTField (k + 1))
      = (《 a + c, b + d 》 : ConcreteBTField (k + 1)) :=
  join_of_split (Nat.succ_pos k) _ _ _
    (split_sum_eq_sum_split (Nat.succ_pos k) _ _ a b c d
      (split_join_eq_split (Nat.succ_pos k) a b) (split_join_eq_split (Nat.succ_pos k) c d))

/-! Width-64 spec forms of the word operations; every `UInt64` is in range at level 6. -/

theorem fromNat_mul64 (a b : UInt64) :
    fromNat (k := 6) (mul64 a b).toNat = concrete_mul (fromNat a.toNat) (fromNat b.toNat) := by
  rw [mul64_eq_rec]
  exact mulRec_correct 6 le_rfl a b (UInt64.toNat_lt a) (UInt64.toNat_lt b)

theorem fromNat_sq64 (v : UInt64) :
    fromNat (k := 6) (sq64 v).toNat = concrete_mul (fromNat v.toNat) (fromNat v.toNat) := by
  rw [sq64_eq_rec]
  exact sqRec_correct 6 le_rfl v (UInt64.toNat_lt v)

theorem fromNat_mulByZ6 (v : UInt64) :
    fromNat (k := 6) (mulByZ6 v).toNat = concrete_mul (fromNat v.toNat) (Z 6) := by
  rw [mulByZ6_eq_rec]
  exact mulByZRec_correct 6 le_rfl v (UInt64.toNat_lt v)

theorem fromNat_inv64 (v : UInt64) :
    fromNat (k := 6) (inv64 v).toNat = concrete_inv (fromNat v.toNat) := by
  rw [inv64_eq_rec]
  exact invRec_correct 6 le_rfl v (UInt64.toNat_lt v)

namespace FastBT128

instance : Zero FastBT128 := ⟨0, 0⟩
instance : One FastBT128 := ⟨1, 0⟩

instance : Add FastBT128 := ⟨add⟩
instance : Neg FastBT128 := ⟨id⟩
instance : Sub FastBT128 where sub a b := a + b
instance : Mul FastBT128 := ⟨mul⟩

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

theorem toConcrete_if_zero {p : Prop} [Decidable p] (x : FastBT128) :
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
  show (《 fromNat (k := 6) (mul64T (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
            ^^^ (mul64T a.lo b.lo ^^^ mul64T a.hi b.hi)
            ^^^ mulByZ6T (mul64T a.hi b.hi)).toNat,
          fromNat (k := 6) (mul64T a.lo b.lo ^^^ mul64T a.hi b.hi).toNat 》 :
      ConcreteBTField 7) = _
  simp only [mul64T_eq_mul64, mulByZ6T_eq_mulByZ6, fromNat_xor, fromNat_mul64,
    fromNat_mulByZ6]
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
  show (《 fromNat (k := 6) (v.lo ^^^ mulByZ6T v.hi).toNat, fromNat (k := 6) v.hi.toNat 》 :
      ConcreteBTField 7) = _
  simp only [mulByZ6T_eq_mulByZ6, fromNat_xor, fromNat_mulByZ6]
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
  show (《 fromNat (k := 6) (mulByZ6T (sq64T v.hi)).toNat,
          fromNat (k := 6) (sq64T v.lo ^^^ sq64T v.hi).toNat 》 : ConcreteBTField 7) = _
  simp only [sq64T_eq_sq64, mulByZ6T_eq_mulByZ6, fromNat_xor, fromNat_sq64,
    fromNat_mulByZ6]
  refine Eq.trans ?_ hme.symm
  simp only [concrete_mul_eq_mul]
  rw [← two_mul, CharTwo.two_eq_zero (R := ConcreteBTField 6), zero_mul, zero_add]

@[simp] theorem toConcrete_inv (v : FastBT128) : toConcrete v⁻¹ = (toConcrete v)⁻¹ := by
  have hme := concrete_inv_step (toConcrete v)
    (split_of_join (Nat.succ_pos 6) (toConcrete v) (fromNat (k := 6) v.hi.toNat)
      (fromNat (k := 6) v.lo.toNat) rfl)
  show (《 fromNat (k := 6)
            (mul64T (inv64T (mul64T v.lo (v.lo ^^^ mulByZ6T v.hi) ^^^ sq64T v.hi)) v.hi).toNat,
          fromNat (k := 6)
            (mul64T (inv64T (mul64T v.lo (v.lo ^^^ mulByZ6T v.hi) ^^^ sq64T v.hi))
              (v.lo ^^^ mulByZ6T v.hi)).toNat 》 : ConcreteBTField 7) = _
  simp only [mul64T_eq_mul64, mulByZ6T_eq_mulByZ6, sq64T_eq_sq64, inv64T_eq_inv64,
    fromNat_xor, fromNat_mul64, fromNat_sq64, fromNat_mulByZ6, fromNat_inv64]
  exact hme.symm

theorem toConcrete_npowRec (a : FastBT128) :
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
