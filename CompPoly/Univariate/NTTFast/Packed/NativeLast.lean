/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.NativeOrder
import CompPoly.Univariate.NTTFast.Packed.Unrolled

/-! # Fused final leaf layers and leaf reversal

The last four DIF layers of a leaf act inside sixteen-word blocks, and the leaf reversal then
reads one word from each of sixteen blocks `L` words apart, `L = 2 ^ (m - 4)`. `lastHalf` runs
both for eight such blocks at once, one block per vector lane, and writes eight words of each of
sixteen natural-order lines; two calls per batch of sixteen block columns complete the lines.

The layers above run as radix-four passes from the top; an odd leaf first runs its single
radix-two layer, so every leaf of at least `2 ^ 8` words ends with the fused final layers.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

/-- `1 <<< k` on machine words, for `k < 32`. -/
theorem one_shiftLeft_toNat (k : USize) (hk : k.toNat < 32) :
    ((1 : USize) <<< k).toNat = 2 ^ k.toNat := by
  have hb : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  rw [USize.toNat_shiftLeft, USize.toNat_one, Nat.one_shiftLeft,
    Nat.mod_eq_of_lt (show k.toNat < System.Platform.numBits by omega),
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]

/-- The output check of `lastHalf` in natural numbers. -/
theorem lastHalf_check {out : ByteArray} {shift : UInt32} {half : USize}
    (h : 0 < shift ∧ shift < 32 ∧ half < 2 ∧
      (1 : USize) <<< (32 - shift).toUSize ≤ out.usize / 64) :
    0 < shift.toNat ∧ shift.toNat < 32 ∧ half.toNat < 2 ∧
      64 * 2 ^ (32 - shift.toNat) ≤ out.usize.toNat := by
  obtain ⟨h0, hs, hh, hl⟩ := h
  rw [UInt32.lt_iff_toNat_lt, show (0 : UInt32).toNat = 0 from rfl] at h0
  rw [UInt32.lt_iff_toNat_lt, show (32 : UInt32).toNat = 32 from rfl] at hs
  rw [USize.lt_iff_toNat_lt, usize_numeral 2 (by decide)] at hh
  have hk : (32 - shift).toUSize.toNat = 32 - shift.toNat := by
    rw [UInt32.toNat_toUSize, UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le]; change shift.toNat ≤ 32; omega)]
    rfl
  rw [USize.le_iff_toNat_le, one_shiftLeft_toNat _ (by rw [hk]; omega), hk, USize.toNat_div,
    usize_numeral 64 (by decide)] at hl
  exact ⟨h0, hs, hh, by omega⟩

/-- Lines `y >>> shift` of sixteen words fit an output of `2 ^ (32 - shift)` lines. -/
theorem lastHalf_store {out : ByteArray} {shift : UInt32} {half : USize}
    (h : 0 < shift ∧ shift < 32 ∧ half < 2 ∧
      (1 : USize) <<< (32 - shift).toUSize ≤ out.usize / 64)
    (y : UInt32) :
    (4 * (16 * (y >>> shift).toUSize + 8 * half)).toNat + 4 * 8 ≤ out.size ∧
      (4 * (16 * (y >>> shift).toUSize + 8 * half)).toNat + 4 * 8 < USize.size := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hb := toNat_usize_le out
  have hU := out.usize.toNat_lt_size
  obtain ⟨_, hs, hh, hl⟩ := lastHalf_check h
  have hr : (y >>> shift).toNat < 2 ^ (32 - shift.toNat) := by
    rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt (show shift.toNat < 32 by omega),
      Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      ← Nat.pow_add, show 32 - shift.toNat + shift.toNat = 32 by omega]
    exact y.toNat_lt
  have hr' : (y >>> shift).toUSize.toNat = (y >>> shift).toNat := UInt32.toNat_toUSize _
  have e : (4 * (16 * (y >>> shift).toUSize + 8 * half)).toNat =
      4 * (16 * (y >>> shift).toNat + 8 * half.toNat) := by
    simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, hr', hsize]
    rw [Nat.mod_eq_of_lt (show 16 * (y >>> shift).toNat < USize.size by omega),
      Nat.mod_eq_of_lt (show 8 * half.toNat < USize.size by omega),
      Nat.mod_eq_of_lt (show 16 * (y >>> shift).toNat + 8 * half.toNat < USize.size by omega),
      Nat.mod_eq_of_lt (show 4 * (16 * (y >>> shift).toNat + 8 * half.toNat) < USize.size by
        omega)]
  rw [e]
  omega

/-- An output with room for one line has room for the touched last word. -/
theorem lastHalf_usize {out : ByteArray} {shift : UInt32} {half : USize}
    (h : 0 < shift ∧ shift < 32 ∧ half < 2 ∧
      (1 : USize) <<< (32 - shift).toUSize ≤ out.usize / 64) :
    4 ≤ out.usize := by
  have hl := (lastHalf_check h).2.2.2
  have := Nat.one_le_two_pow (n := 32 - shift.toNat)
  rw [USize.le_iff_toNat_le, usize_numeral 4 (by decide)]
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The last four DIF layers of the eight blocks at `i0, …, i7`, written to `out` as
half `half` of the natural-order lines `bitrev (16 c + t)`: lane `k` supplies word
`8 half + k` of each line, optionally scaled. The lanes are independent, so the compiler
runs them as vector lanes. -/
@[noinline, specialize]
def lastHalf (p : ℕ) [Mont32Field p] (t3 t2 t1 b : @& ByteArray) (i0 i1 i2 i3 i4 i5 i6 i7 c : USize)
    (shift : UInt32) (half : USize) (factor : UInt32) (scale : Bool) (out : ByteArray)
    (h : 4 * (i0.toNat + 15) + 3 < b.size ∧
      4 * (i1.toNat + 15) + 3 < b.size ∧
      4 * (i2.toNat + 15) + 3 < b.size ∧
      4 * (i3.toNat + 15) + 3 < b.size ∧
      4 * (i4.toNat + 15) + 3 < b.size ∧
      4 * (i5.toNat + 15) + 3 < b.size ∧
      4 * (i6.toNat + 15) + 3 < b.size ∧
      4 * (i7.toNat + 15) + 3 < b.size ∧
      b.size < USize.size ∧
      31 < t3.size ∧
      t3.size < USize.size ∧
      15 < t2.size ∧
      t2.size < USize.size ∧
      7 < t1.size ∧
      t1.size < USize.size) :
    ByteArray :=
  if hout : 0 < shift ∧ shift < 32 ∧ half < 2 ∧
      (1 : USize) <<< (32 - shift).toUSize ≤ out.usize / 64 then
    lastHalf_words%
  else out

/-- Block `v`'s word index at batch `c` stays in range. -/
theorem laneBound (v : USize) (hv : v.toNat < 16) (Lw c : USize) (b : ByteArray)
    (hL : 64 * Lw.toNat ≤ b.size) (hb : b.size < USize.size)
    (hc : 16 * c.toNat + 16 ≤ Lw.toNat) : 4 * ((v * Lw + 16 * c).toNat + 15) + 3 < b.size := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hvL : v.toNat * Lw.toNat ≤ 15 * Lw.toNat := Nat.mul_le_mul_right _ (by omega)
  simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, hsize]
  rw [Nat.mod_eq_of_lt (show v.toNat * Lw.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show 16 * c.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show v.toNat * Lw.toNat + 16 * c.toNat < USize.size by omega)]
  omega

/-- Batches `c, …, c + n - 1` of sixteen block columns, both halves each. -/
@[specialize]
def lastRevGo (p : ℕ) [Mont32Field p] (t3 t2 t1 b : @& ByteArray) (Lw : USize)
    (shift factor : UInt32) (scale : Bool)
    (hb : 64 * Lw.toNat ≤ b.size ∧ b.size < USize.size ∧ 31 < t3.size ∧ t3.size < USize.size ∧
      15 < t2.size ∧ t2.size < USize.size ∧ 7 < t1.size ∧ t1.size < USize.size) :
    Nat → USize → ByteArray → ByteArray
  | 0, _, out => out
  | n + 1, c, out =>
    if hc : 16 * c.toNat + 16 ≤ Lw.toNat then
      let out := lastHalf p t3 t2 t1 b (0 * Lw + 16 * c) (8 * Lw + 16 * c) (4 * Lw + 16 * c)
          (12 * Lw + 16 * c)
        (2 * Lw + 16 * c) (10 * Lw + 16 * c) (6 * Lw + 16 * c) (14 * Lw + 16 * c)
        c shift 0 factor scale out
        ⟨laneBound 0 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 8 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 4 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 12 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 2 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 10 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 6 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 14 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          hb.2.1, hb.2.2⟩
      let out := lastHalf p t3 t2 t1 b (1 * Lw + 16 * c) (9 * Lw + 16 * c) (5 * Lw + 16 * c)
          (13 * Lw + 16 * c)
        (3 * Lw + 16 * c) (11 * Lw + 16 * c) (7 * Lw + 16 * c) (15 * Lw + 16 * c)
        c shift 1 factor scale out
        ⟨laneBound 1 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 9 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 5 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 13 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 3 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 11 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 7 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 15 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          hb.2.1, hb.2.2⟩
      lastRevGo p t3 t2 t1 b Lw shift factor scale hb n (c + 1) out
    else out

/-- The last four DIF layers of a `2 ^ m`-word leaf whose earlier layers are done, in natural
order, optionally scaled. The output starts as a copy of the input, which the first store makes
because the input stays borrowed; every word is then overwritten. -/
@[specialize]
def lastRev (p : ℕ) [Mont32Field p] (t3 t2 t1 b : @& ByteArray) (m : Nat) (factor : UInt32)
    (scale : Bool) :
    ByteArray :=
  if h : 2 ^ (m - 4) < USize.size ∧ 64 * 2 ^ (m - 4) ≤ b.size ∧ b.size < USize.size ∧
      31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
      7 < t1.size ∧ t1.size < USize.size then
    lastRevGo p t3 t2 t1 b (USize.ofNatLT (2 ^ (m - 4)) h.1) (32 - (m - 4)).toUInt32 factor scale
      (by simpa only [USize.toNat_ofNatLT] using h.2) (2 ^ (m - 4) / 16) 0 b
  else b

/-- `blocks` radix-four blocks of quarter `q`, the first at word `0`: for quarters of whole
sixteen-cell batches one range check covers all blocks, otherwise each block checks its own. -/
@[specialize]
def radix4Blocks (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (q blocks : Nat)
    (a : ByteArray) : ByteArray :=
  if h : q % 16 = 0 ∧ 4 * (4 * q * blocks) ≤ a.size ∧ 4 * (2 * q) ≤ th.size ∧
      4 * q ≤ tl.size ∧ a.size < USize.size ∧ th.size < USize.size ∧ tl.size < USize.size then
    blocks16Loop p th tl (q / 16) (USize.ofNatLT q (by omega)) blocks 0 a (by
      simp only [USize.toNat_ofNatLT, USize.toNat_zero]
      omega)
  else Id.run do
    let mut a := a
    for block in [:blocks] do
      a := inner16 p th tl q 0 (block * (4 * q)) (block * (4 * q) + q) (block * (4 * q) + 2 * q)
        (block * (4 * q) + 3 * q) a
    return a

/-- The leading layers of a `2 ^ m`-word leaf: for odd `m` the radix-two top layer, then `count`
radix-four passes. -/
@[specialize]
def leafLayers (p : ℕ) [Mont32Field p] (tw : @& Array ByteArray) (m count : Nat)
    (a : ByteArray) : ByteArray :=
  let a := if m % 2 = 1 then pairs p (tw.getD (m - 1) .empty) (2 ^ (m - 1)) 0 0 (2 ^ (m - 1)) a
    else a
  (List.range count).foldl (fun a pass ↦
    let high := m - 1 - m % 2 - 2 * pass
    let q := 2 ^ (high - 1)
    radix4Blocks p (tw.getD high .empty) (tw.getD (high - 1) .empty) q (2 ^ m / (4 * q)) a) a

/-- A complete `2 ^ m`-word leaf in natural order, optionally scaled. Leaves of at least `2 ^ 8`
words end with the fused final layers, smaller ones with a scalar reversal. -/
@[specialize]
def leafNatural (p : ℕ) [Mont32Field p] (tw : Array ByteArray) (m : Nat) (factor : UInt32)
    (scale : Bool)
    (a : ByteArray) : ByteArray :=
  if 8 ≤ m then
    lastRev p (tw.getD 3 .empty) (tw.getD 2 .empty) (tw.getD 1 .empty) (leafLayers p tw m
    (m / 2 - 2) a)
      m factor scale
  else encodeFields (decode p m (leafLayers p tw m (m / 2) a) factor scale)

/-- The last four DIF layers of the sixteen-word block at `i`, in place: the block's outputs stay
in DIF (bit-reversed) order. -/
@[noinline, specialize]
def leaf16 (p : ℕ) [Mont32Field p] (t3 t2 t1 : @& ByteArray) (i : USize) (b : ByteArray)
    (h : 4 * (i.toNat + 15) + 3 < b.size ∧ b.size < USize.size ∧
      31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
      7 < t1.size ∧ t1.size < USize.size) : ByteArray :=
  leaf16_words%

/-- Four sixteen-word blocks from word `i` of `b`, and `K` twiddles in `t`: the range checks of a
stage kernel. -/
abbrev LeafStageFits (b t : ByteArray) (i : USize) (K : Nat) : Prop :=
  4 * (i.toNat + 64) ≤ b.size ∧ b.size < USize.size ∧ 4 * K ≤ t.size ∧ t.size < USize.size

/-- A stage kernel's buffer has room for the touched last word. -/
theorem leafStage_touch {b t : ByteArray} {i : USize} {K : Nat} (h : LeafStageFits b t i K) :
    4 ≤ b.usize := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hu : b.usize.toNat = b.size := by
    rw [ByteArray.usize, Nat.toUSize, USize.toNat_ofNat_of_lt' h2]
  rw [USize.le_iff_toNat_le, hu, usize_numeral 4 (by decide)]
  omega

/-- Word `k` of a stage kernel's blocks fits its buffer, of the same size as `b`. -/
theorem leafStage_read {b t o : ByteArray} {i : USize} {K : Nat} (h : LeafStageFits b t i K)
    (ho : o.size = b.size) (k : Nat) (hk : k < 64) :
    4 * (i.toNat + (OfNat.ofNat k : USize).toNat) + 3 < o.size ∧ o.size < USize.size := by
  obtain ⟨h1, h2, -, -⟩ := h
  rw [usize_numeral k (by omega), ho]
  exact ⟨by omega, h2⟩

/-- Twiddle `k < K` of a stage kernel fits its table. -/
theorem leafStage_twiddle {b t : ByteArray} {i : USize} {K : Nat} (h : LeafStageFits b t i K)
    (k : Nat) (hk : k < K) (hk8 : k < 8) :
    4 * ((0 : USize).toNat + (OfNat.ofNat k : USize).toNat) + 3 < t.size ∧
      t.size < USize.size := by
  obtain ⟨-, -, h3, h4⟩ := h
  rw [usize_numeral k (by omega), USize.toNat_zero]
  exact ⟨by omega, h4⟩

/-- The eight words from word `i + c` of a stage kernel's blocks fit its buffer. -/
theorem leafStage_store {b t : ByteArray} {i : USize} {K : Nat} (h : LeafStageFits b t i K)
    (c : Nat) (hc : c + 8 ≤ 64) :
    ((i + OfNat.ofNat c) * 4).toNat + 4 * 8 ≤ b.size ∧
      ((i + OfNat.ofNat c) * 4).toNat + 4 * 8 < USize.size := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hc' : (OfNat.ofNat c : USize).toNat = c := usize_numeral c (by omega)
  rw [wordOffset_toNat _ _ (by rw [hc']; omega), hc']
  exact ⟨by omega, by omega⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The first of the four final DIF layers in place on the four blocks from word `i`: words `k` and
`k + 8` of a block, the difference times twiddle `k` of `t3`. -/
@[noinline, specialize]
def leafStage8 (p : ℕ) [Mont32Field p] (t : @& ByteArray) (i : USize) (b : ByteArray)
    (h : LeafStageFits b t i 8) : Buf b.size :=
  leafStage8_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The second of the four final DIF layers in place: words `k` and `k + 4` of a half block, the
difference times twiddle `k` of `t2`. -/
@[noinline, specialize]
def leafStage4 (p : ℕ) [Mont32Field p] (t : @& ByteArray) (i : USize) (b : ByteArray)
    (h : LeafStageFits b t i 4) : Buf b.size :=
  leafStage4_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The third of the four final DIF layers in place: words `k` and `k + 2` of a quarter block, the
difference times twiddle `k` of `t1`. -/
@[noinline, specialize]
def leafStage2 (p : ℕ) [Mont32Field p] (t : @& ByteArray) (i : USize) (b : ByteArray)
    (h : LeafStageFits b t i 2) : Buf b.size :=
  leafStage2_words%

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The last DIF layer in place: words `2 k` and `2 k + 1`, without twiddles. -/
@[noinline, specialize]
def leafStage1 (p : ℕ) [Mont32Field p] (t : @& ByteArray) (i : USize) (b : ByteArray)
    (h : LeafStageFits b t i 0) : Buf b.size :=
  leafStage1_words%

/-- `count` groups of four blocks from word `i` through the stage kernel `k`, after one range
check. -/
@[specialize]
def leafStageLoop (K : Nat)
    (k : (t : ByteArray) → (i : USize) → (b : ByteArray) → LeafStageFits b t i K → Buf b.size)
    (t : @& ByteArray) : (count : Nat) → (i : USize) → (b : ByteArray) →
    4 * (i.toNat + 64 * count) ≤ b.size ∧ b.size < USize.size ∧ 4 * K ≤ t.size ∧
      t.size < USize.size → ByteArray
  | 0, _, b, _ => b
  | count + 1, i, b, h =>
    have h64 : (i + 64).toNat = i.toNat + 64 := by
      rw [usize_add_toNat _ _ (by rw [usize_numeral 64 (by decide)]; omega),
        usize_numeral 64 (by decide)]
    let b' := k t i b ⟨by omega, h.2.1, h.2.2⟩
    leafStageLoop K k t count (i + 64) b'.1 (by rw [b'.2, h64]; omega)

/-- The stage loop keeps the buffer size. -/
theorem size_leafStageLoop (K : Nat)
    (k : (t : ByteArray) → (i : USize) → (b : ByteArray) → LeafStageFits b t i K → Buf b.size)
    (t : ByteArray) : ∀ (count : Nat) (i : USize) (b : ByteArray) (h),
    (leafStageLoop K k t count i b h).size = b.size
  | 0, _, _, _ => rfl
  | count + 1, i, b, h => by
    rw [leafStageLoop, size_leafStageLoop K k t count, (k t i b _).2]

/-- `leaf16` on the blocks at words `0, 16, …, 16 * (blocks - 1)`: the four layers each in one pass
over the groups of four blocks, after one range check, then the remaining blocks one by one. -/
@[specialize]
def leaf16Blocks (p : ℕ) [Mont32Field p] (t3 t2 t1 : @& ByteArray) (blocks : Nat)
    (a : ByteArray) : ByteArray := Id.run do
  let mut a := a
  let n := blocks / 4
  if h : 4 * (64 * n) ≤ a.size ∧ a.size < USize.size ∧
      4 * 8 ≤ t3.size ∧ t3.size < USize.size ∧ 4 * 4 ≤ t2.size ∧ t2.size < USize.size ∧
      4 * 2 ≤ t1.size ∧ t1.size < USize.size then
    have h0 : (0 : USize).toNat = 0 := USize.toNat_zero
    let a8 := leafStageLoop 8 (leafStage8 p) t3 n 0 a (by omega)
    let a4 := leafStageLoop 4 (leafStage4 p) t2 n 0 a8 (by
      rw [size_leafStageLoop]; omega)
    let a2 := leafStageLoop 2 (leafStage2 p) t1 n 0 a4 (by
      rw [size_leafStageLoop, size_leafStageLoop]; omega)
    a := leafStageLoop 0 (leafStage1 p) t1 n 0 a2 (by
      rw [size_leafStageLoop, size_leafStageLoop, size_leafStageLoop]; omega)
  for block in [4 * n:blocks] do
    let i := 16 * block
    if h : 4 * (i + 15) + 3 < a.size ∧ a.size < USize.size ∧
        31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
        7 < t1.size ∧ t1.size < USize.size then
      a := leaf16 p t3 t2 t1 (USize.ofNatLT i (by omega)) a
        (by simpa only [USize.toNat_ofNatLT] using h)
  return a

/-- A complete `2 ^ m`-word leaf in DIF order, the natural order with bit-reversed indices: from
`2 ^ 4` words its last four layers run in place on sixteen-word blocks. -/
@[specialize]
def leafReversed (p : ℕ) [Mont32Field p] (tw : @& Array ByteArray) (m : Nat)
    (a : ByteArray) : ByteArray :=
  if 4 ≤ m then
    leaf16Blocks p (tw.getD 3 .empty) (tw.getD 2 .empty) (tw.getD 1 .empty) (2 ^ m / 16)
      (leafLayers p tw m (m / 2 - 2) a)
  else leafLayers p tw m (m / 2) a

end CompPoly.CPolynomial.NTTFast.Packed.Native
