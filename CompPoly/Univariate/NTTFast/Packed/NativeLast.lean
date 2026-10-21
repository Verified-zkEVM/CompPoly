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
  lastHalf_words%

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

/-- `blocks` radix-four blocks of quarter `q`, the first at word `0`. -/
@[specialize]
def radix4Blocks (p : ℕ) [Mont32Field p] (th tl : @& ByteArray) (q blocks : Nat)
    (a : ByteArray) : ByteArray := Id.run do
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

end CompPoly.CPolynomial.NTTFast.Packed.Native
