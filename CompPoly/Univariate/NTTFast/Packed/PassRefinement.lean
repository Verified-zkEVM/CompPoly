/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Radix4DIF
public import CompPoly.Univariate.NTTFast.Packed.LoopRefinement
public import CompPoly.Univariate.NTTFast.Packed.Folds

/-! # Packed radix-four pass refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode)

/-- All vectorized blocks of one pass agree with the ordinary radix-four block loop. -/
theorem Native.fold_inner16_encode (th tl : Array (FastField p))
    (q blocks : Nat) (a : Array (FastField p))
    (ha : (encode a).size < USize.size)
    (hth : (encode th).size < USize.size) (htl : (encode tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size)
    (hbound : blocks * (4 * q) ≤ a.size) :
    (List.range blocks).foldl (fun acc block ↦
      Native.inner16 p (encode th) (encode tl) q 0 (block * (4 * q))
        (block * (4 * q) + q) (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) acc)
      (encode a) =
      encode (Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks 0 a) := by
  rw [Plan.butterflyDIFRadix4Blocks_eq_foldl_inner th tl (4 * q) q blocks blocks 0 a (by omega),
    ← List.range_eq_range']
  apply foldl_encode (List.range blocks) (fun b ↦ b.size = a.size)
  · intro block hb b hbs
    have hb' : block < blocks := List.mem_range.mp hb
    have hbase : block * (4 * q) + 4 * q ≤ a.size := by
      calc
        _ = (block + 1) * (4 * q) := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ blocks * (4 * q) := Nat.mul_le_mul_right (4 * q) (by omega)
        _ ≤ a.size := hbound
    exact Native.inner16_encode th tl q 0 _ _ _ _ b
      (by simpa only [size_encode_fields, hbs] using ha) hth htl hthi htli
      (by omega) (by omega) (by omega) (by omega)
  · intro block hb b hbs
    simpa only [Plan.size_butterflyDIFRadix4Inner] using hbs
  · rfl

/-- The checked block loop depends only on the buffer's value. -/
theorem Native.blocks16Loop_congr {th tl : ByteArray} {n : Nat} {q : USize} {count : Nat}
    {base : USize} {b b' : ByteArray} (h) (e : b = b') :
    Native.blocks16Loop p th tl n q count base b h =
      Native.blocks16Loop p th tl n q count base b' (e ▸ h) := by
  subst e
  rfl

/-- The block loop checked once runs the ordinary radix-four blocks `block, …`. -/
theorem Native.blocks16Loop_encode (th tl : Array (FastField p)) (n : Nat) (q : USize)
    (hq : 16 * n = q.toNat) : ∀ (count block : Nat) (base : USize) (a : Array (FastField p)) (h),
    base.toNat = block * (4 * q.toNat) →
    Native.blocks16Loop p (encode th) (encode tl) n q count base (encode a) h =
      encode ((List.range' block count).foldl (fun acc blk ↦
        Plan.butterflyDIFRadix4Inner th tl q.toNat 0 (blk * (4 * q.toNat))
          (blk * (4 * q.toNat) + q.toNat) (blk * (4 * q.toNat) + 2 * q.toNat)
          (blk * (4 * q.toNat) + 3 * q.toNat) acc) a) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _; rfl
  | succ count ih =>
    intro block base a h hb
    have ha := h.1
    have hs := h.2.2.2.2.1
    rw [size_encode_fields] at ha hs
    have hc : 4 * q.toNat ≤ 4 * q.toNat * (count + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h1 : (base + q).toNat = base.toNat + q.toNat :=
      Native.usize_add_toNat _ _ (by omega)
    have hm (k : Nat) (hk : k ≤ 4) : (OfNat.ofNat k * q : USize).toNat = k * q.toNat :=
      Native.usize_mul_toNat k q (by omega) (by
        have := Nat.mul_le_mul_right q.toNat hk; omega)
    have h2 : (base + 2 * q).toNat = base.toNat + 2 * q.toNat := by
      rw [Native.usize_add_toNat _ _ (by rw [hm 2 (by decide)]; omega), hm 2 (by decide)]
    have h3 : (base + 3 * q).toNat = base.toNat + 3 * q.toNat := by
      rw [Native.usize_add_toNat _ _ (by rw [hm 3 (by decide)]; omega), hm 3 (by decide)]
    have h4 : (base + 4 * q).toNat = base.toNat + 4 * q.toNat := by
      rw [Native.usize_add_toNat _ _ (by rw [hm 4 (by decide)]; omega), hm 4 (by decide)]
    rw [Native.blocks16Loop, Native.blocks16Loop_congr _ (Native.inner16Loop_encode th tl q.toNat
      n 0 q base (base + q) (base + 2 * q) (base + 3 * q) a _
      (by rw [USize.toNat_zero, Nat.zero_add]) (by rw [h3]; omega) (by rw [h1]; omega)
      (by rw [h1, h2]; omega) (by rw [h2, h3]; omega))]
    rw [ih (block + 1) _ _ _ (by rw [h4, hb, Nat.add_mul, Nat.one_mul])]
    rw [List.range'_succ, List.foldl_cons, butterflyDIFRadix4Inner_eq_quadCells, Nat.sub_zero,
      USize.toNat_zero, h1, h2, h3, hb, hq]

/-- The block loop checked once runs a whole radix-four pass. -/
theorem Native.blocks16Loop_encode_pass (th tl : Array (FastField p)) (n : Nat) (q : USize)
    (hq : 16 * n = q.toNat) (blocks : Nat) (a : Array (FastField p)) (h) :
    Native.blocks16Loop p (encode th) (encode tl) n q blocks 0 (encode a) h =
      encode (Plan.butterflyDIFRadix4Blocks th tl (4 * q.toNat) q.toNat blocks 0 a) := by
  rw [Native.blocks16Loop_encode th tl n q hq blocks 0 0 a h (by rw [USize.toNat_zero,
    Nat.zero_mul]), Plan.butterflyDIFRadix4Blocks_eq_foldl_inner th tl (4 * q.toNat) q.toNat
    blocks blocks 0 a (by omega)]

end CompPoly.CPolynomial.NTTFast.Packed
