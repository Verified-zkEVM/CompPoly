/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Radix4DIF
public import CompPoly.Univariate.NTTFast.Packed.KernelCorrectness

/-! # Local layer independence and global stage fusion -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- A consecutive group of ordinary radix-two butterfly blocks, at an explicit offset. -/
def localLayer [Field R] (tw : Array R) (half blocks base : Nat) (a : Array R) : Array R :=
  (List.range blocks).foldl (fun b block ↦
    Plan.butterflyDIFInner tw half 0 (base + block * (2 * half))
      (base + block * (2 * half) + half) b) a

/-- Nonoverlapping local layers can be scheduled in either order. -/
theorem localLayer_comm [Field R] (ta tb : Array R) (ha na ba hb nb bb : Nat)
    (hha : 0 < ha) (hhb : 0 < hb) (hsep : bb + nb * (2 * hb) ≤ ba) (a : Array R) :
    localLayer ta ha na ba (localLayer tb hb nb bb a) =
      localLayer tb hb nb bb (localLayer ta ha na ba a) := by
  unfold localLayer
  apply Plan.foldl_commute_foldl
  intro i j hi hj x
  symm
  apply Plan.butterflyDIFInner_comm
  intro k hk l hl
  have hib : i * (2 * ha) + 2 * ha ≤ na * (2 * ha) := by nlinarith
  have hjb : j * (2 * hb) + 2 * hb ≤ nb * (2 * hb) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The unrolled half-width-eight leaf layer is one ordinary offset block. -/
theorem layer16_8_eq_localLayer [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    layer16_8 tw a base = localLayer tw 8 1 base a := by rfl

/-- The unrolled half-width-four leaf layer is two ordinary offset blocks. -/
theorem layer16_4_eq_localLayer [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    layer16_4 tw a base = localLayer tw 4 2 base a := by rfl

/-- The unrolled half-width-two leaf layer is four ordinary offset blocks. -/
theorem layer16_2_eq_localLayer [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    layer16_2 tw a base = localLayer tw 2 4 base a := by rfl

/-- The unrolled half-width-one leaf layer is eight ordinary offset blocks. -/
theorem layer16_1_eq_localLayer [Field R] (tw : Array R) (a : Array R) (base : Nat) :
    layer16_1 tw a base = localLayer tw 1 8 base a := by rfl

/-- Consecutive groups of indexed operations traverse the same full interval. -/
theorem foldl_range_groups (f : α → Nat → α) (count blocks : Nat) (a : α) :
    (List.range blocks).foldl (fun b block ↦
      (List.range count).foldl (fun c k ↦ f c (count * block + k)) b) a =
      (List.range (count * blocks)).foldl f a := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    symm
    rw [Nat.mul_succ, List.range_eq_range', Plan.foldl_range'_append_split,
      Nat.zero_add, ← List.range_eq_range']
    exact Plan.foldl_range'_eq_range_add (fun k b ↦ f b k) _ _ _

/-- Traversing local layers in consecutive sixteen-coordinate blocks is one global stage. -/
theorem fold_localLayer [Field R] (tw : Array R) (half count blocks : Nat)
    (hw : count * (2 * half) = 16) (a : Array R) :
    (List.range blocks).foldl (fun b block ↦ localLayer tw half count (block * 16) b) a =
      Plan.butterflyDIFBlocks tw (2 * half) half (count * blocks) 0 a := by
  unfold localLayer
  have hindex (block k : Nat) : block * 16 + k * (2 * half) =
      (count * block + k) * (2 * half) := by rw [← hw]; ring
  simp_rw [hindex]
  rw [foldl_range_groups (fun b k ↦ Plan.butterflyDIFInner tw half 0
    (k * (2 * half)) (k * (2 * half) + half) b) count blocks a]
  symm
  simpa only [← List.range_eq_range'] using
    Plan.butterflyDIFBlocks_eq_foldl_inner tw (2 * half) half (count * blocks)
      (count * blocks) 0 a (by omega)

/-- Interleaving all four local final layers is equivalent to four whole-array stages. -/
theorem fold_leaf16Stages [Field R] (t3 t2 t1 : Array R) (blocks : Nat) (a : Array R) :
    (List.range blocks).foldl (fun b block ↦
      Expressions.leaf16Stages t3 t2 t1 b (block * 16)) a =
      Plan.butterflyDIFBlocks #[1] 2 1 (8 * blocks) 0
        (Plan.butterflyDIFBlocks t1 4 2 (4 * blocks) 0
          (Plan.butterflyDIFBlocks t2 8 4 (2 * blocks) 0
            (Plan.butterflyDIFBlocks t3 16 8 blocks 0 a))) := by
  simp only [Expressions.leaf16Stages, layer16_1_eq_localLayer, layer16_2_eq_localLayer,
    layer16_4_eq_localLayer, layer16_8_eq_localLayer]
  rw [Plan.foldl_quad]
  · rw [fold_localLayer _ 8 1 _ (by decide), fold_localLayer _ 4 2 _ (by decide),
      fold_localLayer _ 2 4 _ (by decide), fold_localLayer _ 1 8 _ (by decide)]
    simp only [Nat.one_mul]
  all_goals
    intro i j hij hj x
    apply localLayer_comm <;> (first | decide | omega)

end CompPoly.CPolynomial.NTTFast.Packed
