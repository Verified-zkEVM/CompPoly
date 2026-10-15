/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Basic
import all CompPoly.Univariate.NTTFast.Plan
public import CompPoly.Univariate.NTTFast.Natural

/-! # Parallel natural-order transforms with independent array segments

Large transforms split the stages into a sequential prefix/suffix and independent
segments. Tasks own separate arrays; the refinement proofs use butterfly locality.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Plan
variable {R : Type*}

private theorem getD_append_left [Zero R] (a b : Array R) (i : Nat) (h : i < a.size) :
    (a ++ b).getD i 0 = a.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

private theorem getD_append_right [Zero R] (a b : Array R) (i : Nat) :
    (a ++ b).getD (a.size + i) 0 = b.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_append_right (xs := a) (ys := b) (i := a.size + i) (by omega)]
  simp only [Nat.add_sub_cancel_left]

private theorem setAppendLeft (a b : Array R) (i : Nat) (v : R) (h : i < a.size) :
    (a ++ b).set! i v = a.set! i v ++ b := by
  simp only [Array.set!, Array.setIfInBounds_append_left h]

private theorem setAppendRight (a b : Array R) (i : Nat) (v : R) :
    (a ++ b).set! (a.size + i) v = a ++ b.set! i v := by
  rw [Array.set!, Array.setIfInBounds_append_right (xs := a) (ys := b)
    (i := a.size + i) (by omega)]
  simp only [Nat.add_sub_cancel_left, Array.set!]

/-- Butterflies confined to the left array leave the right array unchanged. -/
theorem butterflyDIFRadix4Inner_append_left [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat)
    (a b : Array R)
    (ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
      i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size) :
    butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 (a ++ b) =
      butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 a ++ b := by
  conv_lhs => rw [butterflyDIFRadix4Inner.eq_def]
  conv_rhs => rw [butterflyDIFRadix4Inner.eq_def]
  split
  · rename_i hj
    have h0 : i0 < a.size := by omega
    have h1 : i1 < a.size := by omega
    have h2 : i2 < a.size := by omega
    have h3 : i3 < a.size := by omega
    simp only [getD_append_left a b i0 h0, getD_append_left a b i1 h1,
      getD_append_left a b i2 h2, getD_append_left a b i3 h3,
      setAppendLeft, Array.size_set!, h0, h1, h2, h3]
    exact butterflyDIFRadix4Inner_append_left th tl limit (j + 1) (i0 + 1) (i1 + 1)
      (i2 + 1) (i3 + 1) _ b (by simp only [Array.size_set!] at *; omega)
  · rfl
termination_by limit - j
decreasing_by omega

/-- Shifted butterfly indices operate only on the appended right array. -/
theorem butterflyDIFRadix4Inner_append_right [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat)
    (a b : Array R) :
    butterflyDIFRadix4Inner th tl limit j (a.size + i0) (a.size + i1)
      (a.size + i2) (a.size + i3) (a ++ b) =
      a ++ butterflyDIFRadix4Inner th tl limit j i0 i1 i2 i3 b := by
  conv_lhs => rw [butterflyDIFRadix4Inner.eq_def]
  conv_rhs => rw [butterflyDIFRadix4Inner.eq_def]
  split
  · simp only [getD_append_right, setAppendRight]
    simpa only [Nat.add_assoc] using
      butterflyDIFRadix4Inner_append_right th tl limit (j + 1) (i0 + 1) (i1 + 1)
        (i2 + 1) (i3 + 1) a _
  · rfl
termination_by limit - j
decreasing_by omega

/-- Butterflies confined to the left array leave the right array unchanged. -/
theorem butterflyDITRadix4Inner_append_left [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat)
    (a b : Array R)
    (ha : i0 + (limit - j) ≤ a.size ∧ i1 + (limit - j) ≤ a.size ∧
      i2 + (limit - j) ≤ a.size ∧ i3 + (limit - j) ≤ a.size) :
    butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 (a ++ b) =
      butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 a ++ b := by
  conv_lhs => rw [butterflyDITRadix4Inner.eq_def]
  conv_rhs => rw [butterflyDITRadix4Inner.eq_def]
  split
  · rename_i hj
    have h0 : i0 < a.size := by omega
    have h1 : i1 < a.size := by omega
    have h2 : i2 < a.size := by omega
    have h3 : i3 < a.size := by omega
    simp only [getD_append_left a b i0 h0, getD_append_left a b i1 h1,
      getD_append_left a b i2 h2, getD_append_left a b i3 h3,
      setAppendLeft, Array.size_set!, h0, h1, h2, h3]
    exact butterflyDITRadix4Inner_append_left th tl limit (j + 1) (i0 + 1) (i1 + 1)
      (i2 + 1) (i3 + 1) _ b (by simp only [Array.size_set!] at *; omega)
  · rfl
termination_by limit - j
decreasing_by omega

/-- Shifted butterfly indices operate only on the appended right array. -/
theorem butterflyDITRadix4Inner_append_right [Field R] (th tl : Array R) (limit j i0 i1 i2 i3 : Nat)
    (a b : Array R) :
    butterflyDITRadix4Inner tl th limit j (a.size + i0) (a.size + i1)
      (a.size + i2) (a.size + i3) (a ++ b) =
      a ++ butterflyDITRadix4Inner tl th limit j i0 i1 i2 i3 b := by
  conv_lhs => rw [butterflyDITRadix4Inner.eq_def]
  conv_rhs => rw [butterflyDITRadix4Inner.eq_def]
  split
  · simp only [getD_append_right, setAppendRight]
    simpa only [Nat.add_assoc] using
      butterflyDITRadix4Inner_append_right th tl limit (j + 1) (i0 + 1) (i1 + 1)
        (i2 + 1) (i3 + 1) a _
  · rfl
termination_by limit - j
decreasing_by omega

/-- Complete left-hand blocks leave an appended suffix unchanged. -/
theorem butterflyDIFRadix4Blocks_append_left [Field R] (th tl : Array R) (q blocks block : Nat)
    (a b : Array R) (ha : blocks * (4 * q) ≤ a.size) :
    butterflyDIFRadix4Blocks th tl (4 * q) q blocks block (a ++ b) =
      butterflyDIFRadix4Blocks th tl (4 * q) q blocks block a ++ b := by
  conv_lhs => rw [butterflyDIFRadix4Blocks.eq_def]
  conv_rhs => rw [butterflyDIFRadix4Blocks.eq_def]
  split
  · rename_i hb
    have hs : (block + 1) * (4 * q) ≤ a.size :=
      (Nat.mul_le_mul_right (4 * q) (by omega)).trans ha
    dsimp only
    rw [butterflyDIFRadix4Inner_append_left th tl q 0 (block * (4 * q)) (block * (4 * q) + q)
      (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) a b (by
      simp only [Nat.sub_zero]; rw [Nat.add_mul, Nat.one_mul] at hs; omega)]
    exact butterflyDIFRadix4Blocks_append_left th tl q blocks (block + 1) _ b
      (by simpa only [size_butterflyDIFRadix4Inner] using ha)
  · rfl
termination_by blocks - block
decreasing_by omega

/-- Offset block traversal agrees with traversal of the right-hand segment. -/
theorem butterflyDIFRadix4Blocks_append_right [Field R] (th tl : Array R)
    (q left blocks block : Nat)
    (a b : Array R) (ha : a.size = left * (4 * q)) :
    butterflyDIFRadix4Blocks th tl (4 * q) q (left + blocks) (left + block) (a ++ b) =
      a ++ butterflyDIFRadix4Blocks th tl (4 * q) q blocks block b := by
  conv_lhs => rw [butterflyDIFRadix4Blocks.eq_def]
  conv_rhs => rw [butterflyDIFRadix4Blocks.eq_def]
  simp only [Nat.add_lt_add_iff_left]
  split
  · have h0 : (left + block) * (4 * q) = a.size + block * (4 * q) := by
      rw [Nat.add_mul, ha]
    simp only [h0, Nat.add_assoc]
    rw [butterflyDIFRadix4Inner_append_right]
    simpa only [Nat.add_assoc] using butterflyDIFRadix4Blocks_append_right th tl q left blocks
      (block + 1) a _ ha
  · rfl
termination_by blocks - block
decreasing_by omega

private theorem butterflyDIFRadix4Blocks_split [Field R] (th tl : Array R) (q m n block : Nat)
    (a : Array R) (hb : block ≤ m) :
    butterflyDIFRadix4Blocks th tl (4 * q) q (m + n) block a =
      butterflyDIFRadix4Blocks th tl (4 * q) q (m + n) m
        (butterflyDIFRadix4Blocks th tl (4 * q) q m block a) := by
  by_cases h : block < m
  · conv_lhs => rw [butterflyDIFRadix4Blocks.eq_def]
    conv_rhs => rw [show butterflyDIFRadix4Blocks th tl (4 * q) q m block a = _ from
      butterflyDIFRadix4Blocks.eq_def ..]
    simp only [h, show block < m + n by omega, ↓reduceIte]
    exact butterflyDIFRadix4Blocks_split th tl q m n (block + 1) _ (by omega)
  · have he : block = m := by omega
    subst block
    conv_rhs => rw [show butterflyDIFRadix4Blocks th tl (4 * q) q m m a = _ from
      butterflyDIFRadix4Blocks.eq_def ..]
    simp only [Nat.lt_irrefl, ↓reduceIte]
termination_by m - block
decreasing_by omega

/-- Complete aligned blocks can be transformed independently. -/
theorem butterflyDIFRadix4Blocks_append [Field R] (th tl : Array R) (q m n : Nat) (a b : Array R)
    (ha : a.size = m * (4 * q)) :
    butterflyDIFRadix4Blocks th tl (4 * q) q (m + n) 0 (a ++ b) =
      butterflyDIFRadix4Blocks th tl (4 * q) q m 0 a ++
        butterflyDIFRadix4Blocks th tl (4 * q) q n 0 b := by
  rw [butterflyDIFRadix4Blocks_split th tl q m n 0 _ (by omega),
    butterflyDIFRadix4Blocks_append_left th tl q m 0 a b (by omega)]
  simpa only [Nat.add_zero] using
    butterflyDIFRadix4Blocks_append_right th tl q m n 0 _ b
      (by simpa only [size_butterflyDIFRadix4Blocks] using ha)

/-- Complete left-hand blocks leave an appended suffix unchanged. -/
theorem butterflyDITRadix4Blocks_append_left [Field R] (th tl : Array R) (q blocks block : Nat)
    (a b : Array R) (ha : blocks * (4 * q) ≤ a.size) :
    butterflyDITRadix4Blocks tl th (4 * q) q blocks block (a ++ b) =
      butterflyDITRadix4Blocks tl th (4 * q) q blocks block a ++ b := by
  conv_lhs => rw [butterflyDITRadix4Blocks.eq_def]
  conv_rhs => rw [butterflyDITRadix4Blocks.eq_def]
  split
  · rename_i hb
    have hs : (block + 1) * (4 * q) ≤ a.size :=
      (Nat.mul_le_mul_right (4 * q) (by omega)).trans ha
    dsimp only
    rw [butterflyDITRadix4Inner_append_left th tl q 0 (block * (4 * q)) (block * (4 * q) + q)
      (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) a b (by
      simp only [Nat.sub_zero]; rw [Nat.add_mul, Nat.one_mul] at hs; omega)]
    exact butterflyDITRadix4Blocks_append_left th tl q blocks (block + 1) _ b
      (by simpa only [size_butterflyDITRadix4Inner] using ha)
  · rfl
termination_by blocks - block
decreasing_by omega

/-- Offset block traversal agrees with traversal of the right-hand segment. -/
theorem butterflyDITRadix4Blocks_append_right [Field R] (th tl : Array R)
    (q left blocks block : Nat)
    (a b : Array R) (ha : a.size = left * (4 * q)) :
    butterflyDITRadix4Blocks tl th (4 * q) q (left + blocks) (left + block) (a ++ b) =
      a ++ butterflyDITRadix4Blocks tl th (4 * q) q blocks block b := by
  conv_lhs => rw [butterflyDITRadix4Blocks.eq_def]
  conv_rhs => rw [butterflyDITRadix4Blocks.eq_def]
  simp only [Nat.add_lt_add_iff_left]
  split
  · have h0 : (left + block) * (4 * q) = a.size + block * (4 * q) := by
      rw [Nat.add_mul, ha]
    simp only [h0, Nat.add_assoc]
    rw [butterflyDITRadix4Inner_append_right]
    simpa only [Nat.add_assoc] using butterflyDITRadix4Blocks_append_right th tl q left blocks
      (block + 1) a _ ha
  · rfl
termination_by blocks - block
decreasing_by omega

private theorem butterflyDITRadix4Blocks_split [Field R] (th tl : Array R) (q m n block : Nat)
    (a : Array R) (hb : block ≤ m) :
    butterflyDITRadix4Blocks tl th (4 * q) q (m + n) block a =
      butterflyDITRadix4Blocks tl th (4 * q) q (m + n) m
        (butterflyDITRadix4Blocks tl th (4 * q) q m block a) := by
  by_cases h : block < m
  · conv_lhs => rw [butterflyDITRadix4Blocks.eq_def]
    conv_rhs => rw [show butterflyDITRadix4Blocks tl th (4 * q) q m block a = _ from
      butterflyDITRadix4Blocks.eq_def ..]
    simp only [h, show block < m + n by omega, ↓reduceIte]
    exact butterflyDITRadix4Blocks_split th tl q m n (block + 1) _ (by omega)
  · have he : block = m := by omega
    subst block
    conv_rhs => rw [show butterflyDITRadix4Blocks tl th (4 * q) q m m a = _ from
      butterflyDITRadix4Blocks.eq_def ..]
    simp only [Nat.lt_irrefl, ↓reduceIte]
termination_by m - block
decreasing_by omega

/-- Complete aligned blocks can be transformed independently. -/
theorem butterflyDITRadix4Blocks_append [Field R] (th tl : Array R) (q m n : Nat) (a b : Array R)
    (ha : a.size = m * (4 * q)) :
    butterflyDITRadix4Blocks tl th (4 * q) q (m + n) 0 (a ++ b) =
      butterflyDITRadix4Blocks tl th (4 * q) q m 0 a ++
        butterflyDITRadix4Blocks tl th (4 * q) q n 0 b := by
  rw [butterflyDITRadix4Blocks_split th tl q m n 0 _ (by omega),
    butterflyDITRadix4Blocks_append_left th tl q m 0 a b (by omega)]
  simpa only [Nat.add_zero] using
    butterflyDITRadix4Blocks_append_right th tl q m n 0 _ b
      (by simpa only [size_butterflyDITRadix4Blocks] using ha)

end CompPoly.CPolynomial.NTTFast.Plan

namespace CompPoly.CPolynomial.NTTFast.Parallel
variable {R : Type*}

/-- Execute one planned radix-four pass on all complete blocks. -/
@[inline] def step [Field R] [DecidableEq R] (inverse : Bool) (tw : Array (Array R))
    (low : Nat) (a : Array R) : Array R :=
  let q := 2 ^ low
  if inverse then
    Plan.stageBlocksDIT (tw.getD (low + 1) #[]) (tw.getD low #[])
      (4 * q) q (a.size / (4 * q)) 0 a
  else
    Plan.stageBlocksDIF (tw.getD (low + 1) #[]) (tw.getD low #[])
      (4 * q) q (a.size / (4 * q)) 0 a

@[simp] theorem size_step [Field R] [DecidableEq R] (inverse : Bool)
    (tw : Array (Array R)) (low : Nat) (a : Array R) :
    (step inverse tw low a).size = a.size := by
  cases inverse <;> simp only [step, Bool.false_eq_true, ↓reduceIte,
    Plan.stageBlocksDIF_eq, Plan.checkedBlocks_eq,
    Plan.stageBlocksDIT_eq, Plan.checkedDITBlocks_eq,
    Plan.size_butterflyDIFRadix4Blocks, Plan.size_butterflyDITRadix4Blocks]

/-- Aligned segments have no butterfly dependencies across their boundary. -/
theorem step_append [Field R] [DecidableEq R] (inverse : Bool) (tw : Array (Array R))
    (low : Nat) (a b : Array R) (ha : 4 * 2 ^ low ∣ a.size)
    (hb : 4 * 2 ^ low ∣ b.size) :
    step inverse tw low (a ++ b) = step inverse tw low a ++ step inverse tw low b := by
  have hq : 0 < 4 * 2 ^ low := Nat.mul_pos (by omega) (Nat.two_pow_pos low)
  have hcount : (a.size + b.size) / (4 * 2 ^ low) =
      a.size / (4 * 2 ^ low) + b.size / (4 * 2 ^ low) := by
    rw [← Nat.div_mul_cancel ha, ← Nat.div_mul_cancel hb, ← Nat.add_mul,
      Nat.mul_div_cancel _ hq, Nat.mul_div_cancel _ hq, Nat.mul_div_cancel _ hq]
  cases inverse <;> simp only [step, Bool.false_eq_true, ↓reduceIte,
    Plan.stageBlocksDIF_eq, Plan.checkedBlocks_eq,
    Plan.stageBlocksDIT_eq, Plan.checkedDITBlocks_eq, Array.size_append, hcount]
  · exact Plan.butterflyDIFRadix4Blocks_append _ _ _ _ _ _ _ (Nat.div_mul_cancel ha).symm
  · exact Plan.butterflyDITRadix4Blocks_append _ _ _ _ _ _ _ (Nat.div_mul_cancel ha).symm

/-- Run a sequence of planned radix-four passes. -/
@[inline, specialize] def runPasses [Field R] [DecidableEq R] (inverse : Bool)
    (tw : Array (Array R)) (passes : List Nat) (a : Array R) : Array R :=
  passes.foldl (fun a low ↦ step inverse tw low a) a

@[simp] theorem size_runPasses [Field R] [DecidableEq R] (inverse : Bool)
    (tw : Array (Array R)) (passes : List Nat) (a : Array R) :
    (runPasses inverse tw passes a).size = a.size := by
  induction passes generalizing a with
  | nil => rfl
  | cons low rest ih =>
    change (runPasses inverse tw rest (step inverse tw low a)).size = a.size
    rw [ih, size_step]

/-- An aligned sequence of stages can run independently on each segment. -/
theorem runPasses_append [Field R] [DecidableEq R] (inverse : Bool) (tw : Array (Array R))
    (passes : List Nat) (a b : Array R)
    (h : ∀ low ∈ passes, 4 * 2 ^ low ∣ a.size ∧ 4 * 2 ^ low ∣ b.size) :
    runPasses inverse tw passes (a ++ b) =
      runPasses inverse tw passes a ++ runPasses inverse tw passes b := by
  induction passes generalizing a b with
  | nil => rfl
  | cons low rest ih =>
    have hl := h low (List.mem_cons_self ..)
    change runPasses inverse tw rest (step inverse tw low (a ++ b)) =
      runPasses inverse tw rest (step inverse tw low a) ++
        runPasses inverse tw rest (step inverse tw low b)
    rw [step_append inverse tw low a b hl.1 hl.2]
    apply ih
    intro k hk
    simpa only [size_step] using h k (List.mem_cons_of_mem _ hk)

end CompPoly.CPolynomial.NTTFast.Parallel

namespace CompPoly.CPolynomial.NTTFast.Parallel
variable {R : Type*}

/-- Descending fused passes for a forward transform. -/
def forwardPasses [Field R] (D : NTT.Domain R) : List Nat :=
  (List.range (D.logN / 2)).map (fun pass ↦ D.logN - 1 - 2 * pass - 1)

private theorem blockSize_eq (low : Nat) : 2 ^ (low + 2) = 4 * 2 ^ low := by
  rw [pow_add]
  omega

private theorem forwardPasses_eq [Field R] [DecidableEq R] (D : NTT.Domain R)
    (tw : Array (Array R)) (a : Array R) (ha : a.size = D.n) :
    runPasses false tw (forwardPasses D) a =
      (List.range (D.logN / 2)).foldl (fun a pass ↦
        let high := D.logN - 1 - 2 * pass
        let low := high - 1
        Plan.stageBlocksDIF (tw.getD high #[]) (tw.getD low #[])
          (2 ^ (low + 2)) (2 ^ low) (D.n / (2 ^ (low + 2))) 0 a) a := by
  simp only [runPasses, forwardPasses, List.foldl_map]
  apply Plan.foldl_range_congr_inv (p := fun b : Array R ↦ b.size = D.n)
  · intro pass hp b hb
    have hhigh : (D.logN - 1 - 2 * pass - 1) + 1 = D.logN - 1 - 2 * pass := by omega
    simp only [step, Bool.false_eq_true, ↓reduceIte, hb, hhigh, blockSize_eq]
  · intro pass hp b hb
    simpa only [size_step] using hb
  · exact ha

/-- Splitting forward passes retains the checked stage loop, including odd logs. -/
theorem forwardStages_eq [Field R] [DecidableEq R] (D : NTT.Domain R)
    (tw : Array (Array R)) (a : Array R) (ha : a.size = D.n) :
    (if D.logN % 2 = 1 then
      Plan.butterflyStageDIFWithTwiddles D 0 (tw.getD 0 #[])
        (runPasses false tw (forwardPasses D) a)
    else runPasses false tw (forwardPasses D) a) = Plan.checkedStages D tw a := by
  rw [forwardPasses_eq D tw a ha]
  by_cases h : D.logN % 2 = 1 <;> simp [Plan.checkedStages, List.range_eq_range', h]

end CompPoly.CPolynomial.NTTFast.Parallel
