/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Data.Nat.Bitwise

/-!
# Forward NTT

This file provides spec-level forward NTT definitions together with an
iterative radix-2 implementation.
-/

open scoped BigOperators

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Forward

variable {R : Type*} [Field R]

private theorem foldl_range_eq_rec {α : Type*} (f : Nat → α → α) (x : α) :
    ∀ n : Nat,
      List.foldl (fun acc i => f i acc) x (List.range n) = Nat.rec x (fun i acc => f i acc) n
  | 0 => by simp
  | n + 1 => by
      simp [List.range_succ, List.foldl_append, foldl_range_eq_rec f x n]

private theorem foldl_range_eq_rec_fst {α β : Type*}
    (f : Nat → α × β → α × β) (x : α × β) (n : Nat) :
    (List.foldl (fun acc i => f i acc) x (List.range n)).1 =
      (Nat.rec (motive := fun _ => α × β) x (fun i acc => f i acc) n).1 := by
  simpa using congrArg Prod.fst
    (show List.foldl (fun acc i => f i acc) x (List.range n) =
        Nat.rec (motive := fun _ => α × β) x (fun i acc => f i acc) n from
      foldl_range_eq_rec f x n)

/-- DFT/NTT formula at one output index. -/
@[inline] def nttAt (D : Domain R) (a : Array R) (k : D.Idx) : R :=
  ∑ j : D.Idx, a.getD j.1 0 * D.omega ^ ((k : Nat) * (j : Nat))

/-- Full forward transform specified directly from the NTT formula. -/
@[inline] def forwardSpec (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun k : D.Idx => nttAt D a k)

/-- Reverse the lowest `bits` bits of `i`. -/
def bitRevNat : Nat → Nat → Nat
  | 0, _ => 0
  | bits + 1, i => ((i &&& 1) <<< bits) ||| bitRevNat bits (i >>> 1)

private theorem bitRevNat_lt (bits i : Nat) : bitRevNat bits i < 2 ^ bits := by
  induction bits generalizing i with
  | zero =>
      simp [bitRevNat]
  | succ bits ih =>
      rw [bitRevNat]
      apply Nat.append_lt
      · exact ih (i >>> 1)
      · rw [Nat.and_one_is_mod]
        exact Nat.mod_lt _ (by decide : 0 < 2)

private theorem bitRevNat_even (bits b : Nat) :
    bitRevNat (bits + 1) (2 * b) = bitRevNat bits b := by
  simp [bitRevNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

private theorem bitRevNat_odd_or (bits b : Nat) :
    bitRevNat (bits + 1) (2 * b + 1) = (1 <<< bits) ||| bitRevNat bits b := by
  rw [bitRevNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 * b + 1) / 2 = b := by
    have h2 : 0 < 2 := by decide
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.add_mul_div_right 1 b (H := h2))
  rw [hdiv]
  simp

private theorem bitRevNat_odd (bits b : Nat) :
    bitRevNat (bits + 1) (2 * b + 1) = 2 ^ bits + bitRevNat bits b := by
  rw [bitRevNat_odd_or]
  have hlt : bitRevNat bits b < 2 ^ bits := bitRevNat_lt bits b
  have hand : 2 ^ bits &&& bitRevNat bits b = 0 := by
    simpa [Nat.shiftLeft_eq] using
      (Nat.and_shl_eq_zero_of_lt_two_pow (a := 1) (n := bits) (b := bitRevNat bits b) hlt)
  rw [Nat.shiftLeft_eq, one_mul]
  exact (Nat.sum_of_and_eq_zero_is_or hand).symm

/-- Apply bit-reversal permutation to an evaluation array. -/
def bitRevPermute (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD (bitRevNat D.logN i.1) 0)

private def butterflyInnerStep
    (blockSize half : Nat) (wm : R) (block j : Nat) (st : Array R × R) : Array R × R :=
  let acc := st.1
  let w := st.2
  let i0 := block * blockSize + j
  let i1 := i0 + half
  let u := acc.getD i0 0
  let t := w * acc.getD i1 0
  (((acc.set! i0 (u + t)).set! i1 (u - t)), w * wm)

private def butterflyBlockStep
    (blockSize half : Nat) (wm : R) (block : Nat) (acc : Array R) : Array R :=
  (Nat.rec (motive := fun _ => Array R × R)
    (acc, (1 : R))
    (fun j st => butterflyInnerStep blockSize half wm block j st)
    half).1

/-- One butterfly stage of the iterative radix-2 transform. -/
def butterflyStage (D : Domain R) (stage : Nat) (a : Array R) : Array R := Id.run do
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  let mut acc := a
  for block in [0:D.n / blockSize] do
    let mut st : Array R × R := (acc, (1 : R))
    for j in [0:half] do
      st := butterflyInnerStep blockSize half wm block j st
    acc := st.1
  return acc

/--
Pure structural-recursive specification of one butterfly stage.

This matches the imperative control flow of `butterflyStage`, but replaces the
`for` loops with explicit `Nat.rec` recursors.
-/
def butterflyStageSpec (D : Domain R) (stage : Nat) (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  Nat.rec (motive := fun _ => Array R)
    a
    (fun block acc => butterflyBlockStep blockSize half wm block acc)
    (D.n / blockSize)

/--
The imperative butterfly loop agrees with the pure pointwise butterfly stage
specification.

This is where the local `set!` bookkeeping for one stage belongs.
-/
theorem butterflyStage_eq_butterflyStageSpec
    (D : Domain R) (stage : Nat) (a : Array R) (ha : a.size = D.n) :
    butterflyStage D stage a = butterflyStageSpec D stage a := by
  have _ := ha
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  have hinner :
      ∀ block acc,
        (List.foldl
          (fun st j => butterflyInnerStep blockSize half wm block j st)
          (acc, (1 : R)) (List.range half)).1 =
          (Nat.rec (motive := fun _ => Array R × R)
            (acc, (1 : R))
            (fun j st => butterflyInnerStep blockSize half wm block j st)
            half).1 := by
    intro block acc
    exact foldl_range_eq_rec_fst
      (f := fun j st => butterflyInnerStep blockSize half wm block j st)
      (x := (acc, (1 : R))) half
  have hstep :
      (fun acc block =>
        (List.foldl
          (fun st j =>
            butterflyInnerStep
              (2 ^ (stage + 1))
              (2 ^ stage)
              (D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1)))
              block j st)
          (acc, (1 : R)) (List.range' 0 (2 ^ stage))).1) =
        fun acc block =>
          butterflyBlockStep
            (2 ^ (stage + 1))
            (2 ^ stage)
            (D.omega ^ (2 ^ D.logN / 2 ^ (stage + 1)))
            block acc := by
    funext acc block
    simpa [blockSize, half, wm, List.range_eq_range', butterflyInnerStep, butterflyBlockStep]
      using hinner block acc
  simp [butterflyStage, butterflyStageSpec]
  rw [hstep]
  simpa [List.range_eq_range', butterflyBlockStep, butterflyInnerStep, blockSize, half, wm] using
    foldl_range_eq_rec
    (f := fun block acc => butterflyBlockStep blockSize half wm block acc)
    (x := a) (D.n / blockSize)

@[simp] private theorem size_butterflyInnerStep
    (blockSize half : Nat) (wm : R) (block j : Nat) (st : Array R × R) :
    (butterflyInnerStep blockSize half wm block j st).1.size = st.1.size := by
  simp [butterflyInnerStep]

private theorem size_butterflyBlockStep_aux
    (blockSize half : Nat) (wm : R) (block : Nat) :
    ∀ n : Nat, ∀ acc : Array R,
      (Nat.rec (motive := fun _ => Array R × R)
        (acc, (1 : R))
        (fun j st => butterflyInnerStep blockSize half wm block j st)
        n).1.size = acc.size
  | 0, acc => by simp
  | n + 1, acc => by
      simp [size_butterflyBlockStep_aux blockSize half wm block n acc]

@[simp] private theorem size_butterflyBlockStep
    (blockSize half : Nat) (wm : R) (block : Nat) (acc : Array R) :
    (butterflyBlockStep blockSize half wm block acc).size = acc.size := by
  simp [butterflyBlockStep, size_butterflyBlockStep_aux]

private theorem size_butterflyStageSpec_aux
    (blockSize half : Nat) (wm : R) :
    ∀ n : Nat, ∀ acc : Array R,
      (Nat.rec (motive := fun _ => Array R)
        acc
        (fun block acc => butterflyBlockStep blockSize half wm block acc)
        n).size = acc.size
  | 0, acc => by simp
  | n + 1, acc => by
      simp [size_butterflyStageSpec_aux blockSize half wm n acc]

theorem size_butterflyStageSpec (D : Domain R) (stage : Nat) (a : Array R) (ha : a.size = D.n) :
    (butterflyStageSpec D stage a).size = D.n := by
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  rw [show (butterflyStageSpec D stage a).size = a.size by
    simp [butterflyStageSpec, size_butterflyStageSpec_aux]]
  exact ha

theorem size_butterflyStage (D : Domain R) (stage : Nat) (a : Array R) (ha : a.size = D.n) :
    (butterflyStage D stage a).size = D.n := by
  rw [butterflyStage_eq_butterflyStageSpec D stage a ha]
  exact size_butterflyStageSpec D stage a ha

/-- Run all radix-2 butterfly stages (complexity: `O(n log n)`). -/
def runStages (D : Domain R) (a : Array R) : Array R := Id.run do
  let mut acc := a
  for stage in [0:D.logN] do
    acc := butterflyStage D stage acc
  return acc

/--
Proof-oriented stagewise specification for the forward transform.

`forwardStageSpec D completed a` means: start from the bit-reversed input `a`,
then apply exactly the first `completed` radix-2 butterfly stages.
-/
def forwardStageSpec (D : Domain R) (completed : Nat) (a : Array R) : Array R :=
  Nat.rec (bitRevPermute D a) (fun stage acc => butterflyStage D stage acc) completed

/--
Stagewise pure specification built from `butterflyStageSpec`.

This removes the mutable-array implementation details but still mirrors the
radix-2 control flow exactly.
-/
def forwardStagePureSpec (D : Domain R) (completed : Nat) (a : Array R) : Array R :=
  Nat.rec (bitRevPermute D a) (fun stage acc => butterflyStageSpec D stage acc) completed

/--
Mathematical partial-DFT state after `completed` radix-2 stages.

Each contiguous block of size `2^completed` has already been transformed, while
the remaining `D.logN - completed` bits are still encoded by bit-reversed block
selection.
-/
def forwardMathStageSpec (D : Domain R) (completed : Nat) (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ completed
  let stride : Nat := 2 ^ (D.logN - completed)
  Array.ofFn (fun i : D.Idx =>
    let block := i.1 / blockSize
    let offset := i.1 % blockSize
    ∑ t : Fin blockSize,
      a.getD (bitRevNat (D.logN - completed) block + t.1 * stride) 0 *
        D.omega ^ (offset * t.1 * stride))

private def forwardMathValueAt (D : Domain R) (completed : Nat) (a : Array R) (idx : Nat) : R :=
  let blockSize : Nat := 2 ^ completed
  let stride : Nat := 2 ^ (D.logN - completed)
  let block := idx / blockSize
  let offset := idx % blockSize
  ∑ t : Fin blockSize,
    a.getD (bitRevNat (D.logN - completed) block + t.1 * stride) 0 *
      D.omega ^ (offset * t.1 * stride)

private def stageTwiddle (D : Domain R) (stage : Nat) : R :=
  D.omega ^ (D.n / 2 ^ (stage + 1))

/--
Outer stage invariant: after `doneBlocks` many length-`2^(stage+1)` blocks have
been processed, those blocks already satisfy the stage-`stage+1` math spec,
while the remaining blocks still satisfy the stage-`stage` math spec.
-/
private def forwardMathBlocksSpec
    (D : Domain R) (stage doneBlocks : Nat) (a : Array R) : Array R :=
  let blockSize : Nat := 2 ^ (stage + 1)
  Array.ofFn (fun i : D.Idx =>
    if i.1 / blockSize < doneBlocks then
      forwardMathValueAt D (stage + 1) a i.1
    else
      forwardMathValueAt D stage a i.1)

/--
Inner stage invariant inside one length-`2^(stage+1)` block: previous blocks
are already upgraded to the stage-`stage+1` math spec, while inside the current
block the first `donePairs` butterfly pairs have been upgraded and the rest are
still at the stage-`stage` math spec.
-/
private def forwardMathPairsSpec
    (D : Domain R) (stage block donePairs : Nat) (a : Array R) : Array R :=
  let half : Nat := 2 ^ stage
  let blockSize : Nat := 2 ^ (stage + 1)
  Array.ofFn (fun i : D.Idx =>
    let bigBlock := i.1 / blockSize
    let pair := i.1 % half
    if bigBlock < block then
      forwardMathValueAt D (stage + 1) a i.1
    else if bigBlock = block then
      if pair < donePairs then
        forwardMathValueAt D (stage + 1) a i.1
      else
        forwardMathValueAt D stage a i.1
    else
      forwardMathValueAt D stage a i.1)

@[simp] theorem forwardStageSpec_zero (D : Domain R) (a : Array R) :
    forwardStageSpec D 0 a = bitRevPermute D a := rfl

@[simp] theorem forwardStageSpec_succ (D : Domain R) (stage : Nat) (a : Array R) :
    forwardStageSpec D (stage + 1) a =
      butterflyStage D stage (forwardStageSpec D stage a) := rfl

@[simp] theorem forwardStagePureSpec_zero (D : Domain R) (a : Array R) :
    forwardStagePureSpec D 0 a = bitRevPermute D a := rfl

@[simp] theorem forwardStagePureSpec_succ (D : Domain R) (stage : Nat) (a : Array R) :
    forwardStagePureSpec D (stage + 1) a =
      butterflyStageSpec D stage (forwardStagePureSpec D stage a) := rfl

@[simp] theorem size_forwardStageSpec (D : Domain R) (completed : Nat) (a : Array R) :
    (forwardStageSpec D completed a).size = D.n := by
  induction completed with
  | zero =>
      simp [forwardStageSpec, bitRevPermute]
  | succ completed ih =>
      rw [forwardStageSpec_succ]
      exact size_butterflyStage D completed (forwardStageSpec D completed a) ih

@[simp] theorem size_forwardStagePureSpec (D : Domain R) (completed : Nat) (a : Array R) :
    (forwardStagePureSpec D completed a).size = D.n := by
  induction completed with
  | zero =>
      simp [forwardStagePureSpec, bitRevPermute]
  | succ completed ih =>
      rw [forwardStagePureSpec_succ]
      exact size_butterflyStageSpec D completed (forwardStagePureSpec D completed a) ih

/--
The algorithmic stage recursion agrees with the pure stage recursion.

This is the global bookkeeping bridge from the recursive algorithmic stages to
their pointwise closed-form counterparts.
-/
theorem forwardStageSpec_eq_forwardStagePureSpec (D : Domain R) (a : Array R) :
    ∀ completed : Nat, forwardStageSpec D completed a = forwardStagePureSpec D completed a := by
  intro completed
  induction completed with
  | zero =>
      simp
  | succ completed ih =>
      rw [forwardStageSpec_succ, forwardStagePureSpec_succ, ih]
      rw [butterflyStage_eq_butterflyStageSpec D completed (forwardStagePureSpec D completed a)]
      exact size_forwardStagePureSpec D completed a

/--
Base case of the mathematical stage invariant: before any butterflies, the
state is exactly the bit-reversed input.
-/
theorem forwardMathStageSpec_zero (D : Domain R) (a : Array R) :
    forwardMathStageSpec D 0 a = bitRevPermute D a := by
  apply Array.ext
  · simp [forwardMathStageSpec, bitRevPermute]
  · intro i hi₁ hi₂
    simp [forwardMathStageSpec, bitRevPermute]

private theorem forwardMathBlocksSpec_zero
    (D : Domain R) (stage : Nat) (a : Array R) :
    forwardMathBlocksSpec D stage 0 a = forwardMathStageSpec D stage a := by
  apply Array.ext
  · simp [forwardMathBlocksSpec, forwardMathStageSpec]
  · intro i hi₁ hi₂
    simp [forwardMathBlocksSpec, forwardMathStageSpec, forwardMathValueAt]

private theorem forwardMathPairsSpec_zero
    (D : Domain R) (stage block : Nat) (a : Array R) :
    forwardMathPairsSpec D stage block 0 a = forwardMathBlocksSpec D stage block a := by
  apply Array.ext
  · simp [forwardMathPairsSpec, forwardMathBlocksSpec]
  · intro i hi₁ hi₂
    simp [forwardMathPairsSpec, forwardMathBlocksSpec, forwardMathValueAt]

private theorem forwardMathPairsSpec_half
    (D : Domain R) (stage block : Nat) (a : Array R) :
    forwardMathPairsSpec D stage block (2 ^ stage) a =
      forwardMathBlocksSpec D stage (block + 1) a := by
  apply Array.ext
  · simp [forwardMathPairsSpec, forwardMathBlocksSpec]
  · intro i hi₁ hi₂
    let bb : Nat := i / 2 ^ (stage + 1)
    let v1 : R := forwardMathValueAt D (stage + 1) a i
    let v0 : R := forwardMathValueAt D stage a i
    have hpair : i % 2 ^ stage < 2 ^ stage := by
      exact Nat.mod_lt _ (pow_pos (by norm_num) _)
    have hcase :
        (if bb < block then
          v1
        else if bb = block then
          if i % 2 ^ stage < 2 ^ stage then v1 else v0
        else
          v0)
          = (if bb < block + 1 then v1 else v0) := by
      by_cases hlt : bb < block
      · have hlt' : bb < block + 1 := Nat.lt_trans hlt (Nat.lt_succ_self _)
        rw [if_pos hlt, if_pos hlt']
      · by_cases hEq : bb = block
        · have hlt' : bb < block + 1 := by
            simp [hEq]
          rw [if_neg hlt, if_pos hEq, if_pos hpair, if_pos hlt']
        · have hnot : ¬ bb < block + 1 := by
            exact not_lt_of_ge
              (Nat.succ_le_of_lt
                (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hEq)))
          rw [if_neg hlt, if_neg hEq, if_neg hnot]
    simpa [forwardMathPairsSpec, forwardMathBlocksSpec, forwardMathValueAt, bb, v1, v0]
      using hcase

private theorem forwardMathBlocksSpec_final
    (D : Domain R) (stage : Nat) (a : Array R) (hstage : stage < D.logN) :
    forwardMathBlocksSpec D stage (D.n / 2 ^ (stage + 1)) a =
      forwardMathStageSpec D (stage + 1) a := by
  apply Array.ext
  · simp [forwardMathBlocksSpec, forwardMathStageSpec]
  · intro i hi₁ hi₂
    let blockSize : Nat := 2 ^ (stage + 1)
    let bb : Nat := i / blockSize
    let v1 : R := forwardMathValueAt D (stage + 1) a i
    let v0 : R := forwardMathValueAt D stage a i
    have hi : i < D.n := by
      simpa [forwardMathStageSpec] using hi₂
    have hle : stage + 1 ≤ D.logN := Nat.succ_le_of_lt hstage
    have hdiv : blockSize ∣ D.n := by
      dsimp [blockSize]
      simpa [Domain.n] using Nat.pow_dvd_pow 2 hle
    have hmul : (D.n / blockSize) * blockSize = D.n := by
      exact Nat.div_mul_cancel hdiv
    have hmul' : blockSize * (D.n / blockSize) = D.n := by
      rw [Nat.mul_comm, hmul]
    have hmul'' : blockSize * (2 ^ D.logN / blockSize) = 2 ^ D.logN := by
      simpa [Domain.n] using hmul'
    have hiPow : i < 2 ^ D.logN := by
      simpa [Domain.n] using hi
    have hiPow' : i < blockSize * (2 ^ D.logN / blockSize) := by
      rw [hmul'']
      exact hiPow
    have hi' : i < blockSize * (D.n / blockSize) := by
      simpa [Domain.n] using hiPow'
    have hblock : bb < D.n / blockSize := by
      dsimp [bb]
      exact Nat.div_lt_of_lt_mul hi'
    have hcase : (if bb < D.n / blockSize then v1 else v0) = v1 := by
      rw [if_pos hblock]
    simpa [forwardMathBlocksSpec, forwardMathStageSpec, forwardMathValueAt, blockSize, bb, v1, v0]
      using hcase

private theorem butterfly_lower_div_block (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) / 2 ^ (stage + 1) = block := by
  rw [Nat.mul_comm block (2 ^ (stage + 1))]
  rw [Nat.mul_add_div (Nat.two_pow_pos (stage + 1))]
  have hlt : j < 2 ^ (stage + 1) :=
    Nat.lt_trans hj (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self stage))
  rw [Nat.div_eq_of_lt hlt, add_zero]

private theorem butterfly_upper_div_block (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) / 2 ^ (stage + 1) = block := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      block * 2 ^ (stage + 1) + (j + 2 ^ stage) by omega]
  rw [Nat.mul_comm block (2 ^ (stage + 1))]
  rw [Nat.mul_add_div (Nat.two_pow_pos (stage + 1))]
  have hlt : j + 2 ^ stage < 2 ^ (stage + 1) := by
    rw [pow_succ]
    omega
  rw [Nat.div_eq_of_lt hlt, add_zero]

private theorem butterfly_lower_mod_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) % 2 ^ stage = j := by
  rw [show block * 2 ^ (stage + 1) + j = (block * 2) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hj

private theorem butterfly_upper_mod_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) % 2 ^ stage = j := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      (block * 2 + 1) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt hj

private theorem butterfly_lower_div_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j) / 2 ^ stage = block * 2 := by
  rw [show block * 2 ^ (stage + 1) + j = (block * 2) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_comm (block * 2) (2 ^ stage)]
  rw [Nat.mul_add_div (Nat.two_pow_pos stage)]
  rw [Nat.div_eq_of_lt hj, add_zero]

private theorem butterfly_upper_div_half (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) / 2 ^ stage = block * 2 + 1 := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      (block * 2 + 1) * 2 ^ stage + j by
    rw [pow_succ]
    ring]
  rw [Nat.mul_comm (block * 2 + 1) (2 ^ stage)]
  rw [Nat.mul_add_div (Nat.two_pow_pos stage)]
  rw [Nat.div_eq_of_lt hj, add_zero]

private theorem butterfly_j_mod_blockSize (stage j : Nat) (hj : j < 2 ^ stage) :
    j % 2 ^ (stage + 1) = j := by
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans hj (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self stage)))

private theorem butterfly_upper_mod_blockSize (stage block j : Nat) (hj : j < 2 ^ stage) :
    (block * 2 ^ (stage + 1) + j + 2 ^ stage) % 2 ^ (stage + 1) =
      j + 2 ^ stage := by
  rw [show block * 2 ^ (stage + 1) + j + 2 ^ stage =
      block * 2 ^ (stage + 1) + (j + 2 ^ stage) by omega]
  rw [Nat.mul_add_mod_self_right]
  exact Nat.mod_eq_of_lt (by
    rw [pow_succ]
    omega)

private theorem stageTwiddle_eq_stride
    (D : Domain R) (stage : Nat) (hstage : stage < D.logN) :
    stageTwiddle D stage = D.omega ^ (2 ^ (D.logN - (stage + 1))) := by
  unfold stageTwiddle
  congr 1
  rw [Domain.n]
  exact Nat.pow_div (Nat.succ_le_of_lt hstage) (by decide : 0 < 2)

private theorem stage_stride_half_eq_domain_half
    (D : Domain R) (stage : Nat) (hstage : stage < D.logN) :
    2 ^ stage * 2 ^ (D.logN - (stage + 1)) = D.n / 2 := by
  rw [Domain.n, Nat.pow_div (show 1 ≤ D.logN by omega) (by decide : 0 < 2)]
  rw [← pow_add]
  congr 1
  omega

private theorem omega_pow_domain_mul (D : Domain R) (k : Nat) :
    D.omega ^ (D.n * k) = 1 := by
  have h : D.omega ^ D.n = 1 := by
    simpa [Domain.n] using D.primitive.pow_eq_one
  rw [pow_mul, h, one_pow]

private theorem omega_pow_add_domain_mul (D : Domain R) (e k : Nat) :
    D.omega ^ (e + D.n * k) = D.omega ^ e := by
  rw [pow_add, omega_pow_domain_mul D k, mul_one]

private theorem omega_pow_domain_half_eq_neg_one
    (D : Domain R) (hlog : 0 < D.logN) :
    D.omega ^ (D.n / 2) = -1 := by
  have hdiv : 2 ∣ D.n := by
    simpa [Domain.n] using Nat.pow_dvd_pow 2 (show 1 ≤ D.logN by omega)
  have hprod : D.n = D.n / 2 * 2 := by
    exact (Nat.div_mul_cancel hdiv).symm
  have hprim2 : IsPrimitiveRoot (D.omega ^ (D.n / 2)) 2 := by
    exact IsPrimitiveRoot.pow D.n_pos D.primitive hprod
  exact IsPrimitiveRoot.eq_neg_one_of_two_right hprim2

private theorem omega_pow_stage_stride_eq_neg_one
    (D : Domain R) (stage : Nat) (hstage : stage < D.logN) :
    D.omega ^ (2 ^ stage * 2 ^ (D.logN - (stage + 1))) = -1 := by
  rw [stage_stride_half_eq_domain_half D stage hstage]
  exact omega_pow_domain_half_eq_neg_one D (by omega)

private theorem forwardMathPairsSpec_get_lower_current
    (D : Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j < (forwardMathPairsSpec D stage block j a).size) :
    (forwardMathPairsSpec D stage block j a)[block * 2 ^ (stage + 1) + j] =
      forwardMathValueAt D stage a (block * 2 ^ (stage + 1) + j) := by
  simp [forwardMathPairsSpec, forwardMathValueAt,
    butterfly_lower_div_block stage block j hj,
    butterfly_lower_mod_half stage block j hj]

private theorem forwardMathPairsSpec_get_upper_current
    (D : Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j + 2 ^ stage <
      (forwardMathPairsSpec D stage block j a).size) :
    (forwardMathPairsSpec D stage block j a)[block * 2 ^ (stage + 1) + j + 2 ^ stage] =
      forwardMathValueAt D stage a (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [forwardMathPairsSpec, forwardMathValueAt,
    butterfly_upper_div_block stage block j hj,
    butterfly_upper_mod_half stage block j hj]

private theorem forwardMathPairsSpec_get_lower_next
    (D : Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j < (forwardMathPairsSpec D stage block (j + 1) a).size) :
    (forwardMathPairsSpec D stage block (j + 1) a)[block * 2 ^ (stage + 1) + j] =
      forwardMathValueAt D (stage + 1) a (block * 2 ^ (stage + 1) + j) := by
  simp [forwardMathPairsSpec, forwardMathValueAt,
    butterfly_lower_div_block stage block j hj,
    butterfly_lower_mod_half stage block j hj]

private theorem forwardMathPairsSpec_get_upper_next
    (D : Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    (hi : block * 2 ^ (stage + 1) + j + 2 ^ stage <
      (forwardMathPairsSpec D stage block (j + 1) a).size) :
    (forwardMathPairsSpec D stage block (j + 1) a)[block * 2 ^ (stage + 1) + j + 2 ^ stage] =
      forwardMathValueAt D (stage + 1) a (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [forwardMathPairsSpec, forwardMathValueAt,
    butterfly_upper_div_block stage block j hj,
    butterfly_upper_mod_half stage block j hj]

private theorem forwardMathValueAt_succ_lower
    (D : Domain R) (stage block j : Nat) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage) :
    forwardMathValueAt D (stage + 1) a (block * 2 ^ (stage + 1) + j) =
      forwardMathValueAt D stage a (block * 2 ^ (stage + 1) + j) +
        (stageTwiddle D stage) ^ j *
          forwardMathValueAt D stage a (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [forwardMathValueAt,
    butterfly_lower_div_block stage block j hj,
    butterfly_lower_mod_half stage block j hj,
    butterfly_lower_div_half stage block j hj,
    butterfly_upper_div_half stage block j hj,
    butterfly_upper_mod_half stage block j hj,
    butterfly_j_mod_blockSize stage j hj,
    stageTwiddle_eq_stride D stage hstage]
  have hbits : D.logN - stage = (D.logN - (stage + 1)) + 1 := by
    omega
  rw [← Fin.sum_univ_odd_even
    (n := stage)
    (f := fun x =>
      a[bitRevNat (D.logN - (stage + 1)) block +
          x * 2 ^ (D.logN - (stage + 1))]?.getD 0 *
        D.omega ^ (j * x * 2 ^ (D.logN - (stage + 1))))]
  rw [hbits]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 = 2 * block by ring]
    rw [bitRevNat_even]
    rw [pow_succ]
    rw [show bitRevNat (D.logN - (stage + 1)) block +
          2 * ↑x * 2 ^ (D.logN - (stage + 1)) =
        bitRevNat (D.logN - (stage + 1)) block +
          ↑x * (2 ^ (D.logN - (stage + 1)) * 2) by ring]
    rw [show j * (2 * ↑x) * 2 ^ (D.logN - (stage + 1)) =
        j * ↑x * (2 ^ (D.logN - (stage + 1)) * 2) by ring]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 + 1 = 2 * block + 1 by ring]
    rw [bitRevNat_odd]
    rw [pow_succ]
    rw [show bitRevNat (D.logN - (stage + 1)) block +
          (2 * ↑x + 1) * 2 ^ (D.logN - (stage + 1)) =
        2 ^ (D.logN - (stage + 1)) +
          bitRevNat (D.logN - (stage + 1)) block +
          ↑x * (2 ^ (D.logN - (stage + 1)) * 2) by ring]
    rw [← pow_mul]
    rw [show j * (2 * ↑x + 1) * 2 ^ (D.logN - (stage + 1)) =
        2 ^ (D.logN - (stage + 1)) * j +
          j * ↑x * (2 ^ (D.logN - (stage + 1)) * 2) by ring]
    rw [pow_add]
    ring

private theorem forwardMathValueAt_succ_upper
    (D : Domain R) (stage block j : Nat) (a : Array R)
    (hstage : stage < D.logN) (hj : j < 2 ^ stage) :
    forwardMathValueAt D (stage + 1) a (block * 2 ^ (stage + 1) + j + 2 ^ stage) =
      forwardMathValueAt D stage a (block * 2 ^ (stage + 1) + j) -
        (stageTwiddle D stage) ^ j *
          forwardMathValueAt D stage a (block * 2 ^ (stage + 1) + j + 2 ^ stage) := by
  simp [forwardMathValueAt,
    butterfly_upper_div_block stage block j hj,
    butterfly_upper_mod_blockSize stage block j hj,
    butterfly_lower_div_half stage block j hj,
    butterfly_lower_mod_half stage block j hj,
    butterfly_upper_div_half stage block j hj,
    butterfly_upper_mod_half stage block j hj,
    stageTwiddle_eq_stride D stage hstage]
  have hbits : D.logN - stage = (D.logN - (stage + 1)) + 1 := by
    omega
  rw [← Fin.sum_univ_odd_even
    (n := stage)
    (f := fun x =>
      a[bitRevNat (D.logN - (stage + 1)) block +
          x * 2 ^ (D.logN - (stage + 1))]?.getD 0 *
        D.omega ^ ((j + 2 ^ stage) * x * 2 ^ (D.logN - (stage + 1))))]
  rw [hbits]
  rw [Finset.mul_sum]
  rw [sub_eq_add_neg]
  have hN :
      D.n = 2 ^ stage * (2 ^ (D.logN - (stage + 1)) * 2) := by
    rw [Domain.n, ← pow_succ, ← pow_add]
    congr 1
    omega
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 = 2 * block by ring]
    rw [bitRevNat_even]
    rw [pow_succ]
    rw [show bitRevNat (D.logN - (stage + 1)) block +
          2 * ↑x * 2 ^ (D.logN - (stage + 1)) =
        bitRevNat (D.logN - (stage + 1)) block +
          ↑x * (2 ^ (D.logN - (stage + 1)) * 2) by ring]
    rw [show (j + 2 ^ stage) * (2 * ↑x) * 2 ^ (D.logN - (stage + 1)) =
        j * ↑x * (2 ^ (D.logN - (stage + 1)) * 2) + D.n * ↑x by
      rw [hN]
      ring]
    rw [omega_pow_add_domain_mul]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show block * 2 + 1 = 2 * block + 1 by ring]
    rw [bitRevNat_odd]
    rw [pow_succ]
    rw [show bitRevNat (D.logN - (stage + 1)) block +
          (2 * ↑x + 1) * 2 ^ (D.logN - (stage + 1)) =
        2 ^ (D.logN - (stage + 1)) +
          bitRevNat (D.logN - (stage + 1)) block +
          ↑x * (2 ^ (D.logN - (stage + 1)) * 2) by ring]
    rw [show (j + 2 ^ stage) * (2 * ↑x + 1) * 2 ^ (D.logN - (stage + 1)) =
        (D.n / 2 +
          (2 ^ (D.logN - (stage + 1)) * j +
            j * ↑x * (2 ^ (D.logN - (stage + 1)) * 2))) +
          D.n * ↑x by
      rw [← stage_stride_half_eq_domain_half D stage hstage, hN]
      ring]
    rw [omega_pow_add_domain_mul]
    rw [pow_add, omega_pow_domain_half_eq_neg_one D (by omega)]
    rw [pow_add]
    rw [← pow_mul]
    ring

private theorem eq_lower_or_upper_of_block_pair
    (stage block j i : Nat) (_hj : j < 2 ^ stage)
    (hblock : i / 2 ^ (stage + 1) = block) (hpair : i % 2 ^ stage = j) :
    i = block * 2 ^ (stage + 1) + j ∨
      i = block * 2 ^ (stage + 1) + j + 2 ^ stage := by
  let half : Nat := 2 ^ stage
  let r : Nat := i % 2 ^ (stage + 1)
  have hblockSize : 2 ^ (stage + 1) = 2 * half := by
    simp [half, pow_succ, Nat.mul_comm]
  have hi_decomp : i = block * 2 ^ (stage + 1) + r := by
    calc
      i = 2 ^ (stage + 1) * (i / 2 ^ (stage + 1)) + i % 2 ^ (stage + 1) := by
        exact (Nat.div_add_mod i (2 ^ (stage + 1))).symm
      _ = i / 2 ^ (stage + 1) * 2 ^ (stage + 1) + i % 2 ^ (stage + 1) := by
        ring
      _ = block * 2 ^ (stage + 1) + r := by
        simp [hblock, r]
  have hr_lt : r < 2 * half := by
    simpa [r, hblockSize] using Nat.mod_lt i (Nat.two_pow_pos (stage + 1))
  have hhalf_dvd : half ∣ 2 ^ (stage + 1) := by
    rw [hblockSize]
    exact ⟨2, by ring⟩
  have hr_mod : r % half = j := by
    simpa [r, half, hpair] using (Nat.mod_mod_of_dvd i hhalf_dvd)
  have hr_decomp : r = (r / half) * half + j := by
    calc
      r = half * (r / half) + r % half := by
        exact (Nat.div_add_mod r half).symm
      _ = r / half * half + r % half := by
        ring
      _ = r / half * half + j := by rw [hr_mod]
  have hq_lt : r / half < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos stage)]
    simpa [half, Nat.mul_comm] using hr_lt
  interval_cases hq : r / half
  · left
    rw [hi_decomp, hr_decomp]
    simp
  · right
    rw [hi_decomp, hr_decomp]
    simp [half]
    omega

private theorem forwardMathPairsSpec_get_unchanged
    (D : Domain R) (stage block j : Nat) (a : Array R) (hj : j < 2 ^ stage)
    {i : Nat}
    (hiOld : i < (forwardMathPairsSpec D stage block j a).size)
    (hiNew : i < (forwardMathPairsSpec D stage block (j + 1) a).size)
    (hneLower : block * 2 ^ (stage + 1) + j ≠ i)
    (hneUpper : block * 2 ^ (stage + 1) + j + 2 ^ stage ≠ i) :
    (forwardMathPairsSpec D stage block j a)[i] =
      (forwardMathPairsSpec D stage block (j + 1) a)[i] := by
  simp only [forwardMathPairsSpec, Array.getElem_ofFn]
  by_cases hltBlock : i / 2 ^ (stage + 1) < block
  · rw [if_pos hltBlock, if_pos hltBlock]
  · rw [if_neg hltBlock, if_neg hltBlock]
    by_cases hEqBlock : i / 2 ^ (stage + 1) = block
    · rw [if_pos hEqBlock, if_pos hEqBlock]
      by_cases hltPair : i % 2 ^ stage < j
      · rw [if_pos hltPair, if_pos (Nat.lt_trans hltPair (Nat.lt_succ_self j))]
      · have hgePair : j ≤ i % 2 ^ stage := Nat.le_of_not_lt hltPair
        rw [if_neg hltPair]
        by_cases hltPairNext : i % 2 ^ stage < j + 1
        · have hpair : i % 2 ^ stage = j := by omega
          rcases eq_lower_or_upper_of_block_pair stage block j i hj hEqBlock hpair with h | h
          · exact (hneLower h.symm).elim
          · exact (hneUpper h.symm).elim
        · rw [if_neg hltPairNext]
    · rw [if_neg hEqBlock, if_neg hEqBlock]

private theorem butterfly_upper_lt_of_lower_lt_domain
    (D : Domain R) (stage block j : Nat) (hstage : stage < D.logN) (hj : j < 2 ^ stage)
    (hlower : block * 2 ^ (stage + 1) + j < D.n) :
    block * 2 ^ (stage + 1) + j + 2 ^ stage < D.n := by
  let blocks : Nat := 2 ^ (D.logN - (stage + 1))
  let blockSize : Nat := 2 ^ (stage + 1)
  have hN : D.n = blocks * blockSize := by
    dsimp [Domain.n, blocks, blockSize]
    rw [← pow_add]
    congr 1
    omega
  have hlower' : block * blockSize + j < blocks * blockSize := by
    rw [← hN]
    simpa [blockSize] using hlower
  have hblock : block < blocks := by
    by_contra hnot
    have hle : blocks ≤ block := Nat.le_of_not_lt hnot
    have hmul : blocks * blockSize ≤ block * blockSize := Nat.mul_le_mul_right blockSize hle
    have hle' : blocks * blockSize ≤ block * blockSize + j :=
      Nat.le_trans hmul (Nat.le_add_right _ _)
    omega
  have hupperBlock :
      block * blockSize + j + 2 ^ stage < (block + 1) * blockSize := by
    calc
      block * blockSize + j + 2 ^ stage < block * blockSize + blockSize := by
        have hjBlock : j + 2 ^ stage < blockSize := by
          dsimp [blockSize]
          rw [pow_succ]
          omega
        omega
      _ = (block + 1) * blockSize := by ring
  have hnext : block + 1 ≤ blocks := Nat.succ_le_of_lt hblock
  have hnextMul : (block + 1) * blockSize ≤ blocks * blockSize :=
    Nat.mul_le_mul_right blockSize hnext
  rw [hN]
  exact Nat.lt_of_lt_of_le hupperBlock hnextMul

/--
One pure butterfly stage advances the mathematical partial-DFT invariant by one
stage.

This is the main Cooley-Tukey algebra step.
-/
private theorem butterflyInnerStep_forwardMathPairsSpec_succ
    (D : Domain R) (stage block : Nat) (a : Array R) (hstage : stage < D.logN) :
    ∀ donePairs : Nat,
      donePairs < 2 ^ stage →
        butterflyInnerStep
          (2 ^ (stage + 1))
          (2 ^ stage)
          (stageTwiddle D stage)
          block donePairs
          (forwardMathPairsSpec D stage block donePairs a, (stageTwiddle D stage) ^ donePairs) =
        (forwardMathPairsSpec D stage block (donePairs + 1) a,
          (stageTwiddle D stage) ^ (donePairs + 1)) := by
  intro donePairs hdonePairs
  simp [butterflyInnerStep]
  constructor
  · apply Array.ext
    · simp [forwardMathPairsSpec]
    · intro i hi₁ hi₂
      simp only [Array.size_setIfInBounds] at hi₁
      simp [Array.getElem_setIfInBounds, hi₁]
      by_cases hUpper : block * 2 ^ (stage + 1) + donePairs + 2 ^ stage = i
      · rw [if_pos hUpper]
        subst i
        have hLowerOld :
            block * 2 ^ (stage + 1) + donePairs <
              (forwardMathPairsSpec D stage block donePairs a).size := by
          omega
        rw [Array.getElem?_eq_getElem hLowerOld]
        rw [Array.getElem?_eq_getElem hi₁]
        simp only [Option.getD_some]
        rw [forwardMathPairsSpec_get_lower_current D stage block donePairs a hdonePairs hLowerOld]
        rw [forwardMathPairsSpec_get_upper_current D stage block donePairs a hdonePairs hi₁]
        rw [forwardMathPairsSpec_get_upper_next D stage block donePairs a hdonePairs hi₂]
        exact (forwardMathValueAt_succ_upper D stage block donePairs a hstage hdonePairs).symm
      · rw [if_neg hUpper]
        by_cases hLower : block * 2 ^ (stage + 1) + donePairs = i
        · rw [if_pos hLower]
          subst i
          have hLowerDomain : block * 2 ^ (stage + 1) + donePairs < D.n := by
            simpa [forwardMathPairsSpec] using hi₁
          have hUpperDomain :
              block * 2 ^ (stage + 1) + donePairs + 2 ^ stage < D.n :=
            butterfly_upper_lt_of_lower_lt_domain
              D stage block donePairs hstage hdonePairs hLowerDomain
          have hUpperOld :
              block * 2 ^ (stage + 1) + donePairs + 2 ^ stage <
                (forwardMathPairsSpec D stage block donePairs a).size := by
            simpa [forwardMathPairsSpec] using hUpperDomain
          rw [Array.getElem?_eq_getElem hi₁]
          rw [Array.getElem?_eq_getElem hUpperOld]
          simp only [Option.getD_some]
          rw [forwardMathPairsSpec_get_lower_current D stage block donePairs a hdonePairs hi₁]
          rw [forwardMathPairsSpec_get_upper_current D stage block donePairs a hdonePairs hUpperOld]
          rw [forwardMathPairsSpec_get_lower_next D stage block donePairs a hdonePairs hi₂]
          exact (forwardMathValueAt_succ_lower D stage block donePairs a hstage hdonePairs).symm
        · rw [if_neg hLower]
          exact forwardMathPairsSpec_get_unchanged D stage block donePairs a hdonePairs
            hi₁ hi₂ hLower hUpper
  · rw [pow_succ]

private theorem butterflyBlockStep_aux_forwardMathPairsSpec
    (D : Domain R) (stage block : Nat) (a : Array R) (hstage : stage < D.logN) :
    ∀ donePairs : Nat,
      donePairs ≤ 2 ^ stage →
        (Nat.rec (motive := fun _ => Array R × R)
          (forwardMathBlocksSpec D stage block a, (1 : R))
          (fun j st =>
            butterflyInnerStep
              (2 ^ (stage + 1))
              (2 ^ stage)
              (stageTwiddle D stage)
              block j st)
          donePairs) =
        (forwardMathPairsSpec D stage block donePairs a,
          (stageTwiddle D stage) ^ donePairs) := by
  intro donePairs
  induction donePairs with
  | zero =>
      intro _
      simp [forwardMathPairsSpec_zero, stageTwiddle]
  | succ donePairs ih =>
      intro hdonePairs
      have hlt : donePairs < 2 ^ stage := Nat.lt_of_succ_le hdonePairs
      have hstep :=
        butterflyInnerStep_forwardMathPairsSpec_succ D stage block a hstage donePairs hlt
      simpa [ih (Nat.le_of_succ_le hdonePairs)] using hstep

private theorem butterflyBlockStep_forwardMathBlocksSpec_succ
    (D : Domain R) (stage block : Nat) (a : Array R) (hstage : stage < D.logN) :
    butterflyBlockStep
      (2 ^ (stage + 1))
      (2 ^ stage)
      (stageTwiddle D stage)
      block
      (forwardMathBlocksSpec D stage block a) =
    forwardMathBlocksSpec D stage (block + 1) a := by
  have hpairs :=
    butterflyBlockStep_aux_forwardMathPairsSpec D stage block a hstage (2 ^ stage) le_rfl
  simpa [butterflyBlockStep, forwardMathPairsSpec_half, stageTwiddle]
    using congrArg Prod.fst hpairs

private theorem butterflyStageSpec_aux_forwardMathBlocksSpec
    (D : Domain R) (stage : Nat) (a : Array R) (hstage : stage < D.logN) :
    ∀ doneBlocks : Nat,
      (Nat.rec (motive := fun _ => Array R)
        (forwardMathStageSpec D stage a)
        (fun block acc =>
          butterflyBlockStep
            (2 ^ (stage + 1))
            (2 ^ stage)
            (stageTwiddle D stage)
            block acc)
        doneBlocks) =
      forwardMathBlocksSpec D stage doneBlocks a := by
  intro doneBlocks
  induction doneBlocks with
  | zero =>
      simp [forwardMathBlocksSpec_zero]
  | succ doneBlocks ih =>
      simp [ih, butterflyBlockStep_forwardMathBlocksSpec_succ D stage doneBlocks a hstage]

theorem butterflyStageSpec_forwardMathStageSpec_succ
    (D : Domain R) (stage : Nat) (a : Array R) (hstage : stage < D.logN) :
    butterflyStageSpec D stage (forwardMathStageSpec D stage a) =
      forwardMathStageSpec D (stage + 1) a := by
  calc
    butterflyStageSpec D stage (forwardMathStageSpec D stage a)
      = forwardMathBlocksSpec D stage (D.n / 2 ^ (stage + 1)) a := by
          simpa [butterflyStageSpec, stageTwiddle] using
            butterflyStageSpec_aux_forwardMathBlocksSpec D stage a hstage (D.n / 2 ^ (stage + 1))
    _ = forwardMathStageSpec D (stage + 1) a := by
          exact forwardMathBlocksSpec_final D stage a hstage

/--
The pure stage recursion matches the mathematical partial-DFT state at every
stage.
-/
theorem forwardStagePureSpec_eq_forwardMathStageSpec (D : Domain R) (a : Array R) :
    ∀ completed : Nat, completed ≤ D.logN →
      forwardStagePureSpec D completed a = forwardMathStageSpec D completed a := by
  intro completed
  induction completed with
  | zero =>
      intro _
      rw [forwardStagePureSpec_zero, forwardMathStageSpec_zero]
  | succ completed ih =>
      intro hcompleted
      have hle : completed ≤ D.logN := Nat.le_of_succ_le hcompleted
      have hlt : completed < D.logN := Nat.lt_of_succ_le hcompleted
      rw [forwardStagePureSpec_succ, ih hle]
      exact butterflyStageSpec_forwardMathStageSpec_succ D completed a hlt

/--
Algorithmic stages coincide with the proof-oriented stagewise specification.

This is the loop-invariant bridge: the imperative `for stage in [0:D.logN]`
implementation computes the same intermediate states as `forwardStageSpec`.
Basically, this is recursion vs. `for` loop bookkeeping.
-/
theorem runStages_bitRevPermute_eq_forwardStageSpec (D : Domain R) (a : Array R) :
    runStages D (bitRevPermute D a) = forwardStageSpec D D.logN a := by
  have hfold :
      ∀ n : Nat,
        List.foldl
          (fun acc stage => butterflyStage D stage acc)
          (bitRevPermute D a)
          (List.range n) =
          Nat.rec (bitRevPermute D a) (fun stage acc => butterflyStage D stage acc) n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        simp [List.range_succ, List.foldl_append, ih]
  simp [runStages]
  rw [← List.range_eq_range']
  simpa [forwardStageSpec] using hfold D.logN

/--
Once all `logN` stages are completed, the stagewise specification matches the
direct NTT formula.
-/
theorem forwardMathStageSpec_final_eq_forwardSpec (D : Domain R) (a : Array R) :
    forwardMathStageSpec D D.logN a = forwardSpec D a := by
  apply Array.ext
  · simp [forwardMathStageSpec, forwardSpec]
  · intro i hi₁ hi₂
    have hi : i < D.n := by
      simpa [forwardSpec] using hi₂
    have himod : i % 2 ^ D.logN = i := by
      simpa [Domain.n] using Nat.mod_eq_of_lt hi
    have hidiv : i / 2 ^ D.logN = 0 := by
      have hi' : i < 2 ^ D.logN := by
        simpa [Domain.n] using hi
      exact Nat.div_eq_of_lt hi'
    simp [forwardMathStageSpec, forwardSpec, nttAt, himod, bitRevNat]
    rfl

/--
Once all `logN` stages are completed, the stagewise specification matches the
direct NTT formula.
-/
theorem forwardStageSpec_final_eq_forwardSpec (D : Domain R) (a : Array R) :
    forwardStageSpec D D.logN a = forwardSpec D a := by
  calc
    forwardStageSpec D D.logN a = forwardStagePureSpec D D.logN a := by
      exact forwardStageSpec_eq_forwardStagePureSpec D a D.logN
    _ = forwardMathStageSpec D D.logN a := by
      exact forwardStagePureSpec_eq_forwardMathStageSpec D a D.logN le_rfl
    _ = forwardSpec D a := by
      exact forwardMathStageSpec_final_eq_forwardSpec D a

/-- Intended fast implementation entry point for NTT. -/
@[inline] def forwardImpl (D : Domain R) (p : CPolynomial.Raw R) : Array R :=
  runStages D (bitRevPermute D p)

@[simp] theorem size_forwardSpec (D : Domain R) (a : Array R) :
    (forwardSpec D a).size = D.n := by
  simp [forwardSpec]

theorem forwardImpl_correct (D : Domain R) (p : CPolynomial.Raw R) :
    forwardImpl D p = forwardSpec D p := by
  rw [forwardImpl]
  rw [runStages_bitRevPermute_eq_forwardStageSpec]
  rw [forwardStageSpec_final_eq_forwardSpec]

end Forward
end NTT
end CPolynomial
end CompPoly
