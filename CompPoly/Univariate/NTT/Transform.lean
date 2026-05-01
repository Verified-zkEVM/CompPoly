/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Data.Nat.Bitwise

/-!
# Shared radix-2 NTT transform

This file provides the root-parametric bit-reversal and butterfly machinery used
by forward and inverse radix-2 NTTs.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Transform

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

/-- Reverse the lowest `bits` bits of `i`. -/
def bitRevNat : Nat → Nat → Nat
  | 0, _ => 0
  | bits + 1, i => ((i &&& 1) <<< bits) ||| bitRevNat bits (i >>> 1)

theorem bitRevNat_lt (bits i : Nat) : bitRevNat bits i < 2 ^ bits := by
  induction bits generalizing i with
  | zero =>
      simp [bitRevNat]
  | succ bits ih =>
      rw [bitRevNat]
      apply Nat.append_lt
      · exact ih (i >>> 1)
      · rw [Nat.and_one_is_mod]
        exact Nat.mod_lt _ (by decide : 0 < 2)

theorem bitRevNat_even (bits b : Nat) :
    bitRevNat (bits + 1) (2 * b) = bitRevNat bits b := by
  simp [bitRevNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem bitRevNat_odd_or (bits b : Nat) :
    bitRevNat (bits + 1) (2 * b + 1) = (1 <<< bits) ||| bitRevNat bits b := by
  rw [bitRevNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  have hdiv : (2 * b + 1) / 2 = b := by
    have h2 : 0 < 2 := by decide
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.add_mul_div_right 1 b (H := h2))
  rw [hdiv]
  simp

theorem bitRevNat_odd (bits b : Nat) :
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

def butterflyInnerStep
    (blockSize half : Nat) (wm : R) (block j : Nat) (st : Array R × R) : Array R × R :=
  let acc := st.1
  let w := st.2
  let i0 := block * blockSize + j
  let i1 := i0 + half
  let u := acc.getD i0 0
  let t := w * acc.getD i1 0
  (((acc.set! i0 (u + t)).set! i1 (u - t)), w * wm)

def butterflyBlockStep
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

@[simp] theorem size_butterflyInnerStep
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

@[simp] theorem size_butterflyBlockStep
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

/-- The imperative stage loop agrees with the corresponding `Nat.rec`. -/
theorem runStages_eq_rec (D : Domain R) (a : Array R) :
    runStages D a = Nat.rec a (fun stage acc => butterflyStage D stage acc) D.logN := by
  simp [runStages]
  rw [← List.range_eq_range']
  exact foldl_range_eq_rec (f := fun stage acc => butterflyStage D stage acc) (x := a) D.logN

end Transform
end NTT
end CPolynomial
end CompPoly
