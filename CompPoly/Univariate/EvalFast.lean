/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Ops
public import CompPoly.Univariate.Basic

/-!
# Parallel evaluation at one point

Split a coefficient array into contiguous blocks without copying it. Leaves run Horner;
internal nodes evaluate the halves concurrently and combine their values. `logWorkers`
bounds the number of simultaneously active leaves by `2 ^ logWorkers`; the calling thread
evaluates one of them.
-/

@[expose] public section

namespace CompPoly.CPolynomial

/-- Horner evaluation of the coefficient range `[lo, hi)`, without allocating a slice. -/
@[inline, specialize]
def evalRange [Semiring R] (p : Array R) (x : R) (lo hi : Nat) : R :=
  p.foldr (fun a acc ↦ acc * x + a) 0 hi lo

/-- A field-specific leaf evaluator, with its agreement with Horner evaluation. -/
class EvalKernel (R : Type*) [Semiring R] where
  range : Array R → R → Nat → Nat → R
  range_eq : ∀ p x lo hi, range p x lo hi = evalRange p x lo hi
  /-- The smallest leaf, in coefficients, worth a task of its own; `evalFast` evaluates smaller
  ranges on the calling thread. -/
  minLeaf : Nat := 8192

/-- Default leaves use the semiring’s existing arithmetic. -/
instance (priority := low) [Semiring R] : EvalKernel R where
  range := evalRange
  range_eq := by intros; rfl

/-- Explicit square-and-multiply, shared with the Rust workload. -/
@[specialize]
def evalPower [Monoid R] (x : R) (n : Nat) : R :=
  if n = 0 then 1 else if n = 1 then x else
    let half := evalPower x (n / 2)
    let square := half * half
    if n % 2 = 0 then square else square * x
termination_by n

/-- The benchmark's power schedule computes the usual natural power. -/
theorem evalPower_eq_pow [Monoid R] (x : R) (n : Nat) : evalPower x n = x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [evalPower]
    split
    · subst n; simp only [pow_zero]
    · split
      · subst n; simp only [pow_one]
      · rw [ih (n / 2) (by omega)]
        dsimp only
        rw [← pow_add]
        split
        · congr 1; omega
        · rw [← pow_succ]; congr 1; omega

/-- Build a dependency tree: worker threads never block waiting for child tasks. -/
@[specialize]
def evalParallelTask [Semiring R] [EvalKernel R] (p : Array R) (x : R) (lo hi : Nat) : Nat → Task R
  | 0 => Task.spawn fun _ ↦ EvalKernel.range p x lo hi
  | depth + 1 =>
    if hi - lo < 2 then Task.spawn fun _ ↦ EvalKernel.range p x lo hi else
      let mid := lo + (hi - lo) / 2
      let lower := evalParallelTask p x lo mid depth
      let upper := evalParallelTask p x mid hi depth
      lower.bind (sync := true) fun low ↦ upper.map (sync := true) fun high ↦
        high * evalPower x (mid - lo) + low

/-- Join a spawned upper subtree with the lower range, which the calling thread evaluates
itself. Taking the task as an argument spawns it before the inline work starts. -/
@[noinline, specialize]
def evalJoin [Semiring R] (upper : Task R) (low : Unit → R) (x : R) (n : Nat) : R :=
  let low := low ()
  upper.get * evalPower x n + low

/-- Parallel range evaluation. The calling thread spawns the upper subtrees along the tree's
lower edge and evaluates the lowest leaf itself, so `2 ^ depth` leaves occupy `2 ^ depth - 1`
tasks plus the caller; a caller that only waited would leave one worker's core idle when the
tasks are woken. -/
@[specialize]
def evalParallel [Semiring R] [EvalKernel R] (p : Array R) (x : R) (lo hi : Nat) : Nat → R
  | 0 => EvalKernel.range p x lo hi
  | depth + 1 =>
    if hi - lo < 2 then EvalKernel.range p x lo hi else
      let mid := lo + (hi - lo) / 2
      evalJoin (evalParallelTask p x mid hi depth) (fun _ ↦ evalParallel p x lo mid depth) x
        (mid - lo)

/-- Evaluate one polynomial at one point using up to `2 ^ logWorkers` concurrent blocks, none
smaller than the kernel's `minLeaf` coefficients. -/
@[inline, specialize]
def evalFast [Semiring R] [EvalKernel R] (x : R) (p : CPolynomial R) (logWorkers : Nat := 4) : R :=
  evalParallel p.val x 0 p.val.size
    (min logWorkers (p.val.size / EvalKernel.minLeaf (R := R)).log2)

private theorem horner_affine [Semiring R] (xs : List R) (x acc : R) :
    xs.foldr (fun a v ↦ v * x + a) acc =
      acc * x ^ xs.length + xs.foldr (fun a v ↦ v * x + a) 0 := by
  induction xs with
  | nil => simp only [List.foldr_nil, List.length_nil, pow_zero, mul_one, add_zero]
  | cons a xs ih =>
    simp only [List.foldr_cons, List.length_cons, ih, pow_succ, add_mul, mul_assoc,
      add_assoc]

private theorem evalRange_split [Semiring R] (p : Array R) (x : R)
    (lo mid hi : Nat) (hlo : lo ≤ mid) (hmid : mid ≤ hi) (hhi : hi ≤ p.size) :
    evalRange p x lo hi = evalRange p x mid hi * x ^ (mid - lo) + evalRange p x lo mid := by
  unfold evalRange
  rw [Array.foldr_eq_foldr_extract (start := hi) (stop := lo),
    Array.foldr_eq_foldr_extract (start := hi) (stop := mid),
    Array.foldr_eq_foldr_extract (start := mid) (stop := lo)]
  have hs : p.extract lo hi = p.extract lo mid ++ p.extract mid hi := by
    rw [Array.extract_append_extract, Nat.min_eq_left hlo, Nat.max_eq_right hmid]
  rw [hs, Array.foldr_append]
  simp only [← Array.foldr_toList]
  rw [horner_affine]
  simp only [Array.length_toList, Array.size_extract_of_le (hmid.trans hhi)]

/-- Every task subtree agrees with sequential evaluation of its coefficient range. -/
theorem evalParallelTask_get_eq_evalRange [Semiring R] [EvalKernel R] (p : Array R) (x : R)
    (depth lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ p.size) :
    (evalParallelTask p x lo hi depth).get = evalRange p x lo hi := by
  induction depth generalizing lo hi with
  | zero => exact EvalKernel.range_eq p x lo hi
  | succ depth ih =>
    rw [evalParallelTask]
    split
    · exact EvalKernel.range_eq p x lo hi
    · dsimp only
      simp only [Task.bind, Task.map]
      rw [ih _ _ (by omega) hhi, ih _ _ (by omega) (by omega), evalPower_eq_pow]
      exact (evalRange_split p x lo (lo + (hi - lo) / 2) hi (by omega) (by omega) hhi).symm

/-- Parallel range evaluation agrees with sequential evaluation of its range. -/
theorem evalParallel_eq_evalRange [Semiring R] [EvalKernel R] (p : Array R) (x : R)
    (depth lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ p.size) :
    evalParallel p x lo hi depth = evalRange p x lo hi := by
  induction depth generalizing lo hi with
  | zero => exact EvalKernel.range_eq p x lo hi
  | succ depth ih =>
    rw [evalParallel]
    split
    · exact EvalKernel.range_eq p x lo hi
    · simp only [evalJoin]
      rw [ih _ _ (by omega) (by omega),
        evalParallelTask_get_eq_evalRange p x depth _ _ (by omega) hhi, evalPower_eq_pow]
      exact (evalRange_split p x lo (lo + (hi - lo) / 2) hi (by omega) (by omega) hhi).symm

/-- Parallel evaluation computes exactly the existing Horner evaluator. -/
theorem evalFast_eq_evalHorner [Semiring R] [EvalKernel R] (x : R) (p : CPolynomial R)
    (logWorkers : Nat) : evalFast x p logWorkers = p.evalHorner x := by
  rw [evalFast, evalParallel_eq_evalRange p.val x _ 0 p.val.size (by omega) (by omega)]
  rfl

/-- Parallel evaluation agrees with the mathematical polynomial evaluation API. -/
theorem evalFast_eq_eval [Semiring R] [EvalKernel R] (x : R) (p : CPolynomial R)
    (logWorkers : Nat) :
    evalFast x p logWorkers = p.eval x :=
  (evalFast_eq_evalHorner x p logWorkers).trans (eval_horner_eq_eval x p)

end CompPoly.CPolynomial
