/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all Init.Data.Array.Basic
public import CompPoly.Univariate.NTTFast.Correctness
public import CompPoly.Univariate.NTTFast.ButterflyDIT
public import CompPoly.Univariate.NTTFast.Permutation

/-! # Reusable natural-order NTT plans

Cache the permutation along with the twiddles: computing a reversed index for every
coefficient on every transform otherwise adds a second logarithmic-time traversal.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast

/-- Specializable array builder: callbacks stay inside the worker's scalar loop. -/
@[specialize] def tabulateGo {n : Nat} (f : Fin n → α) (acc : Array α) :
    (i : Nat) → i ≤ n → Array α
  | i + 1, h =>
    tabulateGo f (acc.push (f ⟨n - i - 1, by omega⟩)) i (by omega)
  | 0, _ => acc

/-- Construct an array without a generic callback in its element loop. -/
@[inline, specialize] def tabulate {n : Nat} (f : Fin n → α) : Array α :=
  tabulateGo f (Array.emptyWithCapacity n) n (Nat.le_refl n)

private theorem tabulateGo_eq {n : Nat} (f : Fin n → α) (i : Nat) (h : i ≤ n)
    (acc : Array α) : tabulateGo f acc i h = Array.ofFn.go f acc i h := by
  induction i generalizing acc with
  | zero => rfl
  | succ i ih => exact ih _ _

/-- The specialized builder has exactly the standard array semantics. -/
theorem tabulate_eq {n : Nat} (f : Fin n → α) : tabulate f = Array.ofFn f :=
  tabulateGo_eq f n (Nat.le_refl n) _

/-- A natural-order transform plan, including its cached output permutation. -/
structure NaturalPlan (R : Type*) [Field R] where
  plan : Plan R
  order : Array Nat
  order_eq : order = Array.ofFn (fun i : plan.domain.Idx ↦
    NTT.Transform.bitRevNat plan.domain.logN i.val)

namespace NaturalPlan
variable {R : Type*} [Field R]

/-- Prepare the twiddles and permutation once, outside repeated transforms. -/
def ofDomain (D : NTT.Domain R) : NaturalPlan R :=
  ⟨Plan.ofDomain D, Array.ofFn (fun i : D.Idx ↦ NTT.Transform.bitRevNat D.logN i.val), rfl⟩

/-- The cached index table has one entry per domain element. -/
@[simp] theorem order_size (P : NaturalPlan R) : P.order.size = P.plan.domain.n := by
  simp only [P.order_eq, Array.size_ofFn]

/-- Each cached entry is the corresponding reversed index. -/
theorem order_get (P : NaturalPlan R) (i : Nat) (hi : i < P.plan.domain.n) :
    P.order[i]! = NTT.Transform.bitRevNat P.plan.domain.logN i := by
  have hio : i < P.order.size := by simpa only [order_size] using hi
  rw [getElem!_pos P.order i hio]
  simp only [P.order_eq, Array.getElem_ofFn]

/-- Reuse a correctly sized array by swapping each reversed pair once. -/
@[inline] def permute (P : NaturalPlan R) (a : Array R) : Array R :=
  if a.size = P.order.size then Array.permuteInvolution P.order a
  else P.order.map (fun i ↦ a.getD i 0)

/-- Pair swaps preserve the original gather, including padding and truncation cases. -/
theorem permute_eq_map (P : NaturalPlan R) (a : Array R) :
    P.permute a = P.order.map (fun i ↦ a.getD i 0) := by
  unfold permute
  split
  · rename_i hs
    apply Array.permuteInvolution_eq_map P.order a 0 hs.symm
    · intro i hi
      have hi' : i < P.plan.domain.n := by simpa only [order_size] using hi
      rw [P.order_get i hi', order_size]
      exact NTT.Transform.bitRevNat_lt _ _
    · intro i hi
      have hi' : i < P.plan.domain.n := by simpa only [order_size] using hi
      rw [P.order_get i hi']
      rw [P.order_get _ (NTT.Transform.bitRevNat_lt _ _)]
      exact NTT.Transform.bitRevNat_involutive _ _ hi'
  · rfl

/-- Cached indexing computes the same permutation as the mathematical definition. -/
theorem permute_eq (P : NaturalPlan R) (a : Array R) :
    P.permute a = NTT.Transform.bitRevPermute P.plan.domain a := by
  simp only [permute_eq_map, P.order_eq, Array.map_ofFn, NTT.Transform.bitRevPermute,
    Function.comp_def]

/-- Reuse an input of the right size; otherwise pad or truncate it as before. -/
@[inline] def load (P : NaturalPlan R) (a : Array R) : Array R :=
  if a.size = P.plan.domain.n then a
  else tabulate (fun i : P.plan.domain.Idx ↦ a.getD i.val 0)

/-- Reusing a correctly sized array preserves the total loading semantics. -/
theorem load_eq (P : NaturalPlan R) (a : Array R) :
    P.load a = NTT.loadNaturalArray P.plan.domain a := by
  unfold load
  split
  · rename_i h
    apply Array.ext
    · simp only [NTT.size_loadNaturalArray, h]
    · intro i hi hj
      simp only [NTT.getElem_loadNaturalArray, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hi, Option.getD_some]
  · exact tabulate_eq _

/-- Specialize normalization so each scalar multiplication stays inside its loop. -/
@[inline] def normalize (P : NaturalPlan R) (a : Array R) : Array R :=
  tabulate (fun i : P.plan.domain.Idx ↦ P.plan.nInv * a.getD i.val 0)

/-- Specialized normalization agrees with the existing plan. -/
theorem normalize_eq (P : NaturalPlan R) (a : Array R) :
    P.normalize a = P.plan.normalize a := tabulate_eq _

/-- Forward NTT with natural-order input and output. -/
@[inline] def forward (P : NaturalPlan R) (a : Array R) : Array R :=
  P.permute (Plan.checkedStages P.plan.domain P.plan.twiddles (P.load a))

/-- Inverse NTT with natural-order input and output. -/
@[inline] def inverse (P : NaturalPlan R) (a : Array R) : Array R :=
  P.normalize (Plan.checkedDITStages P.plan.inverseDomain P.plan.inverseTwiddles (P.permute a))

/-- The cached forward path equals the existing natural-order pipeline. -/
theorem forward_eq (P : NaturalPlan R) (a : Array R) :
    P.forward a = NTT.Transform.bitRevPermute P.plan.domain (P.plan.forwardImpl a) := by
  rw [forward, Plan.checkedStages_eq, permute_eq, load_eq]
  rfl

/-- The cached inverse path equals the existing natural-order pipeline. -/
theorem inverse_eq (P : NaturalPlan R) (a : Array R) :
    P.inverse a = P.plan.inverseImpl (NTT.Transform.bitRevPermute P.plan.domain a) := by
  rw [inverse, normalize_eq, Plan.checkedDITStages_eq, permute_eq]
  rfl

end NaturalPlan
end CompPoly.CPolynomial.NTTFast
