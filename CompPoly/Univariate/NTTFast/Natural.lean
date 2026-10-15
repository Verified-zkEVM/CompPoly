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

/-- Map a same-carrier array with one write per coefficient and machine-word indices. -/
@[specialize] def mapUGo (f : α → α) (limit i : USize) (a : Array α)
    (hs : a.size = limit.toNat) : Array α :=
  if hi : i < limit then
    have hin : i.toNat < a.size := by have h : i.toNat < limit.toNat := hi; omega
    let b := a.uset i (f (a.uget i hin)) hin
    have hb : b.size = limit.toNat := (Array.size_uset ..).trans hs
    have hn : (i + 1).toNat = i.toNat + 1 :=
      Plan.usize_add_one i (by
        have := limit.toNat_lt_size
        have h : i.toNat < limit.toNat := hi
        omega)
    mapUGo f limit (i + 1) b hb
  else a
termination_by limit.toNat - i.toNat
decreasing_by omega

/-- Mapping changes coefficients but preserves the array length. -/
@[simp] theorem size_mapUGo (f : α → α) (limit i : USize) (a : Array α) (hs) :
    (mapUGo f limit i a hs).size = a.size := by
  rw [mapUGo]
  split
  · rw [size_mapUGo]
    exact Array.size_uset ..
  · rfl
termination_by limit.toNat - i.toNat
decreasing_by
  have _h : i.toNat < limit.toNat := ‹i < limit›
  have _hn := Plan.usize_add_one i (by have := limit.toNat_lt_size; omega)
  omega

private theorem getD_uset (a : Array α) (i : USize) (v d : α) (hi) (k : Nat) :
    (a.uset i v hi).getD k d = if i.toNat = k then v else a.getD k d := by
  simp only [Array.uset_eq_set, Array.getD_eq_getD_getElem?, Array.getElem?_set]
  split <;> rfl

/-- The loop maps the untouched suffix and leaves the preceding coefficients alone. -/
theorem getD_mapUGo (f : α → α) (limit i : USize) (a : Array α) (hs)
    (k : Nat) (hk : k < a.size) (d : α) :
    (mapUGo f limit i a hs).getD k d =
      if i.toNat ≤ k then f (a.getD k d) else a.getD k d := by
  rw [mapUGo]
  split
  · rename_i hi
    have hin : i.toNat < limit.toNat := hi
    have hia : i.toNat < a.size := by omega
    have hn := Plan.usize_add_one i (by have := limit.toNat_lt_size; omega)
    let b := a.uset i (f (a.uget i hia)) hia
    have hbs : b.size = limit.toNat := (Array.size_uset ..).trans hs
    have hkb : k < b.size := by simpa only [b, Array.size_uset] using hk
    rw [getD_mapUGo f limit (i + 1) b hbs k hkb d, getD_uset]
    by_cases he : i.toNat = k
    · subst k
      simp only [hn, Nat.not_succ_le_self, Nat.le_refl, ↓reduceIte, Array.uget]
      rfl
    · have hp : ((i + 1).toNat ≤ k) = (i.toNat ≤ k) := by apply propext; rw [hn]; omega
      simp only [he, hp, ↓reduceIte]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some]
      rfl
  · rename_i hi
    have hin : ¬ i.toNat < limit.toNat := hi
    have hp : ¬ i.toNat ≤ k := by omega
    simp only [hp, ↓reduceIte]
termination_by limit.toNat - i.toNat
decreasing_by
  have _h : i.toNat < limit.toNat := ‹i < limit›
  have _hn := Plan.usize_add_one i (by have := limit.toNat_lt_size; omega)
  omega

/-- The machine-index map has the ordinary array-map semantics from index zero. -/
theorem mapUGo_zero (f : α → α) (limit : USize) (a : Array α) (hs) :
    mapUGo f limit 0 a hs = a.map f := by
  apply Array.ext
  · simp only [size_mapUGo, Array.size_map]
  · intro k hk hj
    have hka : k < a.size := by simpa only [size_mapUGo] using hk
    have h := getD_mapUGo f limit 0 a hs k hka a[k]
    simpa only [USize.toNat_zero, Nat.zero_le, ↓reduceIte,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk,
      Array.getElem?_eq_getElem hka, Option.getD_some, Array.getElem_map] using h

/-- A natural-order transform plan, including its cached output permutation. -/
structure NaturalPlan (R : Type*) [Field R] where
  plan : Plan R
  order : Array Nat
  order_eq : order = Array.ofFn (fun i : plan.domain.Idx ↦
    NTT.Transform.bitRevNat plan.domain.logN i.val)
  wellFormed : Plan.WellFormed plan

namespace NaturalPlan
variable {R : Type*} [Field R]

/-- Prepare the twiddles and permutation once, outside repeated transforms. -/
def ofDomain (D : NTT.Domain R) : NaturalPlan R :=
  ⟨Plan.ofDomain D, Array.ofFn (fun i : D.Idx ↦ NTT.Transform.bitRevNat D.logN i.val), rfl,
    Plan.ofDomain_wellFormed D⟩

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
  if hs : a.size = P.plan.domain.n then
    if hu : a.size < USize.size then
      mapUGo (fun x ↦ P.plan.nInv * x) (USize.ofNatLT a.size hu) 0 a
        (by simp only [USize.toNat_ofNatLT])
    else tabulate (fun i : P.plan.domain.Idx ↦ P.plan.nInv * a.getD i.val 0)
  else tabulate (fun i : P.plan.domain.Idx ↦ P.plan.nInv * a.getD i.val 0)

/-- Specialized normalization agrees with the existing plan. -/
theorem normalize_eq (P : NaturalPlan R) (a : Array R) :
    P.normalize a = P.plan.normalize a := by
  unfold normalize
  split
  · rename_i hs
    split
    · rw [mapUGo_zero]
      apply Array.ext
      · simp only [Array.size_map, Plan.normalize, Array.size_ofFn, hs]
      · intro i hi hj
        simp only [Plan.normalize, Array.getElem_map, Array.getElem_ofFn,
          Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem (by simpa only [Array.size_map] using hi),
          Option.getD_some]
    · exact tabulate_eq _
  · exact tabulate_eq _

/-- Forward NTT with natural-order input and output. -/
@[inline] def forward [DecidableEq R] (P : NaturalPlan R) (a : Array R) : Array R :=
  P.permute (Plan.checkedStages P.plan.domain P.plan.twiddles (P.load a))

/-- Inverse NTT with natural-order input and output. -/
@[inline] def inverse [DecidableEq R] (P : NaturalPlan R) (a : Array R) : Array R :=
  P.normalize (Plan.checkedDITStages P.plan.inverseDomain P.plan.inverseTwiddles (P.permute a))

/-- The cached forward path equals the existing natural-order pipeline. -/
theorem forward_eq [DecidableEq R] (P : NaturalPlan R) (a : Array R) :
    P.forward a = NTT.Transform.bitRevPermute P.plan.domain (P.plan.forwardImpl a) := by
  rw [forward, Plan.checkedStages_eq, permute_eq, load_eq]
  rfl

/-- The cached inverse path equals the existing natural-order pipeline. -/
theorem inverse_eq [DecidableEq R] (P : NaturalPlan R) (a : Array R) :
    P.inverse a = P.plan.inverseImpl (NTT.Transform.bitRevPermute P.plan.domain a) := by
  rw [inverse, normalize_eq, Plan.checkedDITStages_eq, permute_eq]
  rfl

end NaturalPlan
end CompPoly.CPolynomial.NTTFast
