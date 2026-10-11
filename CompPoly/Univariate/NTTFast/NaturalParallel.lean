/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Natural
public import CompPoly.Univariate.NTTFast.Columns
public import CompPoly.Univariate.NTTFast.ColumnsCorrectness
import CompPoly.Univariate.NTTFast.Correctness.Pipeline

/-! # Parallel natural-order transforms on field arrays

Even sizes with enough columns use the column-parallel transform of `Columns`; the other
large sizes run the passes on independent array segments. Both paths are proved equal to the
scalar natural-order transforms.
-/

private theorem extract_self (a : Array α) : a.extract 0 a.size = a :=
  Array.extract_eq_self_of_le (Nat.le_refl _)

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.NaturalPlan
variable {R : Type*}

/-- The column-parallel transform applies to an exactly sized input of an even size of at least
`2 ^ 16` elements; smaller transforms are faster serially. -/
def ColumnsShape (R : Type*) [PackedRepr R] (n logN : Nat) : Prop :=
  n = 2 ^ logN ∧ logN % 2 = 0 ∧ 16 ≤ logN ∧ logN ≤ 36 ∧
    PackedRepr.width R * (2 ^ logN + 256) ≤ USize.size

instance (R : Type*) [PackedRepr R] (n logN : Nat) : Decidable (ColumnsShape R n logN) := by
  unfold ColumnsShape; exact inferInstance

/-- The number of column tasks: `2 ^ (logWorkers + 1)`, but at least 256 columns each. -/
def columnCount (logN logWorkers : Nat) : Nat := 2 ^ min (logWorkers + 1) (logN - 12)

/-- A domain's twiddle table holds `2 ^ s` entries at stage `s`. -/
theorem size_twiddleTable_getD [Field R] (D : NTT.Domain R) (s : Nat) (hs : s < D.logN) :
    ((Plan.twiddleTable D).getD s #[]).size = 2 ^ s := by
  rw [Plan.twiddleTable_getD_eq_twiddlePowers D s hs, Plan.twiddlePowers_size]

/-- The first two forward passes are the column transform's top passes. -/
theorem runPasses_topPasses [Field R] [DecidableEq R] (D : NTT.Domain R) (tw : Array (Array R))
    (a : Array R) (h4 : 4 ≤ D.logN) :
    Parallel.runPasses false tw ((Parallel.forwardPasses D).drop 2)
      (Columns.topPasses tw D.logN a) =
        Parallel.runPasses false tw (Parallel.forwardPasses D) a := by
  have htake : (Parallel.forwardPasses D).take 2 = [D.logN - 2, D.logN - 4] := by
    rw [Parallel.forwardPasses, ← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    omega
  conv_rhs => rw [← List.take_append_drop 2 (Parallel.forwardPasses D)]
  rw [htake]
  rfl

/-- The column transform computes the scalar forward stages of a domain, in natural order. -/
theorem transform_eq_checkedStages [Field R] [DecidableEq R] [PackedRepr R] (D : NTT.Domain R)
    (tw : Array (Array R)) (S : Nat) (scale : Bool) (f : R) (a : Array R)
    (htw : ∀ s < D.logN, (tw.getD s #[]).size = 2 ^ s) (hS : 0 < S)
    (hdiv : S ∣ 2 ^ (D.logN - 4)) (hshape : ColumnsShape R a.size D.logN) :
    Columns.transform tw D.logN S ((Parallel.forwardPasses D).drop 2) scale f a =
      Array.ofFn (n := 2 ^ D.logN) fun i ↦ Columns.scaleBy scale f
        ((Plan.checkedStages D tw a).getD (NTT.Transform.bitRevNat D.logN i) 0) := by
  obtain ⟨hn, heven, h5, h36, hu⟩ := hshape
  rw [Columns.transform_eq tw D.logN S _ scale f a (by omega) h36 hn htw hu hS hdiv,
    runPasses_topPasses D tw a (by omega), ← Parallel.forwardStages_eq D tw a hn]
  · simp only [heven, Nat.zero_ne_one, ↓reduceIte]
  · intro low hlow
    simp only [Parallel.forwardPasses, List.mem_drop_iff_getElem, List.length_map,
      List.length_range, List.getElem_map, List.getElem_range] at hlow
    obtain ⟨i, hi, rfl⟩ := hlow
    rw [show 4 * 2 ^ (D.logN - 1 - 2 * (2 + i) - 1) = 2 ^ (D.logN - 1 - 2 * (2 + i) - 1 + 2) by
      rw [Nat.pow_add]; ring]
    exact Nat.pow_dvd_pow 2 (by omega)

/-- Parallel forward NTT. Even sizes from `2 ^ 16` run `columnCount` column tasks and sixteen
leaf tasks; other sizes from `2 ^ 18` use at most `2 ^ logWorkers` independent array segments.
Smaller transforms use the scalar loop to avoid task and copy costs. -/
@[inline] def forwardParallel [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat := 4) : Array R :=
  if logWorkers = 0 then P.forward a else
  if ColumnsShape R a.size P.plan.domain.logN then
    Columns.transform P.plan.twiddles P.plan.domain.logN
      (columnCount P.plan.domain.logN logWorkers)
      ((Parallel.forwardPasses P.plan.domain).drop 2) false 1 a
  else if P.plan.domain.logN < 18 then P.forward a else
    let passes := Parallel.forwardPasses P.plan.domain
    let split := (logWorkers + 1) / 2
    let b := Parallel.runPasses false P.plan.twiddles (passes.take split) (P.load a)
    let c := (Parallel.chunksTask false P.plan.twiddles (passes.drop split)
      b 0 b.size logWorkers).get.flatten
    let c := if P.plan.domain.logN % 2 = 1 then
      Plan.butterflyStageDIFWithTwiddles P.plan.domain 0 (P.plan.twiddles.getD 0 #[]) c
      else c
    P.permute c

/-- Parallel inverse NTT with the same natural-order input/output and normalization. Even
sizes run the forward column transform with the inverse twiddles and scale the leaves. -/
@[inline] def inverseParallel [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat := 4) : Array R :=
  if logWorkers = 0 ∨ P.plan.inverseDomain.n ≠ P.plan.domain.n then P.inverse a else
  if ColumnsShape R a.size P.plan.domain.logN then
    Columns.transform P.plan.inverseTwiddles P.plan.domain.logN
      (columnCount P.plan.domain.logN logWorkers)
      ((Parallel.forwardPasses P.plan.inverseDomain).drop 2) true P.plan.nInv a
  else if P.plan.domain.logN < 18 then P.inverse a else
    let passes := Parallel.inversePasses P.plan.inverseDomain
    let split := passes.length - (logWorkers + 1) / 2
    let b := P.permute a
    let c := (Parallel.chunksTask true P.plan.inverseTwiddles (passes.take split)
      b 0 b.size logWorkers).get.flatten
    let c := Parallel.runPasses true P.plan.inverseTwiddles (passes.drop split) c
    let c := if P.plan.inverseDomain.logN % 2 = 1 then
      Plan.butterflyStageWithTwiddles P.plan.inverseDomain (P.plan.inverseDomain.logN - 1)
        (P.plan.inverseTwiddles.getD (P.plan.inverseDomain.logN - 1) #[]) c
      else c
    P.normalize c

/-- The complete parallel forward transform refines the proved scalar transform. -/
theorem forwardParallel_eq [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat) : P.forwardParallel a logWorkers = P.forward a := by
  unfold forwardParallel
  split
  · rfl
  split
  · rename_i h hc
    have htw : ∀ s < P.plan.domain.logN, (P.plan.twiddles.getD s #[]).size = 2 ^ s := by
      rw [P.wellFormed.2.2.1]; exact size_twiddleTable_getD _
    have hn := hc.1
    rw [transform_eq_checkedStages _ _ (columnCount P.plan.domain.logN logWorkers) false 1 a htw
      (by unfold columnCount; exact Nat.two_pow_pos _)
      (by unfold columnCount; exact Nat.pow_dvd_pow 2 (by have := hc.2.2.1; omega)) hc,
      forward, permute_eq, load,
      ite_eq_left_of_eq_true _ _ (eq_true (show a.size = P.plan.domain.n from hn))]
    rfl
  split
  · rfl
  · simp only [Parallel.chunksTask_eq, extract_self]
    have hsplit (xs : List Nat) (n : Nat) (a : Array R) :
        Parallel.runPasses false P.plan.twiddles (xs.drop n)
          (Parallel.runPasses false P.plan.twiddles (xs.take n) a) =
        Parallel.runPasses false P.plan.twiddles xs a := by
      simp only [Parallel.runPasses, ← List.foldl_append, List.take_append_drop]
    rw [hsplit, Parallel.forwardStages_eq _ _ _ (by
      simp only [load_eq, NTT.size_loadNaturalArray])]
    rfl

/-- The complete parallel inverse transform refines the proved scalar transform. -/
theorem inverseParallel_eq [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat) : P.inverseParallel a logWorkers = P.inverse a := by
  unfold inverseParallel
  split
  · rfl
  · rename_i h
    have hn : P.plan.inverseDomain.n = P.plan.domain.n :=
      not_not.mp (fun hc ↦ h (Or.inr hc))
    split
    · rename_i hc
      obtain ⟨hs, heven, h16, h36, hu⟩ := hc
      obtain ⟨hinv, hnInv, _, hitw⟩ := P.wellFormed
      have hl : P.plan.domain.inverse.logN = P.plan.domain.logN := rfl
      have htw : ∀ s < P.plan.domain.inverse.logN,
          (P.plan.inverseTwiddles.getD s #[]).size = 2 ^ s := by
        rw [hitw]; exact size_twiddleTable_getD _
      have hload : NTT.loadNaturalArray P.plan.domain.inverse a = a := by
        apply Array.ext
        · rw [NTT.size_loadNaturalArray, hs]; rfl
        · intro i hi _
          rw [NTT.getElem_loadNaturalArray, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem (by assumption), Option.getD_some]
      have key := transform_eq_checkedStages P.plan.domain.inverse P.plan.inverseTwiddles
        (columnCount P.plan.domain.logN logWorkers) true P.plan.nInv a htw
        (by unfold columnCount; exact Nat.two_pow_pos _)
        (by unfold columnCount; rw [hl]; exact Nat.pow_dvd_pow 2 (by omega))
        ⟨by rw [hl]; exact hs, by rw [hl]; exact heven,
          by omega, by omega, by rw [hl]; exact hu⟩
      rw [hinv]
      refine key.trans ?_
      rw [inverse_eq, Plan.inverseImpl_correct _ P.wellFormed, Plan.checkedStages_eq, hitw]
      conv_lhs => rw [← hload]
      rw [Plan.runStagesDIFRadix4WithTwiddles_correct]
      apply Array.ext
      · simp only [Array.size_ofFn, NTT.Inverse.size_inverseSpec]; rfl
      · intro i hi _
        simp only [Array.getElem_ofFn, Columns.scaleBy, ↓reduceIte, NTT.Inverse.inverseSpec,
          NTT.Transform.bitRevPermute, hnInv]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
        simp only [NTT.Domain.n, NTT.Transform.bitRevNat_lt, ↓reduceDIte, Option.getD_some]
        simp only [Array.size_ofFn] at hi
        have hi' : i < 2 ^ P.plan.domain.inverse.logN := by rw [hl]; exact hi
        rw [NTT.Transform.bitRevNat_involutive _ _ hi', NTT.Forward.forwardSpec,
          Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
        simp only [NTT.Domain.n, hi', ↓reduceDIte, Option.getD_some]
        rfl
    split
    · rfl
    simp only [Parallel.chunksTask_eq, extract_self]
    have hsplit (xs : List Nat) (n : Nat) (a : Array R) :
        Parallel.runPasses true P.plan.inverseTwiddles (xs.drop n)
          (Parallel.runPasses true P.plan.inverseTwiddles (xs.take n) a) =
        Parallel.runPasses true P.plan.inverseTwiddles xs a := by
      simp only [Parallel.runPasses, ← List.foldl_append, List.take_append_drop]
    rw [hsplit, Parallel.inverseStages_eq _ _ _ (by
      simp only [permute_eq_map, Array.size_map, order_size, hn])]
    rfl

end CompPoly.CPolynomial.NTTFast.NaturalPlan
