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

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.NaturalPlan
variable {R : Type*}

/-- The column-parallel transform applies to an exactly sized input of at least `2 ^ 15`
elements; smaller transforms run as one leaf, without tasks or copies. -/
def ColumnsShape (R : Type*) [PackedRepr R] (n logN : Nat) : Prop :=
  n = 2 ^ logN ∧ 15 ≤ logN ∧ logN ≤ 36 ∧ PackedRepr.width R * (2 ^ logN + 256) ≤ USize.size

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

/-- The pair butterflies of an odd transform are its last radix-two stage. -/
theorem lastPair_eq [Field R] (D : NTT.Domain R) (tw0 a : Array R) (ha : a.size = D.n) :
    Columns.lastPair tw0 a = Plan.butterflyStageDIFWithTwiddles D 0 tw0 a := by
  simp only [Columns.lastPair, Plan.butterflyStageDIFWithTwiddles, ha, Nat.zero_add,
    Nat.pow_one, Nat.pow_zero]

/-- The column transform computes the scalar forward stages of a domain, in natural order. -/
theorem transform_eq_checkedStages [Field R] [DecidableEq R] [PackedRepr R] (D : NTT.Domain R)
    (tw : Array (Array R)) (S : Nat) (scale : Bool) (f : R) (a : Array R)
    (htw : ∀ s < D.logN, (tw.getD s #[]).size = 2 ^ s) (hS : 0 < S)
    (hdiv : S ∣ 2 ^ (D.logN - 4)) (hshape : ColumnsShape R a.size D.logN) :
    Columns.transform tw D.logN S ((Parallel.forwardPasses D).drop 2) scale f a =
      Array.ofFn (n := 2 ^ D.logN) fun i ↦ Columns.scaleBy scale f
        ((Plan.checkedStages D tw a).getD (NTT.Transform.bitRevNat D.logN i) 0) := by
  obtain ⟨hn, h15, h36, hu⟩ := hshape
  rw [Columns.transform_eq tw D.logN S _ scale f a (by omega) h36 hn htw hu hS hdiv,
    ← Parallel.forwardStages_eq D tw a hn]
  · unfold Columns.leafPasses
    rw [runPasses_topPasses D tw a (by omega)]
    by_cases ho : D.logN % 2 = 1
    · simp only [ho, beq_self_eq_true, ↓reduceIte]
      rw [lastPair_eq D _ _ (by rw [Parallel.size_runPasses, hn]; rfl)]
    · simp only [ho, beq_iff_eq, ↓reduceIte]
  · intro low hlow
    simp only [Parallel.forwardPasses, List.mem_drop_iff_getElem, List.length_map,
      List.length_range, List.getElem_map, List.getElem_range] at hlow
    obtain ⟨i, hi, rfl⟩ := hlow
    rw [show 4 * 2 ^ (D.logN - 1 - 2 * (2 + i) - 1) = 2 ^ (D.logN - 1 - 2 * (2 + i) - 1 + 2) by
      rw [Nat.pow_add]; ring]
    exact Nat.pow_dvd_pow 2 (by omega)

/-- Parallel forward NTT: from `2 ^ 15` elements, `columnCount` column tasks run the top two
radix-four passes and sixteen leaf tasks the remaining layers; smaller transforms, and a single
worker, run the sequential transform as one leaf. -/
@[inline] def forwardParallel [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat := 4) : Array R :=
  if logWorkers ≠ 0 ∧ ColumnsShape R a.size P.plan.domain.logN then
    Columns.transform P.plan.twiddles P.plan.domain.logN
      (columnCount P.plan.domain.logN logWorkers)
      ((Parallel.forwardPasses P.plan.domain).drop 2) false 1 a
  else P.forward a

/-- Parallel inverse NTT with the same shapes; the column transform runs with the inverse
twiddles and scales the leaves. -/
@[inline] def inverseParallel [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat := 4) : Array R :=
  if logWorkers ≠ 0 ∧ P.plan.inverseDomain.n = P.plan.domain.n ∧
      ColumnsShape R a.size P.plan.domain.logN then
    Columns.transform P.plan.inverseTwiddles P.plan.domain.logN
      (columnCount P.plan.domain.logN logWorkers)
      ((Parallel.forwardPasses P.plan.inverseDomain).drop 2) true P.plan.nInv a
  else P.inverse a

/-- The complete parallel forward transform refines the proved scalar transform. -/
theorem forwardParallel_eq [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat) : P.forwardParallel a logWorkers = P.forward a := by
  unfold forwardParallel
  split
  · rename_i h
    obtain ⟨_, hc⟩ := h
    have htw : ∀ s < P.plan.domain.logN, (P.plan.twiddles.getD s #[]).size = 2 ^ s := by
      rw [P.wellFormed.2.2.1]; exact size_twiddleTable_getD _
    have hn := hc.1
    rw [transform_eq_checkedStages _ _ (columnCount P.plan.domain.logN logWorkers) false 1 a htw
      (by unfold columnCount; exact Nat.two_pow_pos _)
      (by unfold columnCount; exact Nat.pow_dvd_pow 2 (by have := hc.2.1; omega)) hc,
      forward, permute_eq, load,
      ite_eq_left_of_eq_true _ _ (eq_true (show a.size = P.plan.domain.n from hn))]
    rfl
  · rfl

/-- The complete parallel inverse transform refines the proved scalar transform. -/
theorem inverseParallel_eq [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat) : P.inverseParallel a logWorkers = P.inverse a := by
  unfold inverseParallel
  split
  · rename_i h
    obtain ⟨_, hn, hc⟩ := h
    obtain ⟨hs, h15, h36, hu⟩ := hc
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
      ⟨by rw [hl]; exact hs, by omega, by omega, by rw [hl]; exact hu⟩
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
  · rfl

/-- Parallel forward NTT of packed elements (`PackedRepr.encode`), with the shapes of
`forwardParallel`: the column transform runs directly on the packed buffer, and one leaf
unpacks, transforms and packs. -/
@[inline] def forwardPacked [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : ByteArray) (logWorkers : Nat := 4) : ByteArray :=
  if logWorkers ≠ 0 ∧
      ColumnsShape R (a.size / PackedRepr.width R) P.plan.domain.logN then
    Columns.transformPacked P.plan.twiddles P.plan.domain.logN
      (columnCount P.plan.domain.logN logWorkers)
      ((Parallel.forwardPasses P.plan.domain).drop 2) false 1 a
  else Columns.encodeAll (P.forward (Columns.decodeAll a))

/-- Parallel inverse NTT of packed elements, with the shapes of `inverseParallel`. -/
@[inline] def inversePacked [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : ByteArray) (logWorkers : Nat := 4) : ByteArray :=
  if logWorkers ≠ 0 ∧ P.plan.inverseDomain.n = P.plan.domain.n ∧
      ColumnsShape R (a.size / PackedRepr.width R) P.plan.domain.logN then
    Columns.transformPacked P.plan.inverseTwiddles P.plan.domain.logN
      (columnCount P.plan.domain.logN logWorkers)
      ((Parallel.forwardPasses P.plan.inverseDomain).drop 2) true P.plan.nInv a
  else Columns.encodeAll (P.inverse (Columns.decodeAll a))

private theorem shape_bounds [PackedRepr R] (n logN : Nat) (h : ColumnsShape R n logN) :
    PackedRepr.width R * n < USize.size ∧
      PackedRepr.width R * (16 * 2 ^ (logN - 4)) < USize.size ∧ 16 ∣ 2 ^ (logN - 4) := by
  obtain ⟨hn, h15, _, hu⟩ := h
  have hw := PackedRepr.width_pos (R := R)
  have hp : 16 * 2 ^ (logN - 4) = 2 ^ logN := by
    rw [show logN = 4 + (logN - 4) by omega, Nat.pow_add, Nat.add_sub_cancel_left]
  have hlt : PackedRepr.width R * 2 ^ logN < PackedRepr.width R * (2 ^ logN + 256) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hw
  refine ⟨by rw [hn]; omega, by rw [hp]; omega, ?_⟩
  exact Nat.pow_dvd_pow 2 (show 4 ≤ logN - 4 by omega)

/-- The packed parallel forward transform packs the proved scalar transform. -/
theorem forwardPacked_eq [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat) :
    P.forwardPacked (PackedRepr.encode a) logWorkers = PackedRepr.encode (P.forward a) := by
  have hdiv : (PackedRepr.encode a).size / PackedRepr.width R = a.size := by
    rw [PackedRepr.size_encode, Nat.mul_div_cancel_left _ PackedRepr.width_pos]
  unfold forwardPacked
  rw [hdiv]
  split
  · rename_i h
    obtain ⟨hw, hc⟩ := h
    have hb := shape_bounds a.size _ hc
    rw [Columns.transformPacked_encode _ _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2, ← forwardParallel_eq P a]
    unfold forwardParallel
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hw, hc⟩)]
  · rw [Columns.decodeAll_encode, Columns.encodeAll_eq]

/-- The packed parallel inverse transform packs the proved scalar inverse. -/
theorem inversePacked_eq [Field R] [DecidableEq R] [PackedRepr R] (P : NaturalPlan R)
    (a : Array R) (logWorkers : Nat) :
    P.inversePacked (PackedRepr.encode a) logWorkers = PackedRepr.encode (P.inverse a) := by
  have hdiv : (PackedRepr.encode a).size / PackedRepr.width R = a.size := by
    rw [PackedRepr.size_encode, Nat.mul_div_cancel_left _ PackedRepr.width_pos]
  unfold inversePacked
  rw [hdiv]
  split
  · rename_i h
    obtain ⟨hw, hn, hc⟩ := h
    have hb := shape_bounds a.size _ hc
    rw [Columns.transformPacked_encode _ _ _ _ _ _ _ hb.1 hb.2.1 hb.2.2, ← inverseParallel_eq P a]
    unfold inverseParallel
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hw, hn, hc⟩)]
  · rw [Columns.decodeAll_encode, Columns.encodeAll_eq]

end CompPoly.CPolynomial.NTTFast.NaturalPlan
