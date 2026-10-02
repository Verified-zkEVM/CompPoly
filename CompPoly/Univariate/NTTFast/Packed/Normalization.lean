/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Correctness.Basic
public import CompPoly.Univariate.NTTFast.Packed.StageCorrectness

/-! # Moving leaf normalization past independent later blocks -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Writing outside a normalized segment commutes with its normalization. -/
theorem scaleSegment_set_outside [Field R] (a : Array R) (base count : Nat) (factor : R)
    (i : Nat) (x : R) (hout : ¬(base ≤ i ∧ i < base + count)) :
    scaleSegment (a.setIfInBounds i x) base count factor =
      (scaleSegment a base count factor).setIfInBounds i x := by
  by_cases hi : i < a.size
  · apply array_eq_of_getD _ _ (0 : R)
    · simp only [size_scaleSegment, Array.size_setIfInBounds]
    · intro k
      rw [getD_scaleSegment, getD_setIfInBounds _ _ _ _ _ hi,
        getD_setIfInBounds _ _ _ _ _ (by rw [size_scaleSegment]; exact hi),
        getD_scaleSegment]
      by_cases hk : k = i
      · subst k
        simp only [hout, ite_false, ite_true]
      · simp only [hk, ite_false]
  · simp only [Array.setIfInBounds, hi, size_scaleSegment, ↓reduceDIte]

/-- A DIF loop to the right of a normalized segment neither reads nor writes that segment. -/
theorem butterflyDIFInner_comm_scaleLeft [Field R] (tw : Array R)
    (limit j i0 i1 base count : Nat) (factor : R) (a : Array R)
    (h0 : base + count ≤ i0) (h1 : base + count ≤ i1) :
    Plan.butterflyDIFInner tw limit j i0 i1 (scaleSegment a base count factor) =
      scaleSegment (Plan.butterflyDIFInner tw limit j i0 i1 a) base count factor := by
  conv_lhs => rw [Plan.butterflyDIFInner]
  conv_rhs => rw [Plan.butterflyDIFInner]
  split
  · simp only [getD_scaleSegment, show ¬(base ≤ i0 ∧ i0 < base + count) by omega,
      show ¬(base ≤ i1 ∧ i1 < base + count) by omega, ite_false,
      Array.set!_eq_setIfInBounds]
    rw [← scaleSegment_set_outside _ _ _ _ i0 _ (by omega),
      ← scaleSegment_set_outside _ _ _ _ i1 _ (by omega)]
    exact butterflyDIFInner_comm_scaleLeft tw limit (j + 1) (i0 + 1) (i1 + 1)
      base count factor _ (by omega) (by omega)
  · rfl
termination_by limit - j
decreasing_by omega

/-- A complete local layer commutes with normalization of an earlier segment. -/
theorem localLayer_comm_scaleLeft [Field R] (tw : Array R) (half blocks first base count : Nat)
    (factor : R) (a : Array R) (hsep : base + count ≤ first) :
    localLayer tw half blocks first (scaleSegment a base count factor) =
      scaleSegment (localLayer tw half blocks first a) base count factor := by
  unfold localLayer
  symm
  apply Plan.foldl_commute
  intro i hi x
  symm
  exact butterflyDIFInner_comm_scaleLeft tw half 0 _ _ base count factor x
    (by omega) (by omega)

/-- All four local final layers commute with normalization of an earlier segment. -/
theorem leaf16Stages_comm_scaleLeft [Field R] (t3 t2 t1 : Array R)
    (first base count : Nat) (factor : R) (a : Array R) (hsep : base + count ≤ first) :
    Expressions.leaf16Stages t3 t2 t1 (scaleSegment a base count factor) first =
      scaleSegment (Expressions.leaf16Stages t3 t2 t1 a first) base count factor := by
  simp only [Expressions.leaf16Stages, layer16_1_eq_localLayer, layer16_2_eq_localLayer,
    layer16_4_eq_localLayer, layer16_8_eq_localLayer]
  rw [localLayer_comm_scaleLeft _ _ _ _ _ _ _ _ hsep,
    localLayer_comm_scaleLeft _ _ _ _ _ _ _ _ hsep,
    localLayer_comm_scaleLeft _ _ _ _ _ _ _ _ hsep,
    localLayer_comm_scaleLeft _ _ _ _ _ _ _ _ hsep]

/-- Each finished leaf's normalization can be postponed until after all leaves. -/
theorem fold_leafBlock_scaled [Field R] (t3 t2 t1 : Array R) (blocks : Nat) (factor : R)
    (a : Array R) :
    (List.range blocks).foldl (fun b block ↦
      leafBlock t3 t2 t1 (block * 16) factor true b) a =
      (List.range blocks).foldl (fun b block ↦ scaleSegment b (block * 16) 16 factor)
        ((List.range blocks).foldl (fun b block ↦
          Expressions.leaf16Stages t3 t2 t1 b (block * 16)) a) := by
  simp only [leafBlock, ite_true]
  apply Plan.foldl_pair
  intro i j hij hj x
  exact leaf16Stages_comm_scaleLeft _ _ _ _ _ _ _ _ (by omega)

/-- Normalizing successive blocks changes each completed coordinate exactly once. -/
theorem getD_fold_scaleSegments [Field R] (a : Array R) (blocks : Nat) (factor : R) (k : Nat) :
    ((List.range blocks).foldl (fun b block ↦
      scaleSegment b (block * 16) 16 factor) a).getD k 0 =
      if k < blocks * 16 then factor * a.getD k 0 else a.getD k 0 := by
  induction blocks with
  | zero => simp only [List.range_zero, List.foldl_nil, Nat.zero_mul, Nat.not_lt_zero, ite_false]
  | succ blocks ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      getD_scaleSegment, ih]
    by_cases hlo : k < blocks * 16
    · simp (disch := omega) only [hlo, ite_true, ite_eq_right, ite_eq_left]
    · by_cases hhi : k < (blocks + 1) * 16
      · simp (disch := omega) only [hlo, hhi, ite_false, ite_true, ite_eq_left]
      · simp (disch := omega) only [hlo, hhi, ite_false, ite_eq_right]

/-- Once every block is complete, the traversal equals whole-array normalization. -/
theorem fold_scaleSegments_eq_map [Field R] (a : Array R) (blocks : Nat) (factor : R)
    (hs : a.size = blocks * 16) :
    (List.range blocks).foldl (fun b block ↦ scaleSegment b (block * 16) 16 factor) a =
      a.map (fun x ↦ factor * x) := by
  apply array_eq_of_getD _ _ (0 : R)
  · rw [Array.size_map]
    exact foldl_invariant (List.range blocks) (fun b : Array R ↦ b.size = a.size)
      _ (fun i hi b hb ↦ by simpa only [size_scaleSegment] using hb) a rfl
  · intro k
    rw [getD_fold_scaleSegments, getD_scaleMap]
    by_cases hk : k < blocks * 16
    · rw [ite_eq_left hk]
    · rw [ite_eq_right hk]
      have ho : a[k]? = none := Array.getElem?_eq_none (by omega)
      simp only [Array.getD_eq_getD_getElem?, ho, Option.getD_none, MulZeroClass.mul_zero]

/-- Fused normalized leaves compute the ordinary final stages, then whole-array normalization. -/
theorem fold_leafBlock_scaled_eq_map [Field R] (t3 t2 t1 : Array R) (blocks : Nat) (factor : R)
    (a : Array R) (hs : a.size = blocks * 16) :
    (List.range blocks).foldl (fun b block ↦ leafBlock t3 t2 t1 (block * 16) factor true b) a =
      ((List.range blocks).foldl (fun b block ↦
        Expressions.leaf16Stages t3 t2 t1 b (block * 16)) a).map (fun x ↦ factor * x) := by
  rw [fold_leafBlock_scaled]
  apply fold_scaleSegments_eq_map
  exact foldl_invariant (List.range blocks) (fun b : Array R ↦ b.size = blocks * 16)
    _ (fun i hi b hb ↦ by simpa only [size_leaf16Stages] using hb) a hs

/-- The fused inverse schedule normalizes the same unnormalized transform's output. -/
theorem fieldStages_normalized_eq_map (logN : Nat) (tw : Array (Array KoalaBear.Fast.Field))
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field)
    (hlog : 4 ≤ logN) (hmod : logN % 2 = 0) (hs : a.size = 2 ^ logN) :
    fieldStages logN tw a factor true =
      (fieldStages logN tw a factor false).map (fun x ↦ factor * x) := by
  have hf : (decide (logN ≥ 4) && logN % 2 == 0) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hlog, hmod⟩
  have hd : 16 ∣ 2 ^ logN := by simpa using Nat.pow_dvd_pow 2 hlog
  have hdiv := Nat.div_mul_cancel hd
  simp only [fieldStages]
  simp only [hf, ite_true]
  simp only [hmod, Nat.zero_ne_one, ite_false]
  rw [fold_leafBlock_scaled_eq_map]
  · simp only [leafBlock, Bool.false_eq_true, ite_false]
  · have hshape :
        ((List.range (logN / 2 - 2)).foldl (fun b pass ↦ fieldPass logN tw pass b) a).size =
          2 ^ logN :=
      foldl_invariant (List.range (logN / 2 - 2)) (fun b ↦ b.size = 2 ^ logN)
        _ (fun i hi b hb ↦ by simpa only [size_fieldPass] using hb) a hs
    omega

/-- A normalization request is implemented by fused leaves only when their four layers exist. -/
def ValidNormalization (logN : Nat) (normalize : Bool) : Prop :=
  normalize = true → 4 ≤ logN ∧ logN % 2 = 0

/-- The complete packed sequential pipeline implements the verified plan and its normalization. -/
theorem Native.stages_correct (D : NTT.Domain KoalaBear.Fast.Field)
    (a : Array KoalaBear.Fast.Field) (factor : KoalaBear.Fast.Field) (normalize : Bool)
    (hs : a.size = D.n) (hu : 4 * D.n < USize.size)
    (hn : ValidNormalization D.logN normalize) :
    Native.stages D.logN ((Plan.twiddleTable D).map packFields) (packFields a)
      factor.val normalize =
      packFields (if normalize then
        (Plan.runStagesDIFRadix4WithTwiddles D (Plan.twiddleTable D) a).map (fun x ↦ factor * x)
      else Plan.runStagesDIFRadix4WithTwiddles D (Plan.twiddleTable D) a) := by
  obtain ⟨htw, hone⟩ := twiddleTable_invariants D
  rw [Native.stages_packFields _ _ _ _ _ htw hone hs hu]
  cases normalize with
  | false =>
    rw [fieldStages_unscaled_eq_all _ _ _ _ htw hone hs, allFieldStages_eq_plan D _ a htw hone]
    rfl
  | true =>
    obtain ⟨hlog, hmod⟩ := hn rfl
    rw [fieldStages_normalized_eq_map _ _ _ _ hlog hmod hs,
      fieldStages_unscaled_eq_all _ _ _ _ htw hone hs, allFieldStages_eq_plan D _ a htw hone]
    rfl

end CompPoly.CPolynomial.NTTFast.Packed
