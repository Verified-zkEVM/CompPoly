/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Correctness
import CompPoly.Univariate.Roots.RootProduct
import CompPoly.Univariate.Roots.SmoothSubgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Smooth Multiplicative-Subgroup Splitter Correctness

Correctness theorems for the smooth cyclic splitter, including executable
contracts and adapter theorems.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Field-root products satisfy the generic smooth-splitter input predicate. -/
theorem finiteFieldRootProductWith_smoothSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (generator : F) (schedule : Array Nat)
    {p : CPolynomial F} (hp : p ≠ 0) :
    smoothSplitterInput ctx.q generator schedule
      (finiteFieldRootProductWith M D ctx p) := by
  constructor
  · exact CPolynomial.Roots.FiniteField.finiteFieldRootProductWith_ne_zero_of_ne_zero
      M D ctx hp
  · intro a _ha
    exact ctx.frobenius_fixed a

/-- Soundness theorem for a smooth context adapted to the splitter interface. -/
theorem smoothLinearFactorProductSplitterWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmoothCyclicRootContext F) {q : Nat} {p factor : CPolynomial F}
    (h : factor ∈
      ((smoothLinearFactorProductSplitterWith M D ctx).splitLinearFactors q p).toList) :
    IsLinearFactor factor := by
  exact (smoothLinearFactorProductSplitterWith M D ctx).sound q p factor h

/-- Completeness theorem for a smooth context adapted to the splitter interface. -/
theorem smoothLinearFactorProductSplitterWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmoothCyclicRootContext F) {q : Nat} {p : CPolynomial F} {a : F}
    (hvalid : (smoothLinearFactorProductSplitterWith M D ctx).validInput q p)
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          ((smoothLinearFactorProductSplitterWith M D ctx).splitLinearFactors q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  exact (smoothLinearFactorProductSplitterWith M D ctx).complete q p a hvalid hp hroot

/-- Zero-root extraction is sound for the emitted `X` factor. -/
theorem smooth_zero_root_factor_sound {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    IsLinearRootFactorCandidate (CPolynomial.linearFactor (0 : F)) (0 : F) := by
  have hC0 : CPolynomial.C (0 : F) = 0 := by
    apply (CPolynomial.eq_iff_coeff).2
    intro i
    simp
  rw [CPolynomial.linearFactor, neg_zero, hC0, CPolynomial.zero_add]
  simp [IsLinearRootFactorCandidate, IsLinearFactor, CPolynomial.X, CPolynomial.Raw.X,
    CPolynomial.coeff, CPolynomial.Raw.coeff]

/-- Leaf extraction emits only represented nonconstant linear factors. -/
private theorem linearFactorsFromLeafValues_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (points values : Array F) {factor : CPolynomial F}
    (h : factor ∈ (linearFactorsFromLeafValues points values).toList) :
    IsLinearFactor factor := by
  unfold linearFactorsFromLeafValues at h
  rw [Array.foldl_zipIdx_eq_foldl_toList_zipIdx] at h
  have haux : ∀ (xs : List (F × Nat)) (acc : Array (CPolynomial F)),
      (∀ factor, factor ∈ acc.toList → IsLinearFactor factor) →
        factor ∈ (xs.foldl
          (fun factors x ↦
            if values.getD x.2 1 == 0 then
              factors.push (CPolynomial.linearFactor x.1)
            else
              factors) acc).toList →
          IsLinearFactor factor := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc hmem
        exact hacc factor hmem
    | cons x xs ih =>
        intro acc hacc hmem
        simp only [List.foldl_cons] at hmem
        refine ih (if values.getD x.2 1 == 0 then
              acc.push (CPolynomial.linearFactor x.1)
            else
              acc) ?_ hmem
        intro fac hfac
        by_cases hcond : (values.getD x.2 1 == 0) = true
        · rw [if_pos hcond] at hfac
          by_cases hlast : fac = CPolynomial.linearFactor x.1
          · rw [hlast]
            exact linearFactor_isLinearFactor x.1
          · apply hacc
            simpa [hlast] using hfac
        · rw [if_neg hcond] at hfac
          exact hacc fac hfac
  exact haux points.toList.zipIdx #[] (by simp) h

/-- A point whose batch value is zero contributes its explicit linear factor. -/
private theorem mem_linearFactorsFromLeafValues_of_get_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (points values : Array F) {idx : Nat} (hidx : idx < points.size)
    (hval : values.getD idx 1 = 0) :
    CPolynomial.linearFactor points[idx] ∈
      (linearFactorsFromLeafValues points values).toList := by
  unfold linearFactorsFromLeafValues
  rw [Array.foldl_zipIdx_eq_foldl_toList_zipIdx]
  have htarget : (points[idx], idx) ∈ points.toList.zipIdx := by
    have hex : ∃ x ∈ points.toList.zipIdx, x = (points[idx], idx) := by
      rw [List.exists_mem_zipIdx']
      refine ⟨idx, ?_, ?_⟩
      · simpa using hidx
      · simp [Array.getElem_toList]
    rcases hex with ⟨x, hxmem, hxeq⟩
    simpa [hxeq] using hxmem
  have haux : ∀ (xs : List (F × Nat)) (acc : Array (CPolynomial F)),
      CPolynomial.linearFactor points[idx] ∈ acc.toList ∨ (points[idx], idx) ∈ xs →
        CPolynomial.linearFactor points[idx] ∈ (xs.foldl
          (fun factors x ↦
            if values.getD x.2 1 == 0 then
              factors.push (CPolynomial.linearFactor x.1)
            else
              factors) acc).toList := by
    intro xs
    induction xs with
    | nil =>
        intro acc h
        simpa using h
    | cons x xs ih =>
        intro acc h
        simp only [List.foldl_cons]
        apply ih
        rcases h with hacc | hx
        · left
          by_cases hcond : (values.getD x.2 1 == 0) = true
          · rw [if_pos hcond]
            simp [hacc]
          · rw [if_neg hcond]
            exact hacc
        · simp at hx
          rcases hx with hx | hx
          · subst x
            left
            have hbeq : (values.getD idx 1 == 0) = true := by
              simp [hval]
            rw [if_pos hbeq]
            simp
          · right
            exact hx
  exact haux points.toList.zipIdx #[] (Or.inr htarget)

/-- Smooth leaf extraction emits only represented nonconstant linear factors. -/
private theorem smoothLeafLinearFactors_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (E : BatchEvalContext F) (alpha gamma : F) (order : Nat) (p : CPolynomial F)
    {factor : CPolynomial F}
    (h : factor ∈ (smoothLeafLinearFactors E alpha gamma order p).toList) :
    IsLinearFactor factor := by
  unfold smoothLeafLinearFactors at h
  exact linearFactorsFromLeafValues_sound _ _ h

/-- Smooth leaf extraction is complete for roots in the enumerated coset. -/
theorem smoothLeafLinearFactors_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (E : BatchEvalContext F) {alpha gamma a : F} {order : Nat} {p : CPolynomial F}
    (hcoset : ∃ k : Nat, k < order ∧ a = alpha * gamma ^ k)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (smoothLeafLinearFactors E alpha gamma order p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  rcases hcoset with ⟨k, hk, ha⟩
  refine ⟨CPolynomial.linearFactor a, ?_, linearFactor_isRootFactorCandidate a⟩
  unfold smoothLeafLinearFactors
  let points := smoothCosetPoints alpha gamma order
  have hsize : k < points.size := by
    simp [points, smoothCosetPoints]
    exact hk
  have hpoint : points[k] = a := by
    simp [points, smoothCosetPoints, ha]
  have hval : (E.evalBatchWith p points).getD k 1 = 0 := by
    rw [E.correct]
    unfold CPolynomial.evalBatch
    rw [Array.getD_map_of_lt points (fun x ↦ CPolynomial.eval x p) 1 hsize]
    rw [hpoint]
    exact hroot
  have hmem := mem_linearFactorsFromLeafValues_of_get_eq_zero points (E.evalBatchWith p points)
    hsize hval
  simpa [hpoint] using hmem

/-- Schedule-driven smooth coset recursion emits only represented nonconstant linear factors. -/
theorem smoothCosetLinearFactorsWithSchedule_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) :
    ∀ (schedule : List Nat) (order : Nat) (alpha gamma : F) (p factor : CPolynomial F),
      factor ∈
          (smoothCosetLinearFactorsWithSchedule M D E schedule order alpha gamma p).toList →
        IsLinearFactor factor := by
  intro schedule
  induction schedule with
  | nil =>
      intro order alpha gamma p factor h
      unfold smoothCosetLinearFactorsWithSchedule at h
      by_cases hzero : (CPolynomial.monicNormalize p == 0 ||
          CPolynomial.monicNormalize p == 1) = true
      · rw [if_pos hzero] at h
        simp at h
      · rw [if_neg hzero] at h
        by_cases hlin : isRepresentedLinearFactor (CPolynomial.monicNormalize p) = true
        · rw [if_pos hlin] at h
          simp at h
          rcases h with rfl
          exact isRepresentedLinearFactor_sound hlin
        · rw [if_neg hlin] at h
          exact smoothLeafLinearFactors_sound E alpha gamma order (CPolynomial.monicNormalize p) h
  | cons ell rest ih =>
      intro order alpha gamma p factor h
      unfold smoothCosetLinearFactorsWithSchedule at h
      by_cases hzero : (CPolynomial.monicNormalize p == 0 ||
          CPolynomial.monicNormalize p == 1) = true
      · rw [if_pos hzero] at h
        simp at h
      · rw [if_neg hzero] at h
        by_cases hlin : isRepresentedLinearFactor (CPolynomial.monicNormalize p) = true
        · rw [if_pos hlin] at h
          simp at h
          rcases h with rfl
          exact isRepresentedLinearFactor_sound hlin
        · rw [if_neg hlin] at h
          by_cases hellsmall : ell ≤ 1
          · rw [if_pos hellsmall] at h
            exact ih order alpha gamma (CPolynomial.monicNormalize p) factor h
          · rw [if_neg hellsmall] at h
            by_cases helleq : ell = order
            · rw [if_pos helleq] at h
              exact smoothLeafLinearFactors_sound E alpha gamma order
                (CPolynomial.monicNormalize p) h
            · rw [if_neg helleq] at h
              let childOrder := order / ell
              let tau := gamma ^ childOrder
              let xPow := xPowModWith M D (CPolynomial.monicNormalize p) childOrder
              have hfold : ∀ (js : List Nat) (acc : Array (CPolynomial F)),
                  (∀ factor, factor ∈ acc.toList → IsLinearFactor factor) →
                    factor ∈ (js.foldl
                      (fun factors j ↦
                        let beta := alpha ^ childOrder * tau ^ j
                        let witness := xPow - CPolynomial.C beta
                        let child := CPolynomial.monicNormalize
                          (CPolynomial.gcdMonic (CPolynomial.monicNormalize p) witness)
                        if child == 0 || child == 1 then
                          factors
                        else
                          factors ++ smoothCosetLinearFactorsWithSchedule M D E rest childOrder
                            (alpha * gamma ^ j) (gamma ^ ell) child) acc).toList →
                      IsLinearFactor factor := by
                intro js
                induction js with
                | nil =>
                    intro acc hacc hmem
                    exact hacc factor hmem
                | cons j js ihjs =>
                    intro acc hacc hmem
                    simp only [List.foldl_cons] at hmem
                    let beta := alpha ^ childOrder * tau ^ j
                    let witness := xPow - CPolynomial.C beta
                    let child := CPolynomial.monicNormalize
                      (CPolynomial.gcdMonic (CPolynomial.monicNormalize p) witness)
                    refine ihjs
                      (if child == 0 || child == 1 then
                          acc
                        else
                          acc ++ smoothCosetLinearFactorsWithSchedule M D E rest childOrder
                            (alpha * gamma ^ j) (gamma ^ ell) child) ?_ hmem
                    intro fac hfac
                    by_cases hskip : (child == 0 || child == 1) = true
                    · rw [if_pos hskip] at hfac
                      exact hacc fac hfac
                    · rw [if_neg hskip] at hfac
                      simp at hfac
                      rcases hfac with haccmem | hrec
                      · exact hacc fac (by simpa using haccmem)
                      · exact ih childOrder (alpha * gamma ^ j) (gamma ^ ell) child fac
                          (by simpa using hrec)
              exact hfold (List.range ell) #[] (by simp) h

/-- The top-level smooth splitter emits only represented nonconstant linear factors. -/
theorem smoothLinearFactorsAlgorithmWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) (q : Nat) (generator : F) (schedule : Array Nat)
    {p factor : CPolynomial F}
    (h : factor ∈ (smoothLinearFactorsAlgorithmWith M D E q generator schedule p).toList) :
    IsLinearFactor factor := by
  unfold smoothLinearFactorsAlgorithmWith at h
  by_cases hzero : (CPolynomial.monicNormalize p == 0 ||
      CPolynomial.monicNormalize p == 1) = true
  · rw [if_pos hzero] at h
    simp at h
  · rw [if_neg hzero] at h
    by_cases hconst : (((CPolynomial.monicNormalize p).coeff 0 == 0) = true)
    · rw [if_pos hconst] at h
      unfold smoothNonzeroLinearFactorsWith at h
      simp at h
      rcases h with hzeroFactor | hnonzero
      · rcases hzeroFactor with rfl
        exact linearFactor_isLinearFactor 0
      · exact smoothCosetLinearFactorsWithSchedule_sound M D E schedule.toList (q - 1)
          1 generator (CPolynomial.monicNormalize (CPolynomial.divX (CPolynomial.monicNormalize p)))
          factor (by simpa using hnonzero)
    · rw [if_neg hconst] at h
      unfold smoothNonzeroLinearFactorsWith at h
      simp at h
      exact smoothCosetLinearFactorsWithSchedule_sound M D E schedule.toList (q - 1)
        1 generator (CPolynomial.monicNormalize p) factor (by simpa using h)

/-- A smooth coset split maps the residue class `k % ell` to the child-coset equation. -/
theorem smooth_coset_split_root_partition_mod {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {alpha gamma : F} {order ell k : Nat}
    (hgamma_pow : gamma ^ order = 1)
    (hell_dvd : ell ∣ order) :
    (alpha * gamma ^ k) ^ (order / ell) =
      alpha ^ (order / ell) * (gamma ^ (order / ell)) ^ (k % ell) := by
  let n := order / ell
  have hellmul : ell * n = order := by
    dsimp [n]
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hell_dvd
  have hgamma_reduce : gamma ^ (k * n) = gamma ^ ((k % ell) * n) := by
    have hkdecomp : k = ell * (k / ell) + k % ell := (Nat.div_add_mod k ell).symm
    calc
      gamma ^ (k * n) = gamma ^ ((ell * (k / ell) + k % ell) * n) := by
        rw [← hkdecomp]
      _ = gamma ^ ((k / ell) * order + (k % ell) * n) := by
        congr 1
        have hterm : (ell * (k / ell)) * n = (k / ell) * order := by
          calc
            (ell * (k / ell)) * n = (k / ell) * (ell * n) := by ac_rfl
            _ = (k / ell) * order := by rw [hellmul]
        rw [Nat.add_mul, hterm]
      _ = gamma ^ ((k % ell) * n) := by
        rw [pow_add]
        rw [Nat.mul_comm (k / ell) order]
        rw [pow_mul, hgamma_pow]
        simp
  calc
    (alpha * gamma ^ k) ^ n = alpha ^ n * (gamma ^ k) ^ n := by rw [mul_pow]
    _ = alpha ^ n * gamma ^ (k * n) := by rw [pow_mul]
    _ = alpha ^ n * gamma ^ ((k % ell) * n) := by rw [hgamma_reduce]
    _ = alpha ^ n * gamma ^ (n * (k % ell)) := by rw [Nat.mul_comm (k % ell) n]
    _ = alpha ^ n * (gamma ^ n) ^ (k % ell) := by rw [pow_mul]

/-- A smooth coset split partitions roots according to the child-coset equation. -/
theorem smooth_coset_split_root_partition {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {alpha gamma x : F} {order ell : Nat}
    (hgamma_order : orderOf gamma = order)
    (hell_dvd : ell ∣ order) (hell_pos : 0 < ell)
    (hx : ∃ k : Nat, k < order ∧ x = alpha * gamma ^ k) :
    ∃ j : Nat, j < ell ∧
      x ^ (order / ell) = alpha ^ (order / ell) * (gamma ^ (order / ell)) ^ j := by
  rcases hx with ⟨k, _hklt, rfl⟩
  refine ⟨k % ell, Nat.mod_lt k hell_pos, ?_⟩
  apply smooth_coset_split_root_partition_mod
  · rw [← hgamma_order]
    exact pow_orderOf_eq_one gamma
  · exact hell_dvd

/-- A finite-field generator of order `#F - 1` enumerates all nonzero elements. -/
theorem exists_generator_pow_of_order_eq_card_sub_one {F : Type*}
    [Field F] [Finite F] [DecidableEq F]
    {q : Nat} {generator a : F}
    (hcard : Nat.card F = q)
    (hgen : orderOf generator = q - 1) (ha : a ≠ 0) :
    ∃ k : Nat, k < q - 1 ∧ a = generator ^ k := by
  have hq_gt_one : 1 < q := by
    rw [← hcard]
    exact Finite.one_lt_card
  have hgen_ne_zero : generator ≠ 0 := by
    intro hzero
    have hpow : generator ^ (q - 1) = 1 := by
      rw [← hgen]
      exact pow_orderOf_eq_one generator
    rw [hzero] at hpow
    have hqsub : 0 < q - 1 := Nat.sub_pos_of_lt hq_gt_one
    rcases Nat.exists_eq_add_of_lt hqsub with ⟨m, hm⟩
    rw [hm] at hpow
    simp at hpow
  let gu : Fˣ := Units.mk0 generator hgen_ne_zero
  let au : Fˣ := Units.mk0 a ha
  have hgu_order : orderOf (gu : Fˣ) = Nat.card Fˣ := by
    rw [← orderOf_units (y := gu)]
    simp [gu, hgen, Nat.card_units, hcard]
  have htop : Subgroup.zpowers gu = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top (Subgroup.zpowers gu)]
    rw [Nat.card_zpowers, hgu_order]
  have hau_z : au ∈ Subgroup.zpowers gu := by
    rw [htop]
    exact Subgroup.mem_top au
  have hau_range := (mem_zpowers_iff_mem_range_orderOf (x := gu) (y := au)).mp hau_z
  rcases Finset.mem_image.mp hau_range with ⟨k, hk, hkpow⟩
  refine ⟨k, ?_, ?_⟩
  · have hklt : k < orderOf (gu : Fˣ) := by
      simpa using Finset.mem_range.mp hk
    rwa [hgu_order, Nat.card_units, hcard] at hklt
  · have hval := congrArg (fun u : Fˣ ↦ (u : F)) hkpow
    simpa [gu, au] using hval.symm

/-- Roots of `p` are contained in the explicit coset `alpha * <gamma>` of order `order`. -/
def SmoothCosetInvariant {F : Type*} [Field F]
    (alpha gamma : F) (order : Nat) (p : CPolynomial F) : Prop :=
  alpha ≠ 0 ∧
    0 < order ∧
      orderOf gamma = order ∧
        ∀ x : F, CPolynomial.eval x p = 0 →
          ∃ k : Nat, k < order ∧ x = alpha * gamma ^ k

/-- Schedule recursion preserves the smooth coset invariant. -/
theorem smooth_schedule_recursion_preserves_coset_invariant {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {order ell j : Nat} {alpha gamma : F} {p : CPolynomial F}
    (hchild_alpha_ne_zero : alpha * gamma ^ j ≠ 0)
    (hchild_order_pos : 0 < order / ell)
    (hchild_generator_order : orderOf (gamma ^ ell) = order / ell)
    (hchild_roots :
      ∀ x : F,
        CPolynomial.eval x
            (CPolynomial.monicNormalize
              (CPolynomial.gcdMonic p
                (xPowModWith M D p (order / ell) -
                  CPolynomial.C
                    (alpha ^ (order / ell) * (gamma ^ (order / ell)) ^ j)))) = 0 →
          ∃ k : Nat, k < order / ell ∧
            x = (alpha * gamma ^ j) * (gamma ^ ell) ^ k) :
    SmoothCosetInvariant
      (alpha * gamma ^ j)
      (gamma ^ ell)
      (order / ell)
      (CPolynomial.monicNormalize
        (CPolynomial.gcdMonic p
          (xPowModWith M D p (order / ell) -
            CPolynomial.C (alpha ^ (order / ell) * (gamma ^ (order / ell)) ^ j)))) := by
  exact ⟨hchild_alpha_ne_zero, hchild_order_pos, hchild_generator_order, hchild_roots⟩

/-- Schedule factors divide the current coset order along executable smooth recursion. -/
def SmoothScheduleDivides : List Nat → Nat → Prop
  | [], _ => True
  | ell :: rest, order =>
      if ell ≤ 1 then
        SmoothScheduleDivides rest order
      else if ell = order then
        True
      else
        ell ∣ order ∧ SmoothScheduleDivides rest (order / ell)

instance instDecidableSmoothScheduleDivides (schedule : List Nat) (order : Nat) :
    Decidable (SmoothScheduleDivides schedule order) := by
  induction schedule generalizing order with
  | nil =>
      unfold SmoothScheduleDivides
      infer_instance
  | cons ell rest ih =>
      unfold SmoothScheduleDivides
      by_cases hellsmall : ell ≤ 1
      · rw [if_pos hellsmall]
        exact ih order
      · rw [if_neg hellsmall]
        by_cases helleq : ell = order
        · rw [if_pos helleq]
          infer_instance
        · rw [if_neg helleq]
          infer_instance

/-- The declared smooth schedule reaches singleton cosets. -/
theorem smooth_schedule_reaches_singleton {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmoothCyclicRootContext F) :
    ctx.schedule.toList.foldl (fun order ell ↦ order / ell) (ctx.q - 1) = 1 :=
  ctx.schedule_complete

/-- Path completeness for the schedule-driven smooth coset recursion. -/
theorem smoothCosetLinearFactorsWithSchedule_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) :
    ∀ (schedule : List Nat) (order : Nat) (alpha gamma : F) (p : CPolynomial F) (a : F),
      SmoothScheduleDivides schedule order →
        gamma ^ order = 1 →
          p ≠ 0 →
            CPolynomial.eval a p = 0 →
              (∃ k : Nat, k < order ∧ a = alpha * gamma ^ k) →
                ∃ factor,
                  factor ∈
                      (smoothCosetLinearFactorsWithSchedule M D E schedule order alpha gamma
                        p).toList ∧
                    IsLinearRootFactorCandidate factor a := by
  intro schedule
  induction schedule with
  | nil =>
      intro order alpha gamma p a _hsched _hgamma hp hroot hcoset
      unfold smoothCosetLinearFactorsWithSchedule
      let p' := CPolynomial.monicNormalize p
      have hp' : p' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hp
      have hroot' : CPolynomial.eval a p' = 0 := (monicNormalize_root_iff hp).2 hroot
      by_cases hzero : (p' == 0 || p' == 1) = true
      · have hcases : p' = 0 ∨ p' = 1 := by
          simpa [p'] using hzero
        rcases hcases with h0 | h1
        · exact (hp' h0).elim
        · rw [h1] at hroot'
          rw [eval_one a] at hroot'
          exact (one_ne_zero hroot').elim
      · rw [if_neg hzero]
        by_cases hlin : isRepresentedLinearFactor p' = true
        · rw [if_pos hlin]
          refine ⟨p', ?_, representedLinearFactor_candidate_of_root hlin hroot'⟩
          simp [p']
        · rw [if_neg hlin]
          exact smoothLeafLinearFactors_complete E hcoset hroot'
  | cons ell rest ih =>
      intro order alpha gamma p a hsched hgamma hp hroot hcoset
      unfold smoothCosetLinearFactorsWithSchedule
      let p' := CPolynomial.monicNormalize p
      have hp' : p' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hp
      have hroot' : CPolynomial.eval a p' = 0 := (monicNormalize_root_iff hp).2 hroot
      by_cases hzero : (p' == 0 || p' == 1) = true
      · have hcases : p' = 0 ∨ p' = 1 := by
          simpa [p'] using hzero
        rcases hcases with h0 | h1
        · exact (hp' h0).elim
        · rw [h1] at hroot'
          rw [eval_one a] at hroot'
          exact (one_ne_zero hroot').elim
      · rw [if_neg hzero]
        by_cases hlin : isRepresentedLinearFactor p' = true
        · rw [if_pos hlin]
          refine ⟨p', ?_, representedLinearFactor_candidate_of_root hlin hroot'⟩
          simp [p']
        · rw [if_neg hlin]
          by_cases hellsmall : ell ≤ 1
          · rw [if_pos hellsmall]
            have hschedRest : SmoothScheduleDivides rest order := by
              simpa [SmoothScheduleDivides, hellsmall] using hsched
            exact ih order alpha gamma p' a hschedRest hgamma hp' hroot' hcoset
          · rw [if_neg hellsmall]
            by_cases helleq : ell = order
            · rw [if_pos helleq]
              exact smoothLeafLinearFactors_complete E hcoset hroot'
            · rw [if_neg helleq]
              have hschedRest : ell ∣ order ∧ SmoothScheduleDivides rest (order / ell) := by
                simpa [SmoothScheduleDivides, hellsmall, helleq] using hsched
              rcases hschedRest with ⟨hell_dvd, hschedChild⟩
              rcases hcoset with ⟨k, hk, haeq⟩
              have hell_gt_one : 1 < ell := by omega
              have hell_pos : 0 < ell := by omega
              let childOrder := order / ell
              let tau := gamma ^ childOrder
              let xPow := xPowModWith M D p' childOrder
              let j := k % ell
              have hjlt : j < ell := Nat.mod_lt k hell_pos
              have hjmem : j ∈ List.range ell := by
                simpa [j] using hjlt
              have hellmul : ell * childOrder = order := by
                dsimp [childOrder]
                rw [Nat.mul_comm]
                exact Nat.div_mul_cancel hell_dvd
              have hchildGamma : (gamma ^ ell) ^ childOrder = 1 := by
                rw [← pow_mul, hellmul, hgamma]
              have hchildCoset : ∃ t : Nat, t < childOrder ∧
                  a = (alpha * gamma ^ j) * (gamma ^ ell) ^ t := by
                refine ⟨k / ell, ?_, ?_⟩
                · dsimp [childOrder]
                  rw [Nat.div_lt_iff_lt_mul hell_pos]
                  rw [Nat.mul_comm]
                  exact lt_of_lt_of_eq hk hellmul.symm
                · rw [haeq]
                  dsimp [j]
                  have hkdecomp : k % ell + ell * (k / ell) = k :=
                    Nat.mod_add_div k ell
                  calc
                    alpha * gamma ^ k =
                        alpha * gamma ^ (k % ell + ell * (k / ell)) := by
                          rw [hkdecomp]
                    _ = alpha * (gamma ^ (k % ell) * gamma ^ (ell * (k / ell))) := by
                          rw [pow_add]
                    _ = alpha * gamma ^ (k % ell) * (gamma ^ ell) ^ (k / ell) := by
                          rw [pow_mul]
                          ring
              let beta := alpha ^ childOrder * tau ^ j
              let witness := xPow - CPolynomial.C beta
              let child := CPolynomial.monicNormalize (CPolynomial.gcdMonic p' witness)
              have hpoweq : a ^ childOrder = beta := by
                rw [haeq]
                dsimp [beta, tau, j, childOrder]
                exact smooth_coset_split_root_partition_mod hgamma hell_dvd
              have hwitnessRoot : CPolynomial.eval a witness = 0 := by
                dsimp [witness, xPow, beta]
                rw [eval_sub, eval_xPowModWith_eq_pow M D hroot' childOrder, eval_C, hpoweq]
                ring
              have hgcdRoot : CPolynomial.eval a (CPolynomial.gcdMonic p' witness) = 0 :=
                gcdMonic_root_of_left_right hroot' hwitnessRoot
              have hgcdNe : CPolynomial.gcdMonic p' witness ≠ 0 :=
                gcdMonic_ne_zero_of_left hp'
              have hchildNe : child ≠ 0 := monicNormalize_ne_zero_of_ne_zero hgcdNe
              have hchildRoot : CPolynomial.eval a child = 0 :=
                (monicNormalize_root_iff hgcdNe).2 hgcdRoot
              have hchildNotOne : child ≠ 1 := by
                intro h1
                rw [h1] at hchildRoot
                rw [eval_one a] at hchildRoot
                exact (one_ne_zero hchildRoot).elim
              have hskip : ¬ (child == 0 || child == 1) = true := by
                intro hskipTrue
                have hcases : child = 0 ∨ child = 1 := by
                  simpa [child] using hskipTrue
                rcases hcases with h0 | h1
                · exact hchildNe h0
                · exact hchildNotOne h1
              have hrec := ih childOrder (alpha * gamma ^ j) (gamma ^ ell) child a
                hschedChild hchildGamma hchildNe hchildRoot hchildCoset
              have hfold : ∀ (js : List Nat) (acc : Array (CPolynomial F)),
                  (∃ factor, factor ∈ acc.toList ∧ IsLinearRootFactorCandidate factor a) ∨
                    j ∈ js →
                    ∃ factor,
                      factor ∈ (js.foldl
                        (fun factors y ↦
                          let beta := alpha ^ childOrder * tau ^ y
                          let witness := xPow - CPolynomial.C beta
                          let child := CPolynomial.monicNormalize (CPolynomial.gcdMonic p' witness)
                          if child == 0 || child == 1 then
                            factors
                          else
                            factors ++ smoothCosetLinearFactorsWithSchedule M D E rest childOrder
                              (alpha * gamma ^ y) (gamma ^ ell) child) acc).toList ∧
                        IsLinearRootFactorCandidate factor a := by
                intro js
                induction js with
                | nil =>
                    intro acc h
                    rcases h with hacc | hjnil
                    · exact hacc
                    · simp at hjnil
                | cons y ys ihys =>
                    intro acc h
                    simp only [List.foldl_cons]
                    apply ihys
                    rcases h with hacc | hy
                    · left
                      rcases hacc with ⟨factor, hmem, hcand⟩
                      refine ⟨factor, ?_, hcand⟩
                      by_cases hskipY : (CPolynomial.monicNormalize
                          (CPolynomial.gcdMonic p'
                            (xPow - CPolynomial.C (alpha ^ childOrder * tau ^ y))) == 0 ||
                          CPolynomial.monicNormalize
                            (CPolynomial.gcdMonic p'
                              (xPow - CPolynomial.C (alpha ^ childOrder * tau ^ y))) == 1) = true
                      · rw [if_pos hskipY]
                        exact hmem
                      · rw [if_neg hskipY]
                        let childY := CPolynomial.monicNormalize
                          (CPolynomial.gcdMonic p'
                            (xPow - CPolynomial.C (alpha ^ childOrder * tau ^ y)))
                        let tail := smoothCosetLinearFactorsWithSchedule M D E rest childOrder
                          (alpha * gamma ^ y) (gamma ^ ell) childY
                        simpa [childY, tail] using Array.mem_append_left tail
                          (by simpa using hmem)
                    · simp at hy
                      rcases hy with hyj | hyrest
                      · subst y
                        left
                        rcases hrec with ⟨factor, hmem, hcand⟩
                        refine ⟨factor, ?_, hcand⟩
                        rw [if_neg hskip]
                        simpa [child, witness, beta] using
                          Array.mem_append_right acc (by simpa using hmem)
                      · right
                        exact hyrest
              exact hfold (List.range ell) #[] (Or.inr hjmem)

/-- Completeness of the top-level smooth linear-factor splitter. -/
theorem smoothLinearFactorsAlgorithmWith_complete {F : Type*}
    [Field F] [Finite F] [DecidableEq F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (E : BatchEvalContext F) (q : Nat) (generator : F) (schedule : Array Nat)
    (hcard : Nat.card F = q)
    (hgenerator : orderOf generator = q - 1)
    (hschedule : SmoothScheduleDivides schedule.toList (q - 1))
    {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (smoothLinearFactorsAlgorithmWith M D E q generator schedule p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  unfold smoothLinearFactorsAlgorithmWith
  let p' := CPolynomial.monicNormalize p
  have hp' : p' ≠ 0 := monicNormalize_ne_zero_of_ne_zero hp
  have hroot' : CPolynomial.eval a p' = 0 := (monicNormalize_root_iff hp).2 hroot
  by_cases hzero : (p' == 0 || p' == 1) = true
  · have hcases : p' = 0 ∨ p' = 1 := by
      simpa [p'] using hzero
    rcases hcases with h0 | h1
    · exact (hp' h0).elim
    · rw [h1] at hroot'
      rw [eval_one a] at hroot'
      exact (one_ne_zero hroot').elim
  · rw [if_neg hzero]
    by_cases ha0 : a = 0
    · subst a
      have hcoeff : p'.coeff 0 = 0 := by
        simpa [eval_zero_eq_coeff_zero] using hroot'
      have hconst : ((p'.coeff 0 == 0) = true) := by
        simp [hcoeff]
      rw [if_pos hconst]
      refine ⟨CPolynomial.linearFactor (0 : F), ?_, linearFactor_isRootFactorCandidate 0⟩
      unfold smoothNonzeroLinearFactorsWith
      simp
    · have hgenPow : generator ^ (q - 1) = 1 := by
        rw [← hgenerator]
        exact pow_orderOf_eq_one generator
      have hcoset : ∃ k : Nat, k < q - 1 ∧ a = (1 : F) * generator ^ k := by
        rcases exists_generator_pow_of_order_eq_card_sub_one hcard hgenerator ha0 with
          ⟨k, hk, ha⟩
        exact ⟨k, hk, by simp [ha]⟩
      by_cases hconst : ((p'.coeff 0 == 0) = true)
      · rw [if_pos hconst]
        have hcoeff : p'.coeff 0 = 0 := by simpa using hconst
        have hdivRoot : CPolynomial.eval a (CPolynomial.divX p') = 0 :=
          eval_divX_eq_zero_of_ne_zero_root ha0 hcoeff hroot'
        have hdivNe : CPolynomial.divX p' ≠ 0 :=
          divX_ne_zero_of_ne_zero_coeff_zero hp' hcoeff
        have hchildRoot :
            CPolynomial.eval a (CPolynomial.monicNormalize (CPolynomial.divX p')) = 0 :=
          (monicNormalize_root_iff hdivNe).2 hdivRoot
        have hchildNe : CPolynomial.monicNormalize (CPolynomial.divX p') ≠ 0 :=
          monicNormalize_ne_zero_of_ne_zero hdivNe
        rcases smoothCosetLinearFactorsWithSchedule_complete M D E schedule.toList (q - 1)
            (1 : F) generator (CPolynomial.monicNormalize (CPolynomial.divX p')) a
            hschedule hgenPow hchildNe hchildRoot hcoset with ⟨factor, hmem, hcand⟩
        refine ⟨factor, ?_, hcand⟩
        unfold smoothNonzeroLinearFactorsWith
        simpa [p'] using Array.mem_append_right (#[CPolynomial.linearFactor (0 : F)])
          (by simpa using hmem)
      · rw [if_neg hconst]
        rcases smoothCosetLinearFactorsWithSchedule_complete M D E schedule.toList (q - 1)
            (1 : F) generator p' a hschedule hgenPow hp' hroot' hcoset with
          ⟨factor, hmem, hcand⟩
        refine ⟨factor, ?_, hcand⟩
        unfold smoothNonzeroLinearFactorsWith
        simpa using hmem

end FiniteField

end Roots

end CPolynomial

end CompPoly
