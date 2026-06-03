/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Update

/-!
# Koetter Interpolation Soundness

Constraint-order invariants and soundness theorems for direct Koetter
interpolation.
-/

namespace CompPoly

namespace GuruswamiSudan

def lowerXConstraint {F : Type*} (constraint : InterpolationConstraint F) (a : Nat) :
    InterpolationConstraint F :=
  { x := constraint.x, y := constraint.y, xOrder := a, yOrder := constraint.yOrder }

def koetterBasisSatisfiesConstraints {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (basis : Array (CBivariate F)) (constraints : List (InterpolationConstraint F)) : Prop :=
  ∀ constraint, constraint ∈ constraints → ∀ idx, idx < basis.size →
    koetterDiscrepancy constraint (basis.getD idx (0 : CBivariate F)) = 0

def koetterConstraintsLowerClosed {F : Type*}
    (constraints : List (InterpolationConstraint F)) : Prop :=
  ∀ constraint, constraint ∈ constraints → ∀ a,
    constraint.xOrder = a + 1 → lowerXConstraint constraint a ∈ constraints

def koetterConstraintLowerIn {F : Type*}
    (processed : List (InterpolationConstraint F)) (constraint : InterpolationConstraint F) :
    Prop :=
  ∀ a, constraint.xOrder = a + 1 → lowerXConstraint constraint a ∈ processed

def koetterConstraintsLowerBefore {F : Type*}
    (constraints : List (InterpolationConstraint F)) : Prop :=
  ∀ pre current post a, constraints = pre ++ current :: post →
    current.xOrder = a + 1 → lowerXConstraint current a ∈ pre

theorem foldl_append_toArray_toList {α β : Type*}
    (chunk : β → List α) :
    ∀ (xs : List β) (acc : Array α),
      (xs.foldl (fun out x ↦ out ++ (chunk x).toArray) acc).toList =
        acc.toList ++ xs.flatMap chunk := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp

theorem array_foldl_append_toArray_toList {α β : Type*}
    (chunk : β → List α) (xs : Array β) (acc : Array α) :
    (xs.foldl (fun out x ↦ out ++ (chunk x).toArray) acc).toList =
      acc.toList ++ xs.toList.flatMap chunk := by
  simpa using foldl_append_toArray_toList chunk xs.toList acc

theorem array_eq_of_toList {α : Type*} {a b : Array α} (h : a.toList = b.toList) :
    a = b := by
  simpa using congrArg List.toArray h

def interpolationConstraintsList {F : Type*}
    (points : Array (F × F)) (multiplicity : Nat) : List (InterpolationConstraint F) :=
  points.toList.flatMap fun point =>
    (List.range multiplicity).flatMap fun a =>
      (List.range (multiplicity - a)).map fun b =>
        ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
          InterpolationConstraint F)

def interpolationConstraintsOrderList {F : Type*}
    (point : F × F) (multiplicity xOrder : Nat) : List (InterpolationConstraint F) :=
  (List.range (multiplicity - xOrder)).map fun yOrder =>
    ({ x := point.1, y := point.2, xOrder := xOrder, yOrder := yOrder } :
      InterpolationConstraint F)

theorem interpolationConstraintsOrderList_lower_mem {F : Type*}
    (point : F × F) {multiplicity a yOrder : Nat}
    (hy : yOrder < multiplicity - (a + 1)) :
    ({ x := point.1, y := point.2, xOrder := a, yOrder := yOrder } :
      InterpolationConstraint F) ∈ interpolationConstraintsOrderList point multiplicity a := by
  unfold interpolationConstraintsOrderList
  apply List.mem_map.mpr
  refine ⟨yOrder, ?_, rfl⟩
  exact List.mem_range.mpr (by omega)

theorem interpolationConstraintsPointUpTo_lowerBefore {F : Type*}
    (point : F × F) (multiplicity count : Nat) :
    koetterConstraintsLowerBefore
      ((List.range count).flatMap fun xOrder =>
        interpolationConstraintsOrderList point multiplicity xOrder) := by
  unfold koetterConstraintsLowerBefore lowerXConstraint
  induction count with
  | zero =>
      intro pre current post a hsplit _hx
      simp at hsplit
  | succ count ih =>
      intro pre current post a hsplit hx
      rw [List.range_succ, List.flatMap_append] at hsplit
      simp only [List.flatMap_singleton] at hsplit
      let pref : List (InterpolationConstraint F) :=
        (List.range count).flatMap fun xOrder =>
          interpolationConstraintsOrderList point multiplicity xOrder
      let last : List (InterpolationConstraint F) :=
        interpolationConstraintsOrderList point multiplicity count
      change pref ++ last = pre ++ current :: post at hsplit
      rcases List.append_eq_append_iff.mp hsplit with htail | hhead
      · rcases htail with ⟨as, hpre, hlastSplit⟩
        rw [hpre]
        have hcurMem : current ∈ last := by
          rw [hlastSplit]
          simp
        unfold last interpolationConstraintsOrderList at hcurMem
        simp only [List.mem_map, List.mem_range] at hcurMem
        rcases hcurMem with ⟨yOrder, hyOrder, hcur⟩
        subst current
        simp at hx
        subst count
        exact List.mem_append_left as
          (List.mem_flatMap.mpr ⟨a, List.mem_range.mpr (by omega),
            interpolationConstraintsOrderList_lower_mem point hyOrder⟩)
      · rcases hhead with ⟨bs, hprefixSplit, htail⟩
        rcases List.cons_eq_append_iff.mp htail with hboundary | hinside
        · rcases hboundary with ⟨hbs, hrest⟩
          subst bs
          have hpref : pref = pre := by
            simpa using hprefixSplit
          rw [← hpref]
          have hcurMem : current ∈ last := by
            rw [hrest]
            simp
          unfold last interpolationConstraintsOrderList at hcurMem
          simp only [List.mem_map, List.mem_range] at hcurMem
          rcases hcurMem with ⟨yOrder, hyOrder, hcur⟩
          subst current
          simp at hx
          subst count
          exact List.mem_flatMap.mpr ⟨a, List.mem_range.mpr (by omega),
            interpolationConstraintsOrderList_lower_mem point hyOrder⟩
        · rcases hinside with ⟨bs', hbs, hpost⟩
          subst bs
          exact ih pre current bs' a hprefixSplit hx

theorem interpolationConstraintsPointStep_eq_append {F : Type*}
    (point : F × F) (multiplicity : Nat) (acc : Array (InterpolationConstraint F)) :
    (List.range multiplicity).foldl
      (fun out a ↦
        out ++ ((List.range (multiplicity - a)).map fun b ↦
          ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
            InterpolationConstraint F)).toArray)
      acc =
    acc ++ ((List.range multiplicity).flatMap fun a ↦
      (List.range (multiplicity - a)).map fun b ↦
        ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
          InterpolationConstraint F)).toArray := by
  apply array_eq_of_toList
  rw [foldl_append_toArray_toList]
  simp

theorem interpolationConstraints_toList_eq_list {F : Type*}
    (points : Array (F × F)) (multiplicity : Nat) :
    (interpolationConstraints points multiplicity).toList =
      interpolationConstraintsList points multiplicity := by
  unfold interpolationConstraints interpolationConstraintsList
  simp only [bind_pure_comp, map_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, List.foldl_push_eq_append,
    Array.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  have hrange : ∀ n, List.range' 0 n = List.range n := by
    intro n
    exact (List.range_eq_range' (n := n)).symm
  simp [hrange]
  rw [show
      (fun b (a : F × F) ↦
        List.foldl
          (fun b a_1 ↦
            b ++ (List.map (InterpolationConstraint.mk a.1 a.2 a_1)
              (List.range (multiplicity - a_1))).toArray)
          b (List.range multiplicity)) =
      (fun b point ↦
        b ++ ((List.range multiplicity).flatMap fun a ↦
          (List.range (multiplicity - a)).map fun b ↦
            ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
              InterpolationConstraint F)).toArray) by
    funext b point
    exact interpolationConstraintsPointStep_eq_append point multiplicity b]
  rw [array_foldl_append_toArray_toList]
  simp only [List.nil_append]

theorem interpolationConstraintsList_lowerBefore {F : Type*}
    (points : Array (F × F)) (multiplicity : Nat) :
    koetterConstraintsLowerBefore (interpolationConstraintsList points multiplicity) := by
  unfold koetterConstraintsLowerBefore interpolationConstraintsList lowerXConstraint
  intro pre current post a hsplit hx
  generalize points.toList = pointList at hsplit
  induction pointList generalizing pre with
  | nil =>
      simp at hsplit
  | cons point points ih =>
      simp only [List.flatMap_cons] at hsplit
      let chunk : List (InterpolationConstraint F) :=
        (List.range multiplicity).flatMap fun xOrder =>
          interpolationConstraintsOrderList point multiplicity xOrder
      let rest : List (InterpolationConstraint F) :=
        points.flatMap fun point =>
          (List.range multiplicity).flatMap fun xOrder =>
            interpolationConstraintsOrderList point multiplicity xOrder
      change chunk ++ rest = pre ++ current :: post at hsplit
      rcases List.append_eq_append_iff.mp hsplit with htail | hhead
      · rcases htail with ⟨as, hpre, hrestSplit⟩
        rw [hpre]
        exact List.mem_append_right chunk
          (ih as (by simpa [rest, interpolationConstraintsOrderList] using hrestSplit))
      · rcases hhead with ⟨bs, hchunkSplit, htailEq⟩
        rcases List.cons_eq_append_iff.mp htailEq with hboundary | hinside
        · rcases hboundary with ⟨hbs, hrestEq⟩
          subst bs
          have hnone :=
            ih [] (by simpa [rest, interpolationConstraintsOrderList] using hrestEq)
          cases hnone
        · rcases hinside with ⟨bs', hbs, _hpostEq⟩
          subst bs
          have hpointBefore :=
            interpolationConstraintsPointUpTo_lowerBefore point multiplicity multiplicity
          exact hpointBefore pre current bs' a hchunkSplit hx

theorem koetterProcessConstraint_satisfies_cons {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (current : InterpolationConstraint F)
    (state : KoetterState F) (processed : List (InterpolationConstraint F))
    (hSat : koetterBasisSatisfiesConstraints state.basis processed)
    (hClosed : koetterConstraintsLowerClosed processed)
    (hCurrentLower : koetterConstraintLowerIn processed current) :
    koetterBasisSatisfiesConstraints
      (koetterProcessConstraint params current state).basis (current :: processed) := by
  intro constraint hconstraint idx hi
  simp at hconstraint
  cases hconstraint with
  | inl hcur =>
      subst constraint
      apply koetterProcessConstraint_satisfies_current
      intro pivot hpivot a ha
      exact hSat (lowerXConstraint current a) (hCurrentLower a ha) pivot.index
        (koetterSelectPivot_some_index_lt hpivot)
      exact hi
  | inr hprior =>
      apply koetterProcessConstraint_preserves_prior
      · intro k hk
        exact hSat constraint hprior k hk
      · intro k hk a ha
        exact hSat (lowerXConstraint constraint a) (hClosed constraint hprior a ha) k hk
      · exact hi

theorem koetterConstraintLowerIn_of_before {F : Type*}
    {original processed remaining : List (InterpolationConstraint F)}
    {current : InterpolationConstraint F}
    (hsplit : processed.reverse ++ current :: remaining = original)
    (hbefore : koetterConstraintsLowerBefore original) :
    koetterConstraintLowerIn processed current := by
  intro a ha
  have hlowerRev : lowerXConstraint current a ∈ processed.reverse := by
    exact hbefore processed.reverse current remaining a hsplit.symm ha
  simpa [List.mem_reverse] using hlowerRev

theorem koetterConstraintsLowerClosed_cons_of_before {F : Type*}
    {original processed remaining : List (InterpolationConstraint F)}
    {current : InterpolationConstraint F}
    (hsplit : processed.reverse ++ current :: remaining = original)
    (hbefore : koetterConstraintsLowerBefore original)
    (hClosed : koetterConstraintsLowerClosed processed) :
    koetterConstraintsLowerClosed (current :: processed) := by
  intro constraint hmem a ha
  simp at hmem
  cases hmem with
  | inl hcur =>
      subst constraint
      have hlowerRev : lowerXConstraint current a ∈ processed.reverse := by
        exact hbefore processed.reverse current remaining a hsplit.symm ha
      simp [List.mem_reverse] at hlowerRev
      simp [hlowerRev]
  | inr hprocessed =>
      have hlower := hClosed constraint hprocessed a ha
      simp [hlower]

theorem koetterConstraintsLowerClosed_lower_lt {F : Type*}
    {processed : List (InterpolationConstraint F)}
    (hClosed : koetterConstraintsLowerClosed processed)
    {constraint : InterpolationConstraint F}
    (hmem : constraint ∈ processed) :
    ∀ a, a < constraint.xOrder → lowerXConstraint constraint a ∈ processed := by
  have hmain :
      ∀ n, ∀ constraint : InterpolationConstraint F,
        constraint.xOrder = n → constraint ∈ processed →
          ∀ a, a < n → lowerXConstraint constraint a ∈ processed := by
    intro n
    induction n with
    | zero =>
        intro constraint hx _hmem a ha
        omega
    | succ n ih =>
        intro constraint hx hmem a ha
        by_cases haeq : a = n
        · subst a
          exact hClosed constraint hmem n hx
        · have han : a < n := by omega
          have hlowerMem : lowerXConstraint constraint n ∈ processed :=
            hClosed constraint hmem n hx
          have hrec := ih (lowerXConstraint constraint n) rfl hlowerMem a han
          simpa [lowerXConstraint] using hrec
  exact hmain constraint.xOrder constraint rfl hmem

theorem koetterConstraintLowerIn_of_before_lt {F : Type*}
    {original processed remaining : List (InterpolationConstraint F)}
    {current : InterpolationConstraint F}
    (hsplit : processed.reverse ++ current :: remaining = original)
    (hbefore : koetterConstraintsLowerBefore original)
    (hClosed : koetterConstraintsLowerClosed processed) :
    ∀ a, a < current.xOrder → lowerXConstraint current a ∈ processed := by
  intro a ha
  cases hx : current.xOrder with
  | zero =>
      omega
  | succ b =>
      by_cases hab : a = b
      · subst a
        exact koetterConstraintLowerIn_of_before hsplit hbefore b hx
      · have hablt : a < b := by omega
        have hbmem := koetterConstraintLowerIn_of_before hsplit hbefore b hx
        have hlower :=
          koetterConstraintsLowerClosed_lower_lt hClosed hbmem a hablt
        simpa [lowerXConstraint] using hlower

theorem koetterProcessConstraints_fold_satisfies {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (params : GSInterpParams) (original : List (InterpolationConstraint F))
    (hbefore : koetterConstraintsLowerBefore original) :
    ∀ remaining processed state,
      processed.reverse ++ remaining = original →
      koetterBasisSatisfiesConstraints state.basis processed →
      koetterConstraintsLowerClosed processed →
      koetterBasisSatisfiesConstraints
        (remaining.foldl (fun state constraint ↦ koetterProcessConstraint params constraint state)
          state).basis original := by
  intro remaining
  induction remaining with
  | nil =>
      intro processed state hsplit hSat _hClosed constraint hmem idx hi
      have hmemProcessed : constraint ∈ processed := by
        have : constraint ∈ processed.reverse := by
          simpa [hsplit.symm] using hmem
        simpa [List.mem_reverse] using this
      exact hSat constraint hmemProcessed idx hi
  | cons current remaining ih =>
      intro processed state hsplit hSat hClosed
      simp only [List.foldl_cons]
      apply ih (current :: processed) (koetterProcessConstraint params current state)
      · rw [List.reverse_cons, List.append_assoc]
        simpa using hsplit
      · exact koetterProcessConstraint_satisfies_cons params current state processed hSat hClosed
          (koetterConstraintLowerIn_of_before hsplit hbefore)
      · exact koetterConstraintsLowerClosed_cons_of_before hsplit hbefore hClosed

theorem koetterRawInterpolate_sound_of_lowerBefore {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (hbefore : koetterConstraintsLowerBefore
      (interpolationConstraints points params.multiplicity).toList)
    (h : koetterRawInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold koetterRawInterpolate at h
  let constraints := interpolationConstraints points params.multiplicity
  let initial := koetterInitialState (F := F) params
  let finalState := koetterProcessConstraints params constraints initial
  have hselect : koetterSelectFinal? params finalState.basis = some Q := by
    simpa [constraints, initial, finalState, koetterProcessConstraints] using h
  have hne := koetterSelectFinal?_some_ne_zero hselect
  have hdeg := koetterSelectFinal?_some_weightedDegree_le hselect
  rcases koetterSelectFinal?_some_entry_lt hselect with ⟨idx, hidx, hQidx⟩
  refine ⟨hne, hdeg, ?_⟩
  intro point hpoint a b hab
  have hconstraintMem :
      ({ x := point.1, y := point.2, xOrder := a, yOrder := b } :
        InterpolationConstraint F) ∈ constraints.toList := by
    rw [interpolationConstraints_toList_eq_list]
    unfold interpolationConstraintsList
    apply List.mem_flatMap.mpr
    refine ⟨point, hpoint, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨a, by simpa using (show a < params.multiplicity by omega), ?_⟩
    apply List.mem_map.mpr
    refine ⟨b, ?_, rfl⟩
    simpa using (show b < params.multiplicity - a by omega)
  have hSat := koetterProcessConstraints_fold_satisfies params constraints.toList hbefore
    constraints.toList [] initial (by simp)
    (by intro c hc; simp at hc)
    (by intro c hc; simp at hc)
  have hSatFinal : koetterBasisSatisfiesConstraints finalState.basis constraints.toList := by
    simpa [finalState, koetterProcessConstraints] using hSat
  rw [hQidx]
  exact hSatFinal ({ x := point.1, y := point.2, xOrder := a, yOrder := b })
    hconstraintMem idx hidx

/-- Soundness for raw Koetter interpolation when `messageDegree > 1`.

After all Hasse constraints are processed, any selected raw Koetter polynomial
is already a valid interpolation witness. -/
theorem koetterRawInterpolate_sound_of_messageDegree_gt_one {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (_hMessage : ¬ params.messageDegree ≤ 1)
    (h : koetterRawInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  have hbefore :
      koetterConstraintsLowerBefore
        (interpolationConstraints points params.multiplicity).toList := by
    rw [interpolationConstraints_toList_eq_list]
    exact interpolationConstraintsList_lowerBefore points params.multiplicity
  exact koetterRawInterpolate_sound_of_lowerBefore hbefore h

/-- Soundness for any polynomial returned by direct Koetter interpolation. -/
theorem koetterInterpolate_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F}
    (h : koetterInterpolate points params = some Q) :
    ValidInterpolationWitness points params Q := by
  unfold koetterInterpolate at h
  by_cases hLow : params.messageDegree ≤ 1
  · simp [hLow] at h
    cases h
    simpa using lowMessageDegreeInterpolation_sound (points := points)
      (params := params) hLow
  · simp [hLow] at h
    exact koetterRawInterpolate_sound_of_messageDegree_gt_one hLow h

end GuruswamiSudan

end CompPoly
