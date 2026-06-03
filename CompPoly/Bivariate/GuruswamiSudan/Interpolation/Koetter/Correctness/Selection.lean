/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Algebra

/-!
# Koetter Selection Correctness Helpers

Final-candidate and pivot-selection lemmas used by Koetter correctness.
-/

namespace CompPoly

namespace GuruswamiSudan

theorem koetterSelectFinal?_some_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    Q ≠ 0 := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => basis.getD pivot.index 0 ≠ 0
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  have hstep : ∀ best idx, good best → good (step best idx) := by
    intro best idx hbest
    unfold good step
    by_cases hzero : basis.getD idx 0 = 0
    · convert hbest using 1
      simp [hzero]
    · cases best with
      | none =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          simp [hzero', Array.getD_eq_getD_getElem?]
      | some current =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [good, hzero', hbetter', Array.getD_eq_getD_getElem?] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best, good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hbest
        simp only [List.foldl_cons]
        exact ih (step best idx) (hstep best idx hbest)
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    exact hfoldGoodAux (List.range basis.size) none (by simp [good])
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      have hpivotGood : basis.getD pivot.index 0 ≠ 0 := by
        simpa [hbest, good] using hfoldGood
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest] at h
        rcases h with ⟨_, hQ⟩
        have hpivotGood' : basis[pivot.index]?.getD 0 ≠ 0 := by
          simpa [Array.getD_eq_getD_getElem?] using hpivotGood
        simpa [hQ] using hpivotGood'
      · simp [hbest] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

theorem koetterSelectFinal?_some_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest] at h
        rcases h with ⟨hdeg', hQ⟩
        simpa [hQ, Array.getD_eq_getD_getElem?] using hdeg'
      · simp [hbest] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

theorem koetterSelectFinal?_some_entry {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    ∃ idx, Q = basis.getD idx 0 := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest] at h
        rcases h with ⟨_, hQ⟩
        refine ⟨pivot.index, ?_⟩
        simp [hQ, Array.getD_eq_getD_getElem?]
      · simp [hbest] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

theorem koetterSelectFinal?_some_entry_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)} {Q : CBivariate F}
    (h : koetterSelectFinal? params basis = some Q) :
    ∃ idx, idx < basis.size ∧ Q = basis.getD idx 0 := by
  unfold koetterSelectFinal? at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => pivot.index < basis.size
  change
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q at h
  have hstep : ∀ best idx, idx ∈ List.range basis.size → good best → good (step best idx) := by
    intro best idx hidxMem hbest
    have hidx : idx < basis.size := by
      simpa using hidxMem
    unfold good step
    by_cases hzero : basis.getD idx 0 = 0
    · have hzero' : basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      simpa [hzero'] using hbest
    · cases best with
      | none =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          simpa [hzero'] using hidx
      | some current =>
          have hzero' : ¬basis[idx]?.getD 0 = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hidx
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best,
      (∀ idx, idx ∈ xs → idx < basis.size) → good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best _ hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hxs hbest
        simp only [List.foldl_cons]
        apply ih
        · intro j hj
          exact hxs j (by simp [hj])
        · exact hstep best idx (by simpa using hxs idx (by simp)) hbest
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    apply hfoldGoodAux (List.range basis.size) none
    · intro idx hidx
      simpa using hidx
    · simp [good]
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest] at h
  | some pivot =>
      have hpivotLt : pivot.index < basis.size := by
        simpa [hbest, good] using hfoldGood
      by_cases hdeg : CBivariate.natWeightedDegree (basis.getD pivot.index 0)
          1 (yWeight params) ≤ params.weightedDegreeBound
      · simp [hbest] at h
        rcases h with ⟨_, hQ⟩
        refine ⟨pivot.index, hpivotLt, ?_⟩
        simp [hQ, Array.getD_eq_getD_getElem?]
      · simp [hbest] at h
        rcases h with ⟨hdeg', _⟩
        exact (hdeg (by simpa [Array.getD_eq_getD_getElem?] using hdeg')).elim

theorem koetterPivotBetter_weightedDegree_le {F : Type*}
    {candidate current : KoetterPivot F}
    (h : koetterPivotBetter candidate current = true) :
    candidate.weightedDegree ≤ current.weightedDegree := by
  unfold koetterPivotBetter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

theorem koetterPivotBetter_not_weightedDegree_le {F : Type*}
    {candidate current : KoetterPivot F}
    (h : ¬ koetterPivotBetter candidate current = true) :
    current.weightedDegree ≤ candidate.weightedDegree := by
  unfold koetterPivotBetter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    not_and] at h
  omega

theorem koetterPivotBetter_self_false {F : Type*}
    (candidate : KoetterPivot F) :
    koetterPivotBetter candidate candidate = false := by
  unfold koetterPivotBetter
  simp

theorem koetterPivotBetter_not_of_better_left {F : Type*}
    {candidate current other : KoetterPivot F}
    (hbetter : koetterPivotBetter candidate current = true)
    (hother : ¬ koetterPivotBetter other current = true) :
    ¬ koetterPivotBetter other candidate = true := by
  unfold koetterPivotBetter at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    not_and] at *
  omega

theorem koetterPivotBetter_not_index_le_of_weightedDegree_eq {F : Type*}
    {candidate current : KoetterPivot F}
    (h : ¬ koetterPivotBetter candidate current = true)
    (hdegree : candidate.weightedDegree = current.weightedDegree) :
    current.index ≤ candidate.index := by
  unfold koetterPivotBetter at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_or,
    not_and] at h
  omega

theorem koetterSelectFinal?_some_of_exists_entry {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {basis : Array (CBivariate F)}
    (hExists : ∃ idx, idx < basis.size ∧ basis.getD idx 0 ≠ 0 ∧
      CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) ≤
        params.weightedDegreeBound) :
    ∃ Q, koetterSelectFinal? params basis = some Q := by
  unfold koetterSelectFinal?
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      if Q == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := 0
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  change ∃ Q,
    (match (List.range basis.size).foldl step none with
    | none => none
    | some pivot =>
        let Q := basis.getD pivot.index 0
        if CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound then
          some Q
        else none) = some Q
  let degree : Nat → Nat := fun idx ↦
    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params)
  let wellBest : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => pivot.weightedDegree = degree pivot.index
  let boundedBest : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => False
    | some pivot =>
        pivot.weightedDegree = degree pivot.index ∧
          pivot.weightedDegree ≤ params.weightedDegreeBound
  let boundedEntry : Nat → Prop := fun idx ↦
    basis.getD idx 0 ≠ 0 ∧ degree idx ≤ params.weightedDegreeBound
  have hstep_well : ∀ best idx, wellBest best → wellBest (step best idx) := by
    intro best idx hbest
    unfold wellBest step degree at *
    by_cases hzero : basis.getD idx 0 = 0
    · convert hbest using 1
      simp [hzero]
    · have hzero' : ¬basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none =>
          simp [hzero', Array.getD_eq_getD_getElem?]
      | some current =>
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hstep_bounded_preserve : ∀ best idx, boundedBest best → boundedBest (step best idx) := by
    intro best idx hbest
    unfold boundedBest step degree at *
    by_cases hzero : basis.getD idx 0 = 0
    · convert hbest using 1
      simp [hzero]
    · have hzero' : ¬basis[idx]?.getD 0 = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      cases best with
      | none => contradiction
      | some current =>
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            have hle := koetterPivotBetter_weightedDegree_le hbetter
            have hbound :
                CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) ≤
                  params.weightedDegreeBound := by
              have hboundGetD :
                  CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) ≤
                    params.weightedDegreeBound :=
                le_trans hle hbest.2
              simpa [Array.getD_eq_getD_getElem?] using hboundGetD
            simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
            exact hbound
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := 0
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hstep_of_entry : ∀ best idx, wellBest best → boundedEntry idx →
      boundedBest (step best idx) := by
    intro best idx hwell hentry
    rcases hentry with ⟨hne, hbound⟩
    unfold wellBest boundedBest step degree at *
    have hzero' : ¬basis[idx]?.getD 0 = 0 := by
      simpa [Array.getD_eq_getD_getElem?] using hne
    have hbound' : CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
        (yWeight params) ≤ params.weightedDegreeBound := by
      simpa [Array.getD_eq_getD_getElem?] using hbound
    cases best with
    | none =>
        simp [hzero', Array.getD_eq_getD_getElem?]
        exact hbound'
    | some current =>
        by_cases hbetter :
            koetterPivotBetter
              ({ index := idx
                 discrepancy := 0
                 weightedDegree :=
                  CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                KoetterPivot F)
              current = true
        · have hbetter' :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true := by
            simpa [Array.getD_eq_getD_getElem?] using hbetter
          simp [hzero', hbetter', Array.getD_eq_getD_getElem?]
          exact hbound'
        · have hbetter' :
              ¬koetterPivotBetter
                ({ index := idx
                   discrepancy := 0
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true := by
            simpa [Array.getD_eq_getD_getElem?] using hbetter
          have hcurrentLe := koetterPivotBetter_not_weightedDegree_le hbetter
          have hcurrentBound : current.weightedDegree ≤ params.weightedDegreeBound :=
            le_trans hcurrentLe hbound
          simpa [hzero', hbetter'] using (And.intro hwell hcurrentBound)
  have hfold : ∀ (xs : List Nat) best,
      wellBest best →
      boundedBest best ∨ (∃ idx, idx ∈ xs ∧ boundedEntry idx) →
        boundedBest (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best _hwell h
        rcases h with hbest | hmem
        · simpa using hbest
        · rcases hmem with ⟨idx, hidx, _⟩
          simp at hidx
    | cons idx xs ih =>
        intro best hwell h
        simp only [List.foldl_cons]
        apply ih
        · exact hstep_well best idx hwell
        · rcases h with hbest | hmem
          · exact Or.inl (hstep_bounded_preserve best idx hbest)
          · rcases hmem with ⟨j, hj, hentry⟩
            simp at hj
            rcases hj with hji | hjxs
            · subst j
              exact Or.inl (hstep_of_entry best idx hwell hentry)
            · exact Or.inr ⟨j, hjxs, hentry⟩
  rcases hExists with ⟨idx, hidx, hne, hbound⟩
  have hbestBounded : boundedBest ((List.range basis.size).foldl step none) := by
    apply hfold
    · simp [wellBest]
    · exact Or.inr ⟨idx, by simpa using hidx, hne, hbound⟩
  cases hbest : (List.range basis.size).foldl step none with
  | none =>
      simp [hbest, boundedBest] at hbestBounded
  | some pivot =>
      refine ⟨basis.getD pivot.index 0, ?_⟩
      have hdeg' : CBivariate.natWeightedDegree (basis[pivot.index]?.getD 0) 1
          (yWeight params) ≤ params.weightedDegreeBound := by
        have hp := hbestBounded
        simp [hbest, boundedBest, degree, Array.getD_eq_getD_getElem?] at hp
        rw [← hp.1]
        exact hp.2
      simp [hdeg']

theorem koetterSelectPivot_some_discrepancy {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    pivot.discrepancy = koetterDiscrepancy constraint (basis.getD pivot.index 0) ∧
      pivot.discrepancy ≠ 0 := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot =>
        pivot.discrepancy = koetterDiscrepancy constraint (basis.getD pivot.index 0) ∧
          pivot.discrepancy ≠ 0
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best idx, good best → good (step best idx) := by
    intro best idx hbest
    unfold good step
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      convert hbest using 1
      simp [hzero']
    · have hne : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := by
        exact hzero
      cases best with
      | none =>
          have hne' : koetterDiscrepancy constraint (basis[idx]?.getD 0) ≠ 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hne
          simp [hne']
      | some current =>
          have hne' : koetterDiscrepancy constraint (basis[idx]?.getD 0) ≠ 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hne
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hne', hbetter']
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [good, hbetter', Array.getD_eq_getD_getElem?] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best, good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hbest
        simp only [List.foldl_cons]
        exact ih (step best idx) (hstep best idx hbest)
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    exact hfoldGoodAux (List.range basis.size) none (by simp [good])
  simpa [h, good] using hfoldGood

theorem koetterSelectPivot_some_index_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    pivot.index < basis.size := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot => pivot.index < basis.size
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best idx, idx ∈ List.range basis.size → good best → good (step best idx) := by
    intro best idx hidxMem hbest
    have hidx : idx < basis.size := by
      simpa using hidxMem
    unfold good step
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      simpa [hzero'] using hbest
    · cases best with
      | none =>
          have hzero' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          simpa [hzero'] using hidx
      | some current =>
          have hzero' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hzero
          by_cases hbetter :
              koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hidx
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simpa [hzero', hbetter'] using hbest
  have hfoldGoodAux : ∀ (xs : List Nat) best,
      (∀ idx, idx ∈ xs → idx < basis.size) → good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best _hxs hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hxs hbest
        simp only [List.foldl_cons]
        apply ih
        · intro j hj
          exact hxs j (by simp [hj])
        · exact hstep best idx (by simpa using hxs idx (by simp)) hbest
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    apply hfoldGoodAux (List.range basis.size) none
    · intro idx hidx
      simpa using hidx
    · simp [good]
  simpa [h, good] using hfoldGood

theorem koetterSelectPivot_some_weightedDegree_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    pivot.weightedDegree =
      CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params) := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let good : Option (KoetterPivot F) → Prop := fun best ↦
    match best with
    | none => True
    | some pivot =>
        pivot.weightedDegree =
          CBivariate.natWeightedDegree (basis.getD pivot.index 0) 1 (yWeight params)
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best idx, good best → good (step best idx) := by
    intro best idx hbest
    unfold good step
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzero' : koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
        simpa [Array.getD_eq_getD_getElem?] using hzero
      convert hbest using 1
      simp [hzero']
    · have hne : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := hzero
      cases best with
      | none =>
          have hne' : koetterDiscrepancy constraint (basis[idx]?.getD 0) ≠ 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hne
          simp [hne', Array.getD_eq_getD_getElem?]
      | some current =>
          have hne' : koetterDiscrepancy constraint (basis[idx]?.getD 0) ≠ 0 := by
            simpa [Array.getD_eq_getD_getElem?] using hne
          by_cases hbetter :
              (koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true)
          · have hbetter' :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hne', hbetter', Array.getD_eq_getD_getElem?]
          · have hbetter' :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            have hbest' :
                current.weightedDegree =
                  CBivariate.natWeightedDegree (basis[current.index]?.getD 0) 1
                    (yWeight params) := by
              simpa [good, Array.getD_eq_getD_getElem?] using hbest
            simpa [hbetter'] using hbest'
  have hfoldGoodAux : ∀ (xs : List Nat) best, good best → good (xs.foldl step best) := by
    intro xs
    induction xs with
    | nil =>
        intro best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro best hbest
        simp only [List.foldl_cons]
        exact ih (step best idx) (hstep best idx hbest)
  have hfoldGood : good ((List.range basis.size).foldl step none) := by
    exact hfoldGoodAux (List.range basis.size) none (by simp [good])
  simpa [h, good, Array.getD_eq_getD_getElem?] using hfoldGood

theorem koetterSelectPivot_some_weightedDegree_le {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    ∀ idx, idx < basis.size →
      koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 →
        pivot.weightedDegree ≤
          CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let degree : Nat → Nat := fun idx ↦
    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params)
  let nonzero : Nat → Prop := fun idx ↦
    koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0
  let bestLe : Option (KoetterPivot F) → List Nat → Prop := fun best seen ↦
    match best with
    | none => ∀ idx, idx ∈ seen → ¬ nonzero idx
    | some current =>
        current.weightedDegree = degree current.index ∧
          ∀ idx, idx ∈ seen → nonzero idx → current.weightedDegree ≤ degree idx
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best seen idx,
      bestLe best seen → bestLe (step best idx) (seen ++ [idx]) := by
    intro best seen idx hbest
    unfold bestLe step degree nonzero at *
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzeroBeq : (koetterDiscrepancy constraint (basis.getD idx 0) == 0) = true := by
        rw [hzero]
        simp
      rw [if_pos hzeroBeq]
      cases best with
      | none =>
          intro j hj
          rw [List.mem_append, List.mem_singleton] at hj
          rcases hj with hjSeen | hjIdx
          · exact hbest j hjSeen
          · subst j
            intro hnz
            exact hnz hzero
      | some current =>
          refine ⟨hbest.1, ?_⟩
          intro j hj hjnz
          rw [List.mem_append, List.mem_singleton] at hj
          rcases hj with hjSeen | hjIdx
          · exact hbest.2 j hjSeen hjnz
          · subst j
            exact False.elim (hjnz hzero)
    · have hne : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := hzero
      have hneBeq : ¬(koetterDiscrepancy constraint (basis.getD idx 0) == 0) = true := by
        intro hbeq
        exact hne (LawfulBEq.eq_of_beq hbeq)
      rw [if_neg hneBeq]
      cases best with
      | none =>
          constructor
          · rfl
          · intro j hj hjnz
            rw [List.mem_append, List.mem_singleton] at hj
            rcases hj with hjSeen | hjIdx
            · exact False.elim (hbest j hjSeen hjnz)
            · subst j
              exact le_rfl
      | some current =>
          by_cases hbetter :
              (koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true)
          · have hbetterGetElem :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hbetterGetElem]
            have hcandidateLeCurrent := koetterPivotBetter_weightedDegree_le hbetter
            intro j hj hjnz
            rcases hj with hjSeen | hjIdx
            · have hjnzGetD :
                  koetterDiscrepancy constraint (basis.getD j 0) ≠ 0 := by
                simpa [Array.getD_eq_getD_getElem?] using hjnz
              have hle := le_trans hcandidateLeCurrent
                (hbest.2 j hjSeen hjnzGetD)
              simpa [Array.getD_eq_getD_getElem?] using hle
            · subst j
              exact le_rfl
          · have hbetter' :
                ¬(koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis.getD idx 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true) := hbetter
            have hbetterGetElem :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter'
            simp [hbetterGetElem]
            have hcurrentLeCandidate := koetterPivotBetter_not_weightedDegree_le hbetter
            refine ⟨by simpa [Array.getD_eq_getD_getElem?] using hbest.1, ?_⟩
            intro j hj hjnz
            rcases hj with hjSeen | hjIdx
            · have hjnzGetD :
                  koetterDiscrepancy constraint (basis.getD j 0) ≠ 0 := by
                simpa [Array.getD_eq_getD_getElem?] using hjnz
              have hle := hbest.2 j hjSeen hjnzGetD
              simpa [Array.getD_eq_getD_getElem?] using hle
            · subst j
              simpa [Array.getD_eq_getD_getElem?] using hcurrentLeCandidate
  have hfold : ∀ xs seen best,
      bestLe best seen → bestLe (xs.foldl step best) (seen ++ xs) := by
    intro xs
    induction xs with
    | nil =>
        intro seen best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro seen best hbest
        simp only [List.foldl_cons]
        have hnext := hstep best seen idx hbest
        have htail := ih (seen ++ [idx]) (step best idx) hnext
        simpa [List.append_assoc] using htail
  have hbestLe : bestLe ((List.range basis.size).foldl step none) ([] ++ List.range basis.size) := by
    exact hfold (List.range basis.size) [] none (by simp [bestLe, nonzero])
  intro idx hidx hdisc
  have hpivotLe := by
    simpa [h, bestLe, degree, nonzero, Array.getD_eq_getD_getElem?] using hbestLe
  simpa [Array.getD_eq_getD_getElem?] using
    hpivotLe.2 idx (by simpa using hidx)
      (by simpa [Array.getD_eq_getD_getElem?] using hdisc)

theorem koetterSelectPivot_some_not_better {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {params : GSInterpParams} {constraint : InterpolationConstraint F}
    {basis : Array (CBivariate F)} {pivot : KoetterPivot F}
    (h : koetterSelectPivot params constraint basis = some pivot) :
    ∀ idx, idx < basis.size →
      koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 →
        ¬ koetterPivotBetter
          ({ index := idx
             discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
             weightedDegree :=
              CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
            KoetterPivot F)
          pivot = true := by
  unfold koetterSelectPivot at h
  let step : Option (KoetterPivot F) → Nat → Option (KoetterPivot F) :=
    fun best idx ↦
      let Q := basis.getD idx 0
      let delta := koetterDiscrepancy constraint Q
      if delta == 0 then best
      else
        let candidate : KoetterPivot F :=
          { index := idx
            discrepancy := delta
            weightedDegree := CBivariate.natWeightedDegree Q 1 (yWeight params) }
        match best with
        | none => some candidate
        | some current =>
            if koetterPivotBetter candidate current then some candidate else best
  let degree : Nat → Nat := fun idx ↦
    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params)
  let nonzero : Nat → Prop := fun idx ↦
    koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0
  let candidate : Nat → KoetterPivot F := fun idx ↦
    { index := idx
      discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
      weightedDegree := degree idx }
  let bestLe : Option (KoetterPivot F) → List Nat → Prop := fun best seen ↦
    match best with
    | none => ∀ idx, idx ∈ seen → ¬ nonzero idx
    | some current =>
        current.weightedDegree = degree current.index ∧
          ∀ idx, idx ∈ seen → nonzero idx →
            ¬ koetterPivotBetter (candidate idx) current = true
  change (List.range basis.size).foldl step none = some pivot at h
  have hstep : ∀ best seen idx,
      bestLe best seen → bestLe (step best idx) (seen ++ [idx]) := by
    intro best seen idx hbest
    unfold bestLe step degree nonzero candidate at *
    by_cases hzero : koetterDiscrepancy constraint (basis.getD idx 0) = 0
    · have hzeroBeq : (koetterDiscrepancy constraint (basis.getD idx 0) == 0) = true := by
        rw [hzero]
        simp
      rw [if_pos hzeroBeq]
      cases best with
      | none =>
          intro j hj
          rw [List.mem_append, List.mem_singleton] at hj
          rcases hj with hjSeen | hjIdx
          · exact hbest j hjSeen
          · subst j
            intro hnz
            exact hnz hzero
      | some current =>
          refine ⟨hbest.1, ?_⟩
          intro j hj hjnz
          rw [List.mem_append, List.mem_singleton] at hj
          rcases hj with hjSeen | hjIdx
          · exact hbest.2 j hjSeen hjnz
          · subst j
            exact False.elim (hjnz hzero)
    · have hne : koetterDiscrepancy constraint (basis.getD idx 0) ≠ 0 := hzero
      have hneBeq : ¬(koetterDiscrepancy constraint (basis.getD idx 0) == 0) = true := by
        intro hbeq
        exact hne (LawfulBEq.eq_of_beq hbeq)
      rw [if_neg hneBeq]
      cases best with
      | none =>
          constructor
          · rfl
          · intro j hj hjnz
            rw [List.mem_append, List.mem_singleton] at hj
            rcases hj with hjSeen | hjIdx
            · exact False.elim (hbest j hjSeen hjnz)
            · subst j
              simp [koetterPivotBetter, degree, Array.getD_eq_getD_getElem?]
      | some current =>
          by_cases hbetter :
              (koetterPivotBetter
                ({ index := idx
                   discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                   weightedDegree :=
                    CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
                  KoetterPivot F)
                current = true)
          · have hbetterGetElem :
                koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter
            simp [hbetterGetElem]
            intro j hj hjnz
            rcases hj with hjSeen | hjIdx
            · have hjnzGetD :
                  koetterDiscrepancy constraint (basis.getD j 0) ≠ 0 := by
                simpa [Array.getD_eq_getD_getElem?] using hjnz
              have hnot := hbest.2 j hjSeen hjnzGetD
              have hnot' :=
                koetterPivotBetter_not_of_better_left hbetter hnot
              have hnotGet :
                  ¬koetterPivotBetter
                    ({ index := j
                       discrepancy := koetterDiscrepancy constraint (basis[j]?.getD 0)
                       weightedDegree := degree j } :
                      KoetterPivot F)
                    ({ index := idx
                       discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                       weightedDegree :=
                        CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                          (yWeight params) } :
                      KoetterPivot F) = true := by
                simpa [Array.getD_eq_getD_getElem?, degree] using hnot'
              exact Bool.eq_false_iff.mpr hnotGet
            · subst j
              simp [koetterPivotBetter, degree, Array.getD_eq_getD_getElem?]
          · have hbetter' :
                ¬(koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis.getD idx 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true) := hbetter
            have hbetterGetElem :
                ¬koetterPivotBetter
                  ({ index := idx
                     discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                     weightedDegree :=
                      CBivariate.natWeightedDegree (basis[idx]?.getD 0) 1
                        (yWeight params) } :
                    KoetterPivot F)
                  current = true := by
              simpa [Array.getD_eq_getD_getElem?] using hbetter'
            simp [hbetterGetElem]
            refine ⟨by simpa [Array.getD_eq_getD_getElem?] using hbest.1, ?_⟩
            intro j hj hjnz
            rcases hj with hjSeen | hjIdx
            · have hjnzGetD :
                  koetterDiscrepancy constraint (basis.getD j 0) ≠ 0 := by
                simpa [Array.getD_eq_getD_getElem?] using hjnz
              have hnot := hbest.2 j hjSeen hjnzGetD
              have hnotGet :
                  ¬koetterPivotBetter
                    ({ index := j
                       discrepancy := koetterDiscrepancy constraint (basis[j]?.getD 0)
                       weightedDegree := degree j } :
                      KoetterPivot F)
                    current = true := by
                simpa [Array.getD_eq_getD_getElem?] using hnot
              exact Bool.eq_false_iff.mpr hnotGet
            · subst j
              have hnotGet :
                  ¬koetterPivotBetter
                    ({ index := idx
                       discrepancy := koetterDiscrepancy constraint (basis[idx]?.getD 0)
                       weightedDegree := degree idx } :
                      KoetterPivot F)
                    current = true := by
                simpa [Array.getD_eq_getD_getElem?, degree] using hbetter'
              exact Bool.eq_false_iff.mpr hnotGet
  have hfold : ∀ xs seen best,
      bestLe best seen → bestLe (xs.foldl step best) (seen ++ xs) := by
    intro xs
    induction xs with
    | nil =>
        intro seen best hbest
        simpa using hbest
    | cons idx xs ih =>
        intro seen best hbest
        simp only [List.foldl_cons]
        have hnext := hstep best seen idx hbest
        have htail := ih (seen ++ [idx]) (step best idx) hnext
        simpa [List.append_assoc] using htail
  have hbestLe : bestLe ((List.range basis.size).foldl step none) ([] ++ List.range basis.size) := by
    exact hfold (List.range basis.size) [] none (by simp [bestLe, nonzero])
  intro idx hidx hdisc
  have hpivotNot := by
    simpa [h, bestLe, degree, nonzero, candidate, Array.getD_eq_getD_getElem?] using hbestLe
  have hdisc' : ¬koetterDiscrepancy constraint (basis[idx]?.getD 0) = 0 := by
    simpa [Array.getD_eq_getD_getElem?] using hdisc
  have hfalse := hpivotNot.2 idx (by simpa using hidx) hdisc'
  intro htrue
  have hfalseGetD :
      koetterPivotBetter
        ({ index := idx
           discrepancy := koetterDiscrepancy constraint (basis.getD idx 0)
           weightedDegree :=
            CBivariate.natWeightedDegree (basis.getD idx 0) 1 (yWeight params) } :
          KoetterPivot F)
        pivot = false := by
    simpa [Array.getD_eq_getD_getElem?] using hfalse
  rw [hfalseGetD] at htrue
  simp at htrue

end GuruswamiSudan

end CompPoly
