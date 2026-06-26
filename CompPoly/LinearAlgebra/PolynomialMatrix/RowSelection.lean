/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Operations

/-!
# Least-Shifted-Degree Row Selection Helpers

Correctness facts for the generic least-shifted-degree row scan in
`PolynomialMatrix.Operations`.
-/

namespace CompPoly



namespace PolynomialMatrix



variable {F : Type*} [Field F] [BEq F]

def RowChoiceValid (M : PolynomialMatrix F) (shift : Array Nat)
    (choice : RowChoice F) : Prop :=
  choice.index < M.size ∧ choice.row = M.getD choice.index #[] ∧
    rowShiftedDegree? choice.row shift = some choice.degree

omit [BEq F] in
private theorem betterRowChoice_true_candidate_degree_le
    {candidate current : RowChoice F}
    (h : betterRowChoice candidate current = true) :
    candidate.degree ≤ current.degree := by
  unfold betterRowChoice at h
  simp at h
  rcases h with hlt | ⟨heq, _hidx⟩
  · omega
  · have hdegree : candidate.degree = current.degree := heq
    omega
omit [BEq F] in
private theorem betterRowChoice_false_current_degree_le
    {candidate current : RowChoice F}
    (h : betterRowChoice candidate current = false) :
    current.degree ≤ candidate.degree := by
  unfold betterRowChoice at h
  by_cases hlt : candidate.degree < current.degree
  · simp [hlt] at h
  · omega

omit [BEq F] in
private theorem betterRowChoice_not_true_current_degree_le
    {candidate current : RowChoice F}
    (h : ¬ betterRowChoice candidate current = true) :
    current.degree ≤ candidate.degree :=
  betterRowChoice_false_current_degree_le (Bool.eq_false_iff.mpr h)


private theorem leastShiftedDegreeRowStep?_none
    {M : PolynomialMatrix F} {shift : Array Nat}
    {best : Option (RowChoice F)} {i : Nat}
    (h : leastShiftedDegreeRowStep? M shift best i = none) :
    best = none ∧ rowShiftedDegree? (M[i]?.getD #[]) shift = none := by
  unfold leastShiftedDegreeRowStep? at h
  cases hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      have hbest : best = none := by
        simpa [leastShiftedDegreeRowStep?, hdeg] using h
      exact ⟨hbest, rfl⟩
  | some degree =>
      cases best with
      | none =>
          simp [hdeg] at h
      | some current =>
          by_cases hbetter :
              betterRowChoice { index := i, row := M[i]?.getD #[], degree := degree } current
          · simp [hdeg, hbetter] at h
          · simp [hdeg, hbetter] at h


private theorem leastShiftedDegreeRowStep?_some_of_best_some
    {M : PolynomialMatrix F} {shift : Array Nat}
    {best : Option (RowChoice F)} {current : RowChoice F} {i : Nat}
    (hbest : best = some current) :
    ∃ choice, leastShiftedDegreeRowStep? M shift best i = some choice := by
  unfold leastShiftedDegreeRowStep?
  cases hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      refine ⟨current, ?_⟩
      simp [hbest, hdeg]
  | some degree =>
      by_cases hbetter :
          betterRowChoice { index := i, row := M[i]?.getD #[], degree := degree } current
      · exact ⟨{ index := i, row := M[i]?.getD #[], degree := degree },
          by simp [hbest, hdeg, hbetter]⟩
      · exact ⟨current,
          by simp [hbest, hdeg, hbetter]⟩


private theorem leastShiftedDegreeRowStep?_preserves_degree_le
    {M : PolynomialMatrix F} {shift : Array Nat}
    {best : Option (RowChoice F)} {choice : RowChoice F} {d i : Nat}
    (hbest : ∃ current, best = some current ∧ current.degree ≤ d)
    (hstep : leastShiftedDegreeRowStep? M shift best i = some choice) :
    choice.degree ≤ d := by
  rcases hbest with ⟨current, hbest, hcurrent⟩
  unfold leastShiftedDegreeRowStep? at hstep
  cases hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      have hstep' : some current = some choice := by
        simpa [leastShiftedDegreeRowStep?, hdeg, hbest] using hstep
      have hchoice : choice = current := by
        injection hstep' with hEq
        exact hEq.symm
      rw [hchoice]
      exact hcurrent
  | some degree =>
      let candidate : RowChoice F :=
        { index := i, row := M[i]?.getD #[], degree := degree }
      by_cases hbetter : betterRowChoice candidate current
      · have hstep' : some candidate = some choice := by
          simpa [leastShiftedDegreeRowStep?, hdeg, hbest, candidate, hbetter] using hstep
        have hchoice : choice = candidate := by
          injection hstep' with hEq
          exact hEq.symm
        rw [hchoice]
        exact le_trans (betterRowChoice_true_candidate_degree_le hbetter) hcurrent
      · have hstep' : some current = some choice := by
          simpa [leastShiftedDegreeRowStep?, hdeg, hbest, candidate, hbetter] using hstep
        have hchoice : choice = current := by
          injection hstep' with hEq
          exact hEq.symm
        rw [hchoice]
        exact hcurrent


private theorem leastShiftedDegreeRowStep?_degree_le_of_row
    {M : PolynomialMatrix F} {shift : Array Nat}
    {best : Option (RowChoice F)} {choice : RowChoice F} {d i : Nat}
    (hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift = some d)
    (hstep : leastShiftedDegreeRowStep? M shift best i = some choice) :
    choice.degree ≤ d := by
  let candidate : RowChoice F := { index := i, row := M[i]?.getD #[], degree := d }
  cases best with
  | none =>
      have hstep' : some candidate = some choice := by
        simpa [leastShiftedDegreeRowStep?, hdeg, candidate] using hstep
      have hchoice : choice = candidate := by
        injection hstep' with hEq
        exact hEq.symm
      simp [hchoice, candidate]
  | some current =>
      by_cases hbetter : betterRowChoice candidate current
      · have hstep' : some candidate = some choice := by
          simpa [leastShiftedDegreeRowStep?, hdeg, candidate, hbetter] using hstep
        have hchoice : choice = candidate := by
          injection hstep' with hEq
          exact hEq.symm
        simp [hchoice, candidate]
      · have hstep' : some current = some choice := by
          simpa [leastShiftedDegreeRowStep?, hdeg, candidate, hbetter] using hstep
        have hchoice : choice = current := by
          injection hstep' with hEq
          exact hEq.symm
        rw [hchoice]
        exact betterRowChoice_not_true_current_degree_le hbetter


private theorem leastShiftedDegreeFold_some_of_best_some
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {best : Option (RowChoice F)} {current : RowChoice F}
    (hbest : best = some current) :
    ∃ choice,
      xs.foldl (leastShiftedDegreeRowStep? M shift) best = some choice := by
  induction xs generalizing best current with
  | nil =>
      exact ⟨current, hbest⟩
  | cons i xs ih =>
      rcases leastShiftedDegreeRowStep?_some_of_best_some
          (M := M) (shift := shift) (i := i) hbest with
        ⟨choice, hstep⟩
      exact ih (best := leastShiftedDegreeRowStep? M shift best i)
        (current := choice) hstep

private theorem leastShiftedDegreeFold_preserves_degree_le
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {best : Option (RowChoice F)} {choice : RowChoice F} {d : Nat}
    (hbest : ∃ current, best = some current ∧ current.degree ≤ d)
    (hfold : xs.foldl (leastShiftedDegreeRowStep? M shift) best = some choice) :
    choice.degree ≤ d := by
  induction xs generalizing best with
  | nil =>
      rcases hbest with ⟨current, hbest, hcurrent⟩
      rw [hbest] at hfold
      cases hfold
      exact hcurrent
  | cons i xs ih =>
      rcases hbest with ⟨current, hbest, hcurrent⟩
      rcases leastShiftedDegreeRowStep?_some_of_best_some
          (M := M) (shift := shift) (i := i) hbest with
        ⟨stepChoice, hstep⟩
      have hstepBound : stepChoice.degree ≤ d :=
        leastShiftedDegreeRowStep?_preserves_degree_le
          (M := M) (shift := shift) (i := i)
          ⟨current, hbest, hcurrent⟩ hstep
      exact ih (best := leastShiftedDegreeRowStep? M shift best i)
        ⟨stepChoice, hstep, hstepBound⟩
        (by simpa only [List.foldl_cons] using hfold)

private theorem leastShiftedDegreeFold_degree_le_of_mem
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {best : Option (RowChoice F)} {choice : RowChoice F}
    {i d : Nat}
    (hfold : xs.foldl (leastShiftedDegreeRowStep? M shift) best = some choice)
    (hi : i ∈ xs)
    (hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift = some d) :
    choice.degree ≤ d := by
  induction xs generalizing best with
  | nil =>
      simp at hi
  | cons x xs ih =>
      simp at hi
      rcases hi with hix | hi
      · subst x
        cases hstep : leastShiftedDegreeRowStep? M shift best i with
        | none =>
            rcases leastShiftedDegreeRowStep?_none hstep with ⟨_hbest, hrowNone⟩
            rw [hrowNone] at hdeg
            contradiction
        | some stepChoice =>
            have hstepBound : stepChoice.degree ≤ d :=
              leastShiftedDegreeRowStep?_degree_le_of_row hdeg hstep
            exact leastShiftedDegreeFold_preserves_degree_le
              (M := M) (shift := shift) xs
              ⟨stepChoice, rfl, hstepBound⟩
              (by simpa [hstep] using hfold)
      · exact ih (best := leastShiftedDegreeRowStep? M shift best x)
          (by simpa only [List.foldl_cons] using hfold) hi

private theorem leastShiftedDegreeFold_none
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {best : Option (RowChoice F)}
    (hfold : xs.foldl (leastShiftedDegreeRowStep? M shift) best = none) :
    best = none ∧
      ∀ i, i ∈ xs → rowShiftedDegree? (M[i]?.getD #[]) shift = none := by
  induction xs generalizing best with
  | nil =>
      exact ⟨hfold, by simp⟩
  | cons i xs ih =>
      have htail := ih (best := leastShiftedDegreeRowStep? M shift best i)
        (by simpa only [List.foldl_cons] using hfold)
      rcases leastShiftedDegreeRowStep?_none htail.1 with ⟨hbest, hrow⟩
      refine ⟨hbest, ?_⟩
      intro j hj
      simp at hj
      rcases hj with hji | hj
      · subst j
        exact hrow
      · exact htail.2 j hj


private theorem leastShiftedDegreeFold_valid
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {best : Option (RowChoice F)}
    (hbest : ∀ choice, best = some choice → RowChoiceValid M shift choice)
    (hxs : ∀ i, i ∈ xs → i < M.size) :
    ∀ choice,
      xs.foldl (leastShiftedDegreeRowStep? M shift) best = some choice →
        RowChoiceValid M shift choice := by
  induction xs generalizing best with
  | nil =>
      intro choice hfold
      exact hbest choice hfold
  | cons i xs ih =>
      intro choice hfold
      have hstepValid :
          ∀ stepChoice,
            leastShiftedDegreeRowStep? M shift best i = some stepChoice →
              RowChoiceValid M shift stepChoice := by
        intro stepChoice hstep
        cases hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift with
        | none =>
            have hstep' : best = some stepChoice := by
              simpa [leastShiftedDegreeRowStep?, hdeg] using hstep
            exact hbest stepChoice hstep'
        | some degree =>
            let candidate : RowChoice F :=
              { index := i, row := M[i]?.getD #[], degree := degree }
            cases best with
            | none =>
                have hstep' : some candidate = some stepChoice := by
                  simpa [leastShiftedDegreeRowStep?, hdeg, candidate] using hstep
                have hstepChoice : stepChoice = candidate := by
                  injection hstep' with hEq
                  exact hEq.symm
                rw [hstepChoice]
                exact ⟨by simpa [candidate] using hxs i (by simp),
                  by simp [candidate, Array.getD_eq_getD_getElem?],
                  by simpa [candidate] using hdeg⟩
            | some current =>
                by_cases hbetter : betterRowChoice candidate current
                · have hstep' : some candidate = some stepChoice := by
                    simpa [leastShiftedDegreeRowStep?, hdeg, candidate, hbetter] using hstep
                  have hstepChoice : stepChoice = candidate := by
                    injection hstep' with hEq
                    exact hEq.symm
                  rw [hstepChoice]
                  exact ⟨by simpa [candidate] using hxs i (by simp),
                    by simp [candidate, Array.getD_eq_getD_getElem?],
                    by simpa [candidate] using hdeg⟩
                · have hstep' : some current = some stepChoice := by
                    simpa [leastShiftedDegreeRowStep?, hdeg, candidate, hbetter] using hstep
                  have hstepChoice : stepChoice = current := by
                    injection hstep' with hEq
                    exact hEq.symm
                  rw [hstepChoice]
                  exact hbest current rfl
      exact ih
        (best := leastShiftedDegreeRowStep? M shift best i)
        hstepValid
        (by
          intro j hj
          exact hxs j (by simp [hj]))
        choice
        (by simpa only [List.foldl_cons] using hfold)


theorem leastShiftedDegreeChoice?_some_valid
    {M : PolynomialMatrix F} {shift : Array Nat} {choice : RowChoice F}
    (hchoice : leastShiftedDegreeChoice? M shift = some choice) :
    RowChoiceValid M shift choice := by
  unfold leastShiftedDegreeChoice? at hchoice
  exact leastShiftedDegreeFold_valid
    (M := M) (shift := shift) (List.range M.size)
    (by intro choice h; cases h)
    (by intro i hi; exact List.mem_range.mp hi)
    choice hchoice


theorem leastShiftedDegreeChoice?_degree_le
    {M : PolynomialMatrix F} {shift : Array Nat}
    {choice : RowChoice F} {i d : Nat}
    (hchoice : leastShiftedDegreeChoice? M shift = some choice)
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some d) :
    choice.degree ≤ d := by
  unfold leastShiftedDegreeChoice? at hchoice
  have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = some d := by
    simpa [Array.getD_eq_getD_getElem?] using hdeg
  exact leastShiftedDegreeFold_degree_le_of_mem
    (M := M) (shift := shift) (List.range M.size)
    hchoice (List.mem_range.mpr hi) hdeg'


theorem leastShiftedDegreeChoice?_some_of_degree
    {M : PolynomialMatrix F} {shift : Array Nat} {i d : Nat}
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some d) :
    ∃ choice, leastShiftedDegreeChoice? M shift = some choice ∧ choice.degree ≤ d := by
  cases hchoice : leastShiftedDegreeChoice? M shift with
  | none =>
      unfold leastShiftedDegreeChoice? at hchoice
      rcases leastShiftedDegreeFold_none
          (M := M) (shift := shift) (List.range M.size) hchoice with
        ⟨_hbest, hall⟩
      have hnone := hall i (List.mem_range.mpr hi)
      have hnone' : rowShiftedDegree? (M.getD i #[]) shift = none := by
        simpa [Array.getD_eq_getD_getElem?] using hnone
      rw [hnone'] at hdeg
      contradiction
  | some choice =>
      refine ⟨choice, rfl, ?_⟩
      exact leastShiftedDegreeChoice?_degree_le hchoice hi hdeg


theorem leastShiftedDegreeRow?_some_valid
    {M : PolynomialMatrix F} {shift : Array Nat} {row : PolynomialRow F}
    (hrow : leastShiftedDegreeRow? M shift = some row) :
    ∃ choice,
      leastShiftedDegreeChoice? M shift = some choice ∧
        RowChoiceValid M shift choice ∧ choice.row = row := by
  unfold leastShiftedDegreeRow? at hrow
  cases hchoice : leastShiftedDegreeChoice? M shift with
  | none =>
      simp [hchoice] at hrow
  | some choice =>
      simp [hchoice] at hrow
      refine ⟨choice, rfl, leastShiftedDegreeChoice?_some_valid hchoice, ?_⟩
      exact hrow

end PolynomialMatrix



end CompPoly
