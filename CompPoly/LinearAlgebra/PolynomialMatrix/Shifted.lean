/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Degree

/-!
# Shifted Degrees for Polynomial Rows
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*}

/-- Shifted leading term metadata for a nonzero row. -/
structure ShiftedLeadingTerm (F : Type*) where
  position : Nat
  degree : Nat
  shiftedDegree : Nat
  coeff : F
deriving Repr

private def maxOption : Option Nat → Nat → Option Nat
  | none, n => some n
  | some m, n => some (max m n)

/-- Shifted degree of one row entry. Zero entries have no degree. -/
def shiftedEntryDegree? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) (j : Nat) : Option Nat :=
  let p := rowGet row j
  if p == 0 then none else some (p.natDegree + shift.getD j 0)

/-- Shifted degree of a row, with `none` exactly for zero rows. -/
def rowShiftedDegree? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) : Option Nat :=
  (List.range row.size).foldl
    (fun acc j ↦
      match shiftedEntryDegree? row shift j with
      | none => acc
      | some d => maxOption acc d)
    none

/-- Shifted leading position of a nonzero row. Ties use the largest column index. -/
def rowShiftedLeadingPosition? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) : Option Nat :=
  match rowShiftedDegree? row shift with
  | none => none
  | some d =>
      (List.range row.size).reverse.find? fun j ↦
        match shiftedEntryDegree? row shift j with
        | some dj => dj == d
        | none => false

/-- Shifted leading term metadata for a nonzero row. -/
def rowShiftedLeadingTerm? [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) :
    Option (ShiftedLeadingTerm F) :=
  match rowShiftedDegree? row shift, rowShiftedLeadingPosition? row shift with
  | some shiftedDegree, some j =>
      let p := rowGet row j
      if p == 0 then
        none
      else
        some
          { position := j
            degree := p.natDegree
            shiftedDegree := shiftedDegree
            coeff := p.coeff p.natDegree }
  | _, _ => none

private theorem shiftedEntryDegree?_eq_none_iff [Zero F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (shift : Array Nat) (j : Nat) :
    shiftedEntryDegree? row shift j = none ↔ rowGet row j = 0 := by
  simp [shiftedEntryDegree?, rowGet]

private theorem rowShiftedDegreeFold_none_iff [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) :
    ∀ (xs : List Nat) (acc : Option Nat),
      xs.foldl
          (fun acc j ↦
            match shiftedEntryDegree? row shift j with
            | none => acc
            | some d => maxOption acc d)
          acc = none ↔
        acc = none ∧ ∀ j, j ∈ xs → shiftedEntryDegree? row shift j = none := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp
  | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih]
      cases hx : shiftedEntryDegree? row shift x <;> cases acc <;> simp [maxOption, hx]

private theorem rowShiftedDegreeFold_acc_le_of_some [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) :
    ∀ (xs : List Nat) (a d : Nat),
      xs.foldl
          (fun acc j ↦
            match shiftedEntryDegree? row shift j with
            | none => acc
            | some e => maxOption acc e)
          (some a) = some d →
        a ≤ d := by
  intro xs
  induction xs with
  | nil =>
      intro a d h
      exact le_of_eq (Option.some.inj h)
  | cons x xs ih =>
      intro a d h
      cases hx : shiftedEntryDegree? row shift x with
      | none =>
          exact ih a d (by simpa [hx] using h)
      | some e =>
          have hle := ih (max a e) d (by simpa [hx, maxOption] using h)
          exact le_trans (Nat.le_max_left a e) hle

private theorem rowShiftedDegreeFold_entry_le_of_some [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) :
    ∀ (xs : List Nat) (acc : Option Nat) (d j e : Nat),
      xs.foldl
          (fun acc j ↦
            match shiftedEntryDegree? row shift j with
            | none => acc
            | some e => maxOption acc e)
          acc = some d →
        j ∈ xs →
        shiftedEntryDegree? row shift j = some e →
        e ≤ d := by
  intro xs
  induction xs with
  | nil =>
      intro acc d j e _ hmem _
      cases hmem
  | cons x xs ih =>
      intro acc d j e hfold hmem hentry
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · cases acc with
        | none =>
            exact rowShiftedDegreeFold_acc_le_of_some row shift xs e d
              (by simpa [hentry, maxOption] using hfold)
        | some a =>
            have hle := rowShiftedDegreeFold_acc_le_of_some row shift xs (max a e) d
              (by simpa [hentry, maxOption] using hfold)
            exact le_trans (Nat.le_max_right a e) hle
      · exact ih
          (match shiftedEntryDegree? row shift x with
          | none => acc
          | some e => maxOption acc e)
          d j e (by simpa [List.foldl_cons] using hfold) hmem hentry

private theorem rowShiftedDegreeFold_some_acc_or_mem [Zero F] [BEq F]
    (row : PolynomialRow F) (shift : Array Nat) :
    ∀ (xs : List Nat) (acc : Option Nat) (d : Nat),
      xs.foldl
          (fun acc j ↦
            match shiftedEntryDegree? row shift j with
            | none => acc
            | some e => maxOption acc e)
          acc = some d →
        acc = some d ∨ ∃ j, j ∈ xs ∧ shiftedEntryDegree? row shift j = some d := by
  intro xs
  induction xs with
  | nil =>
      intro acc d h
      exact Or.inl h
  | cons x xs ih =>
      intro acc d h
      have htail := ih
        (match shiftedEntryDegree? row shift x with
        | none => acc
        | some e => maxOption acc e)
        d (by simpa [List.foldl_cons] using h)
      rcases htail with hacc | ⟨j, hj, hentry⟩
      · cases hx : shiftedEntryDegree? row shift x with
        | none =>
            left
            simpa [hx] using hacc
        | some e =>
            cases acc with
            | none =>
                right
                refine ⟨x, by simp, ?_⟩
                simpa [hx, maxOption] using hacc
            | some a =>
                have hmax : max a e = d := by
                  simpa [hx, maxOption] using hacc
                by_cases he_le_a : e ≤ a
                · left
                  have hmax_left : max a e = a := max_eq_left he_le_a
                  simpa [hmax_left] using hmax
                · right
                  refine ⟨x, by simp, ?_⟩
                  have ha_le_e : a ≤ e := Nat.le_of_not_ge he_le_a
                  have hmax_right : max a e = e := max_eq_right ha_le_e
                  simpa [hx, hmax_right] using hmax
      · right
        exact ⟨j, by simp [hj], hentry⟩

private theorem rowIsZero_iff_forall_rowGet [Zero F] [BEq F] [LawfulBEq F]
    {row : PolynomialRow F} :
    RowIsZero row ↔ ∀ j, j < row.size → rowGet row j = 0 := by
  constructor
  · intro hz j hj
    exact hz (rowGet row j) (by
      unfold rowGet
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
      exact Array.getElem_mem_toList hj)
  · intro h p hp
    rcases List.getElem_of_mem hp with ⟨j, hj, hget⟩
    rw [← hget]
    simpa [rowGet, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by simpa using hj), Array.getElem_toList] using
      h j (by simpa using hj)

/-- Nonzero rows are exactly the rows with a shifted degree. -/
theorem rowShiftedDegree?_eq_none_iff [Zero F] [BEq F] [LawfulBEq F]
    {row : PolynomialRow F} {shift : Array Nat} :
    rowShiftedDegree? row shift = none ↔ RowIsZero row := by
  rw [rowShiftedDegree?]
  rw [rowShiftedDegreeFold_none_iff row shift (List.range row.size) none]
  simp only [true_and]
  rw [rowIsZero_iff_forall_rowGet]
  constructor
  · intro h j hj
    exact (shiftedEntryDegree?_eq_none_iff row shift j).1 (h j (List.mem_range.mpr hj))
  · intro h j hj
    exact (shiftedEntryDegree?_eq_none_iff row shift j).2 (h j (List.mem_range.mp hj))

/-- A returned shifted row degree bounds every nonzero shifted entry degree. -/
theorem shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some
    [Zero F] [BEq F]
    {row : PolynomialRow F} {shift : Array Nat} {d j e : Nat}
    (hdeg : rowShiftedDegree? row shift = some d)
    (hj : j < row.size)
    (hentry : shiftedEntryDegree? row shift j = some e) :
    e ≤ d := by
  exact rowShiftedDegreeFold_entry_le_of_some row shift (List.range row.size) none d j e
    (by simpa [rowShiftedDegree?] using hdeg) (List.mem_range.mpr hj) hentry

/-- A returned shifted row degree is attained by some row entry. -/
theorem exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some
    [Zero F] [BEq F]
    {row : PolynomialRow F} {shift : Array Nat} {d : Nat}
    (hdeg : rowShiftedDegree? row shift = some d) :
    ∃ j, j < row.size ∧ shiftedEntryDegree? row shift j = some d := by
  have h :=
    rowShiftedDegreeFold_some_acc_or_mem row shift (List.range row.size) none d
      (by simpa [rowShiftedDegree?] using hdeg)
  rcases h with hnone | ⟨j, hj, hentry⟩
  · simp at hnone
  · exact ⟨j, List.mem_range.mp hj, hentry⟩

/-- A shifted weak-Popov matrix has distinct leading positions among nonzero rows. -/
def ShiftedWeakPopov [Zero F] [BEq F]
    (M : PolynomialMatrix F) (shift : Array Nat) : Prop :=
  ∀ i j,
    i < M.size →
    j < M.size →
    i ≠ j →
    rowShiftedLeadingPosition? (M.getD i #[]) shift ≠ none →
    rowShiftedLeadingPosition? (M.getD j #[]) shift ≠ none →
      rowShiftedLeadingPosition? (M.getD i #[]) shift ≠
        rowShiftedLeadingPosition? (M.getD j #[]) shift

end PolynomialMatrix

end CompPoly
