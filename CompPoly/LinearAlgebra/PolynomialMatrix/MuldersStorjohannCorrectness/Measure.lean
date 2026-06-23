/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohannCorrectness.Leading

/-!
# Mulders-Storjohann Correctness Termination Measure Helpers

Measure-decrease and fuel-bound lemmas for Mulders-Storjohann reduction.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

def shiftedRowMeasure (row : PolynomialRow F) (shift : Array Nat) : Nat :=
  match rowShiftedDegree? row shift, rowShiftedLeadingPosition? row shift with
  | some degree, some position => degree * (row.size + 1) + (position + 1)
  | _, _ => 0

def shiftedMatrixMeasure (M : PolynomialMatrix F) (shift : Array Nat) : Nat :=
  (List.range M.size).foldl
    (fun acc i ↦ acc + shiftedRowMeasure (M.getD i #[]) shift)
    0

theorem cancelShiftedLeadingTerm_shiftedRowMeasure_lt
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hsize : reducer.size = target.size) :
    shiftedRowMeasure (cancelShiftedLeadingTerm target reducer shift) shift <
      shiftedRowMeasure target shift := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨htRowDegree, htLeadingPos, _, _, _, _⟩
  have hcancelSize :
      (cancelShiftedLeadingTerm target reducer shift).size = target.size :=
    cancelShiftedLeadingTerm_size hsize
  have hnoTarget :=
    cancelShiftedLeadingTerm_no_target_shifted_entry ht hr hpos hle
  have hentryBound :
      ∀ k, k < (cancelShiftedLeadingTerm target reducer shift).size →
        rowGet (cancelShiftedLeadingTerm target reducer shift) k ≠ 0 →
        (rowGet (cancelShiftedLeadingTerm target reducer shift) k).natDegree +
            shift.getD k 0 ≤ t.shiftedDegree := by
    intro k hk hne
    apply cancelShiftedLeadingTerm_entry_bound ht hr hpos hle hsize
    · simpa [hcancelSize] using hk
    · exact hne
  unfold shiftedRowMeasure
  rw [htRowDegree, htLeadingPos]
  cases hnewDegree :
      rowShiftedDegree? (cancelShiftedLeadingTerm target reducer shift) shift with
  | none =>
      simp
  | some newDegree =>
      have hnewDegreeLe :
          newDegree ≤ t.shiftedDegree :=
        rowShiftedDegree?_le_of_entry_bound hentryBound hnewDegree
      cases hnewPos :
          rowShiftedLeadingPosition? (cancelShiftedLeadingTerm target reducer shift) shift with
      | none =>
          simp
      | some newPos =>
          have hnewPosCancel :
              newPos < (cancelShiftedLeadingTerm target reducer shift).size :=
            rowShiftedLeadingPosition?_lt hnewPos
          have hnewPosTarget : newPos < target.size := by
            simpa [hcancelSize] using hnewPosCancel
          have hnewEntry :
              shiftedEntryDegree? (cancelShiftedLeadingTerm target reducer shift) shift
                newPos = some newDegree :=
            rowShiftedLeadingPosition?_entry_eq hnewDegree hnewPos
          by_cases hdegreeLt : newDegree < t.shiftedDegree
          · have hposBound : newPos + 1 ≤ target.size := by omega
            have hsuccLe : newDegree + 1 ≤ t.shiftedDegree := by omega
            have hmulLe :
                (newDegree + 1) * (target.size + 1) ≤
                  t.shiftedDegree * (target.size + 1) :=
              Nat.mul_le_mul_right (target.size + 1) hsuccLe
            simp [hcancelSize]
            nlinarith
          · have hdegreeEq : newDegree = t.shiftedDegree := by omega
            have hnewEntryTarget :
                shiftedEntryDegree? (cancelShiftedLeadingTerm target reducer shift) shift
                  newPos = some t.shiftedDegree := by
              simpa [hdegreeEq] using hnewEntry
            rcases shiftedEntryDegree?_eq_some_iff_data.1 hnewEntryTarget with
              ⟨hnewNonzero, hnewEntryEq⟩
            have hnewPosLtTarget : newPos < t.position := by
              by_cases heq : newPos = t.position
              · subst newPos
                exact False.elim (hnoTarget hnewEntryTarget)
              · by_cases hright : t.position < newPos
                · have hstrict :=
                    cancelShiftedLeadingTerm_entry_strict_of_pos_lt ht hr hpos hle hsize
                      hnewPosTarget hright hnewNonzero
                  omega
                · omega
            simp [hcancelSize, hdegreeEq]
            omega

theorem foldRange_add_eq_of_pointwise
    (n : Nat) {f g : Nat → Nat}
    (heq : ∀ k, k < n → f k = g k) :
    (List.range n).foldl (fun acc k ↦ acc + f k) 0 =
      (List.range n).foldl (fun acc k ↦ acc + g k) 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by intro k hk; exact heq k (by omega)), heq n (by omega)]

theorem foldRange_add_lt_of_pointwise_lt
    (n : Nat) {f g : Nat → Nat} {idx : Nat}
    (hidx : idx < n)
    (hlt : f idx < g idx)
    (heq : ∀ k, k < n → k ≠ idx → f k = g k) :
    (List.range n).foldl (fun acc k ↦ acc + f k) 0 <
      (List.range n).foldl (fun acc k ↦ acc + g k) 0 := by
  induction n generalizing idx with
  | zero =>
      omega
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hlast : idx = n
      · subst idx
        have hprefix :
            (List.range n).foldl (fun acc k ↦ acc + f k) 0 =
              (List.range n).foldl (fun acc k ↦ acc + g k) 0 := by
          apply foldRange_add_eq_of_pointwise
          intro k hk
          exact heq k (by omega) (by omega)
        rw [hprefix]
        omega
      · have hidxPrefix : idx < n := by omega
        have hprefixLt :
            (List.range n).foldl (fun acc k ↦ acc + f k) 0 <
              (List.range n).foldl (fun acc k ↦ acc + g k) 0 :=
          ih hidxPrefix hlt (by
            intro k hk hne
            exact heq k (by omega) hne)
        have hlastEq : f n = g n := heq n (by omega) (by omega)
        rw [hlastEq]
        omega

omit [LawfulBEq F] [DecidableEq F] in
theorem shiftedMatrixMeasure_replaceRow_lt
    {M : PolynomialMatrix F} {shift : Array Nat} {idx : Nat} {newRow : PolynomialRow F}
    (hidx : idx < M.size)
    (hlt : shiftedRowMeasure newRow shift <
      shiftedRowMeasure (M.getD idx #[]) shift) :
    shiftedMatrixMeasure (replaceRow M idx newRow) shift <
      shiftedMatrixMeasure M shift := by
  unfold shiftedMatrixMeasure
  rw [replaceRow_size]
  apply foldRange_add_lt_of_pointwise_lt
    (n := M.size) (idx := idx)
    (f := fun i ↦ shiftedRowMeasure ((replaceRow M idx newRow).getD i #[]) shift)
    (g := fun i ↦ shiftedRowMeasure (M.getD i #[]) shift)
  · exact hidx
  · have hgetNew : (replaceRow M idx newRow).getD idx #[] = newRow := by
      simp [replaceRow, Array.getD_eq_getD_getElem?, hidx]
    simpa [hgetNew] using hlt
  · intro k hk hne
    have hgetOld : (replaceRow M idx newRow).getD k #[] = M.getD k #[] := by
      have hne' : idx ≠ k := fun h ↦ hne h.symm
      simp [replaceRow, Array.getD_eq_getD_getElem?, hne']
    simp [hgetOld]

theorem muldersStorjohannStep_shiftedMatrixMeasure_lt
    {M : PolynomialMatrix F} {shift : Array Nat} {i j : Nat}
    (hM : WellFormed M)
    (hconf : shiftedLeadingConflict? M shift = some (i, j)) :
    shiftedMatrixMeasure (muldersStorjohannStep M shift i j) shift <
      shiftedMatrixMeasure M shift := by
  rcases shiftedLeadingConflict?_some_bounds hconf with ⟨hi, hj, _hij⟩
  rcases shiftedLeadingConflict?_some_valid hconf with
    ⟨pos, hposI, hposJ⟩
  rcases rowShiftedLeadingTerm?_some_of_position hposI with
    ⟨termI, htermI, htermIpos⟩
  rcases rowShiftedLeadingTerm?_some_of_position hposJ with
    ⟨termJ, htermJ, htermJpos⟩
  rcases rowShiftedLeadingTerm?_some_data htermI with
    ⟨hdegI, _, _, _, _, _⟩
  rcases rowShiftedLeadingTerm?_some_data htermJ with
    ⟨hdegJ, _, _, _, _, _⟩
  have hposJI : termJ.position = termI.position := by omega
  have hposIJ : termI.position = termJ.position := by omega
  have hsizeIJ : (M.getD i #[]).size = (M.getD j #[]).size := by
    rw [matrix_getD_size_of_wellFormed hM hi,
      matrix_getD_size_of_wellFormed hM hj]
  unfold muldersStorjohannStep
  change shiftedMatrixMeasure
      (match rowShiftedDegree? (M.getD i #[]) shift,
          rowShiftedDegree? (M.getD j #[]) shift with
      | some degI, some degJ =>
          if degI ≤ degJ then
            replaceRow M j (cancelShiftedLeadingTerm (M.getD j #[]) (M.getD i #[]) shift)
          else
            replaceRow M i (cancelShiftedLeadingTerm (M.getD i #[]) (M.getD j #[]) shift)
      | _, _ => M) shift <
    shiftedMatrixMeasure M shift
  rw [hdegI, hdegJ]
  change shiftedMatrixMeasure
      (if termI.shiftedDegree ≤ termJ.shiftedDegree then
        replaceRow M j (cancelShiftedLeadingTerm (M.getD j #[]) (M.getD i #[]) shift)
      else
        replaceRow M i (cancelShiftedLeadingTerm (M.getD i #[]) (M.getD j #[]) shift))
      shift <
    shiftedMatrixMeasure M shift
  by_cases hleIJ : termI.shiftedDegree ≤ termJ.shiftedDegree
  · rw [if_pos hleIJ]
    apply shiftedMatrixMeasure_replaceRow_lt hj
    exact cancelShiftedLeadingTerm_shiftedRowMeasure_lt htermJ htermI hposJI hleIJ
      hsizeIJ
  · have hleJI : termJ.shiftedDegree ≤ termI.shiftedDegree := by omega
    rw [if_neg hleIJ]
    apply shiftedMatrixMeasure_replaceRow_lt hi
    exact cancelShiftedLeadingTerm_shiftedRowMeasure_lt htermI htermJ hposIJ hleJI
      hsizeIJ.symm

def matrixShiftedDegreeStep?
    (M : PolynomialMatrix F) (shift : Array Nat)
    (acc : Option Nat) (i : Nat) : Option Nat :=
  match rowShiftedDegree? (M.getD i #[]) shift with
  | none => acc
  | some d => maxOption acc d

def matrixShiftedDegreeSpec? (M : PolynomialMatrix F) (shift : Array Nat) :
    Option Nat :=
  (List.range M.size).foldl
    (matrixShiftedDegreeStep? M shift)
    none

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegreeStep?_eq
    (M : PolynomialMatrix F) (shift : Array Nat) :
    matrixShiftedDegreeStep? M shift =
    (fun acc i ↦
      match rowShiftedDegree? (M.getD i #[]) shift with
      | none => acc
      | some d => maxOption acc d) := by
  rfl

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegree?_eq_spec
    (M : PolynomialMatrix F) (shift : Array Nat) :
    matrixShiftedDegree? M shift = matrixShiftedDegreeSpec? M shift := by
  unfold matrixShiftedDegree? matrixShiftedDegreeSpec?
  rw [matrixShiftedDegreeStep?_eq M shift]
  rfl

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegreeSpecFold_acc_le
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {acc : Option Nat} {a D : Nat}
    (hacc : acc = some a)
    (hfold : xs.foldl (matrixShiftedDegreeStep? M shift) acc = some D) :
    a ≤ D := by
  induction xs generalizing acc a with
  | nil =>
      rw [List.foldl_nil] at hfold
      rw [hacc] at hfold
      exact le_of_eq (Option.some.inj hfold)
  | cons i xs ih =>
      rw [List.foldl_cons] at hfold
      cases hdeg : rowShiftedDegree? (M.getD i #[]) shift with
      | none =>
          have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = none := by
            simpa [Array.getD_eq_getD_getElem?] using hdeg
          exact ih hacc (by simpa [matrixShiftedDegreeStep?, hdeg'] using hfold)
      | some rowDeg =>
          have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = some rowDeg := by
            simpa [Array.getD_eq_getD_getElem?] using hdeg
          cases acc with
          | none =>
              simp at hacc
          | some accDeg =>
              have hnext :
                  matrixShiftedDegreeStep? M shift (some accDeg) i =
                    some (max accDeg rowDeg) := by
                simp [matrixShiftedDegreeStep?, hdeg', maxOption]
              have hmax_le : max accDeg rowDeg ≤ D :=
                ih rfl (by simpa [hnext] using hfold)
              have ha_eq : accDeg = a := Option.some.inj hacc
              omega

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegreeSpecFold_row_le
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {acc : Option Nat} {D i rowDeg : Nat}
    (hfold : xs.foldl (matrixShiftedDegreeStep? M shift) acc = some D)
    (hi : i ∈ xs)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    rowDeg ≤ D := by
  induction xs generalizing acc with
  | nil =>
      cases hi
  | cons x xs ih =>
      rw [List.foldl_cons] at hfold
      rw [List.mem_cons] at hi
      rcases hi with rfl | hi
      · cases hacc : acc with
        | none =>
            have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = some rowDeg := by
              simpa [Array.getD_eq_getD_getElem?] using hdeg
            have hnext :
                matrixShiftedDegreeStep? M shift none i = some rowDeg := by
              simp [matrixShiftedDegreeStep?, hdeg', maxOption]
            exact matrixShiftedDegreeSpecFold_acc_le xs rfl
              (by simpa [hacc, hnext] using hfold)
        | some accDeg =>
            have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = some rowDeg := by
              simpa [Array.getD_eq_getD_getElem?] using hdeg
            have hnext :
                matrixShiftedDegreeStep? M shift (some accDeg) i =
                  some (max accDeg rowDeg) := by
              simp [matrixShiftedDegreeStep?, hdeg', maxOption]
            have hmax_le :
                max accDeg rowDeg ≤ D :=
              matrixShiftedDegreeSpecFold_acc_le xs rfl
                (by simpa [hacc, hnext] using hfold)
            omega
      · exact ih hfold hi

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegreeSpec?_row_le
    {M : PolynomialMatrix F} {shift : Array Nat} {D i rowDeg : Nat}
    (hmat : matrixShiftedDegreeSpec? M shift = some D)
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    rowDeg ≤ D := by
  unfold matrixShiftedDegreeSpec? at hmat
  exact matrixShiftedDegreeSpecFold_row_le (List.range M.size) hmat
    (List.mem_range.mpr hi) hdeg

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegree?_row_le
    {M : PolynomialMatrix F} {shift : Array Nat} {D i rowDeg : Nat}
    (hmat : matrixShiftedDegree? M shift = some D)
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    rowDeg ≤ D := by
  rw [matrixShiftedDegree?_eq_spec] at hmat
  exact matrixShiftedDegreeSpec?_row_le hmat hi hdeg

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegreeSpecFold_some_of_acc_some
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {acc : Option Nat} {a : Nat}
    (hacc : acc = some a) :
    ∃ D, xs.foldl (matrixShiftedDegreeStep? M shift) acc = some D := by
  induction xs generalizing acc a with
  | nil =>
      exact ⟨a, by simp [hacc]⟩
  | cons i xs ih =>
      rw [List.foldl_cons]
      cases hdeg : rowShiftedDegree? (M.getD i #[]) shift with
      | none =>
          have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = none := by
            simpa [Array.getD_eq_getD_getElem?] using hdeg
          rcases ih hacc with ⟨D, hD⟩
          exact ⟨D, by simpa [matrixShiftedDegreeStep?, hdeg'] using hD⟩
      | some rowDeg =>
          have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = some rowDeg := by
            simpa [Array.getD_eq_getD_getElem?] using hdeg
          cases acc with
          | none =>
              simp at hacc
          | some accDeg =>
              have hnext :
                  matrixShiftedDegreeStep? M shift (some accDeg) i =
                    some (max accDeg rowDeg) := by
                simp [matrixShiftedDegreeStep?, hdeg', maxOption]
              exact ih hnext

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegreeSpecFold_exists_some_of_row
    {M : PolynomialMatrix F} {shift : Array Nat}
    (xs : List Nat) {i rowDeg : Nat}
    (hi : i ∈ xs)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    ∃ D, xs.foldl (matrixShiftedDegreeStep? M shift) none = some D := by
  induction xs with
  | nil =>
      cases hi
  | cons x xs ih =>
      rw [List.mem_cons] at hi
      rw [List.foldl_cons]
      rcases hi with rfl | hi
      · have hdeg' : rowShiftedDegree? (M[i]?.getD #[]) shift = some rowDeg := by
          simpa [Array.getD_eq_getD_getElem?] using hdeg
        have hnext : matrixShiftedDegreeStep? M shift none i = some rowDeg := by
          simp [matrixShiftedDegreeStep?, hdeg', maxOption]
        exact matrixShiftedDegreeSpecFold_some_of_acc_some xs hnext
      · cases hdegX : rowShiftedDegree? (M.getD x #[]) shift with
        | none =>
            have hdegX' : rowShiftedDegree? (M[x]?.getD #[]) shift = none := by
              simpa [Array.getD_eq_getD_getElem?] using hdegX
            simpa [matrixShiftedDegreeStep?, hdegX'] using ih hi
        | some rowDegX =>
            have hdegX' : rowShiftedDegree? (M[x]?.getD #[]) shift = some rowDegX := by
              simpa [Array.getD_eq_getD_getElem?] using hdegX
            have hnext : matrixShiftedDegreeStep? M shift none x = some rowDegX := by
              simp [matrixShiftedDegreeStep?, hdegX', maxOption]
            exact matrixShiftedDegreeSpecFold_some_of_acc_some xs hnext

omit [LawfulBEq F] [DecidableEq F] in
theorem matrixShiftedDegree?_row_le_getD
    {M : PolynomialMatrix F} {shift : Array Nat} {i rowDeg : Nat}
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    rowDeg ≤ (matrixShiftedDegree? M shift).getD 0 := by
  cases hmat : matrixShiftedDegree? M shift with
  | some D =>
      simpa [hmat] using matrixShiftedDegree?_row_le hmat hi hdeg
  | none =>
      rw [matrixShiftedDegree?_eq_spec] at hmat
      unfold matrixShiftedDegreeSpec? at hmat
      rcases matrixShiftedDegreeSpecFold_exists_some_of_row
          (List.range M.size) (List.mem_range.mpr hi) hdeg with
        ⟨D, hD⟩
      rw [hD] at hmat
      contradiction

omit [LawfulBEq F] [DecidableEq F] in
theorem shiftedRowMeasure_le_of_degree_bound
    {row : PolynomialRow F} {shift : Array Nat} {d : Nat}
    (hbound : ∀ rowDeg, rowShiftedDegree? row shift = some rowDeg → rowDeg ≤ d) :
    shiftedRowMeasure row shift ≤ (d + 1) * (row.size + 1) := by
  unfold shiftedRowMeasure
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp
  | some rowDeg =>
      cases hpos : rowShiftedLeadingPosition? row shift with
      | none =>
          simp
      | some pos =>
          have hrowDeg_le : rowDeg ≤ d := hbound rowDeg hdeg
          have hpos_lt : pos < row.size := rowShiftedLeadingPosition?_lt hpos
          simp
          nlinarith

omit [LawfulBEq F] [DecidableEq F] in
theorem shiftedMatrixMeasure_range_le_of_degree_bound
    {M : PolynomialMatrix F} {shift : Array Nat} {d : Nat}
    (hM : WellFormed M)
    (hbound : ∀ i rowDeg, i < M.size →
      rowShiftedDegree? (M.getD i #[]) shift = some rowDeg → rowDeg ≤ d) :
    ∀ n, n ≤ M.size →
      (List.range n).foldl
        (fun acc i ↦ acc + shiftedRowMeasure (M.getD i #[]) shift)
        0 ≤ n * ((d + 1) * (MatrixWidth M + 1)) := by
  intro n hn
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnM : n < M.size := by omega
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have hrow :
          shiftedRowMeasure (M.getD n #[]) shift ≤
            (d + 1) * ((M.getD n #[]).size + 1) := by
        apply shiftedRowMeasure_le_of_degree_bound
        intro rowDeg hdeg
        exact hbound n rowDeg hnM hdeg
      have hrow' :
          shiftedRowMeasure (M.getD n #[]) shift ≤
            (d + 1) * (MatrixWidth M + 1) := by
        simpa [Array.getD_eq_getD_getElem?,
          matrix_getElem?_getD_size_of_wellFormed hM hnM] using hrow
      have hacc := ih (by omega)
      nlinarith

omit [LawfulBEq F] [DecidableEq F] in
theorem shiftedMatrixMeasure_le_of_degree_bound
    {M : PolynomialMatrix F} {shift : Array Nat} {d : Nat}
    (hM : WellFormed M)
    (hbound : ∀ i rowDeg, i < M.size →
      rowShiftedDegree? (M.getD i #[]) shift = some rowDeg → rowDeg ≤ d) :
    shiftedMatrixMeasure M shift ≤
      M.size * ((d + 1) * (MatrixWidth M + 1)) := by
  unfold shiftedMatrixMeasure
  exact shiftedMatrixMeasure_range_le_of_degree_bound hM hbound M.size (Nat.le_refl M.size)

omit [LawfulBEq F] [DecidableEq F] in
theorem shiftedMatrixMeasure_lt_muldersStorjohannFuel
    {M : PolynomialMatrix F} {shift : Array Nat}
    (hM : WellFormed M) :
    shiftedMatrixMeasure M shift < muldersStorjohannFuel M shift := by
  let d := (matrixShiftedDegree? M shift).getD 0
  have hbound :
      shiftedMatrixMeasure M shift ≤
        M.size * ((d + 1) * (MatrixWidth M + 1)) := by
    apply shiftedMatrixMeasure_le_of_degree_bound hM
    intro i rowDeg hi hdeg
    exact matrixShiftedDegree?_row_le_getD hi hdeg
  unfold muldersStorjohannFuel
  change shiftedMatrixMeasure M shift <
    (M.size + 1) * (MatrixWidth M + 1) * (d + 1)
  have hwidthPos : 0 < MatrixWidth M + 1 := by omega
  have hdPos : 0 < d + 1 := by omega
  nlinarith

end PolynomialMatrix

end CompPoly
