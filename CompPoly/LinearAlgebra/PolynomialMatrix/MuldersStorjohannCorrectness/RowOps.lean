/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import CompPoly.Univariate.ToPoly.Impl

/-!
# Mulders-Storjohann Correctness Row and Row-Span Helpers

Row operation and row-span lemmas used by the Mulders-Storjohann correctness proof.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [DecidableEq F] in
theorem rowScalePolynomial_size (c : CPolynomial F) (row : PolynomialRow F) :
    (rowScalePolynomial c row).size = row.size := by
  simp [rowScalePolynomial]

theorem rowScaleMonomial_size (c : F) (d : Nat) (row : PolynomialRow F) :
    (rowScaleMonomial c d row).size = row.size := by
  simp [rowScaleMonomial, rowScalePolynomial_size]

omit [DecidableEq F] in
theorem rowNeg_size (row : PolynomialRow F) :
    (rowNeg row).size = row.size := by
  simp [rowNeg]

omit [DecidableEq F] in
theorem rowAdd_size (a b : PolynomialRow F) :
    (rowAdd a b).size = max a.size b.size := by
  simp [rowAdd]

omit [DecidableEq F] in
theorem rowSub_size (a b : PolynomialRow F) :
    (rowSub a b).size = max a.size b.size := by
  simp [rowSub, rowAdd_size, rowNeg_size]

omit [DecidableEq F] in
theorem rowGet_rowAdd (a b : PolynomialRow F) (j : Nat) :
    rowGet (rowAdd a b) j = rowGet a j + rowGet b j := by
  by_cases hj : j < (rowAdd a b).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowAdd, rowGet] at hj ⊢
  · have hle : (rowAdd a b).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp [rowAdd] at hle
    have hja : a.size ≤ j := by omega
    have hjb : b.size ≤ j := by omega
    simp [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hja,
      Array.getElem?_eq_none hjb]

omit [DecidableEq F] in
theorem rowGet_rowScalePolynomial
    (c : CPolynomial F) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowScalePolynomial c row) j = c * rowGet row j := by
  by_cases hj : j < (rowScalePolynomial c row).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowScalePolynomial, rowGet] at hj ⊢
    simp [Array.getElem?_eq_getElem hj]
  · have hle : (rowScalePolynomial c row).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp [rowScalePolynomial] at hle
    simp [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]

omit [DecidableEq F] in
theorem rowGet_rowNeg (row : PolynomialRow F) (j : Nat) :
    rowGet (rowNeg row) j = -rowGet row j := by
  by_cases hj : j < (rowNeg row).size
  · rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp [rowNeg, rowGet] at hj ⊢
    simp [Array.getElem?_eq_getElem hj]
  · have hle : (rowNeg row).size ≤ j := Nat.le_of_not_gt hj
    rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp [rowNeg] at hle
    simp [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]

omit [DecidableEq F] in
theorem rowGet_rowSub (a b : PolynomialRow F) (j : Nat) :
    rowGet (rowSub a b) j = rowGet a j - rowGet b j := by
  simp [rowSub, rowGet_rowAdd, rowGet_rowNeg, sub_eq_add_neg]

theorem rowGet_rowScaleMonomial
    (c : F) (d : Nat) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowScaleMonomial c d row) j =
      CPolynomial.monomial d c * rowGet row j := by
  simp [rowScaleMonomial, rowGet_rowScalePolynomial]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem rowGet_zeroRow (width j : Nat) :
    rowGet (zeroRow (F := F) width) j = 0 := by
  unfold rowGet zeroRow
  by_cases hj : j < (Array.replicate width (0 : CPolynomial F)).size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    simp
  · have hle : (Array.replicate width (0 : CPolynomial F)).size ≤ j :=
      Nat.le_of_not_gt hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle]
    simp

omit [DecidableEq F] in
theorem rowScalePolynomial_zeroRow (c : CPolynomial F) (width : Nat) :
    rowScalePolynomial c (zeroRow (F := F) width) = zeroRow width := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, zeroRow]

omit [DecidableEq F] in
theorem rowScalePolynomial_eq_zeroRow_of_rowIsZero
    (c : CPolynomial F) {row : PolynomialRow F} (hrow : RowIsZero row) :
    rowScalePolynomial c row = zeroRow row.size := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    have hjRow : j < row.size := by
      simpa [rowScalePolynomial] using hj₁
    have hzero : row[j] = 0 := by
      exact hrow row[j] (by
        simpa only [Array.mem_def] using Array.getElem_mem_toList hjRow)
    simp [rowScalePolynomial, zeroRow, hzero]

omit [LawfulBEq F] [DecidableEq F] in
theorem zeroRow_rowIsZero (width : Nat) :
    RowIsZero (zeroRow (F := F) width) := by
  intro p hp
  rw [zeroRow] at hp
  simpa using (List.mem_replicate.mp (by simpa [Array.mem_def] using hp)).2

omit [DecidableEq F] in
theorem rowScalePolynomial_zero (row : PolynomialRow F) :
    rowScalePolynomial (0 : CPolynomial F) row = zeroRow row.size := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowScalePolynomial (0 : CPolynomial F) row) j =
          rowGet (zeroRow (F := F) row.size) j := by
      simp [rowGet_zeroRow]
      by_cases hj : j < row.size
      · simp [rowGet, rowScalePolynomial, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hj]
      · have hle : row.size ≤ j := Nat.le_of_not_gt hj
        simp [rowGet, rowScalePolynomial, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none hle]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowAdd_zeroRow_zeroRow (width : Nat) :
    rowAdd (zeroRow (F := F) width) (zeroRow width) = zeroRow width := by
  apply Array.ext
  · simp [rowAdd, zeroRow]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (zeroRow (F := F) width) (zeroRow width)) j =
          rowGet (zeroRow (F := F) width) j := by
      simp [rowGet_rowAdd, rowGet_zeroRow]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowAdd_zeroRow_right
    {width : Nat} (row : PolynomialRow F) (hsize : row.size = width) :
    rowAdd row (zeroRow (F := F) width) = row := by
  apply Array.ext
  · simp [rowAdd, zeroRow, hsize]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd row (zeroRow (F := F) width)) j = rowGet row j := by
      simp [rowGet_rowAdd, rowGet_zeroRow]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowScalePolynomial_rowAdd
    (c : CPolynomial F) (a b : PolynomialRow F) :
    rowScalePolynomial c (rowAdd a b) =
      rowAdd (rowScalePolynomial c a) (rowScalePolynomial c b) := by
  apply Array.ext
  · simp [rowScalePolynomial, rowAdd]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, rowAdd, rowGet]
    cases a[j]? <;> cases b[j]? <;> simp [mul_add]

omit [DecidableEq F] in
theorem rowAdd_assoc (a b c : PolynomialRow F) :
    rowAdd (rowAdd a b) c = rowAdd a (rowAdd b c) := by
  apply Array.ext
  · simp [rowAdd, max_assoc]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowAdd a b) c) j =
          rowGet (rowAdd a (rowAdd b c)) j := by
      simp [rowGet_rowAdd, add_assoc]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowAdd_rowNeg_left (row : PolynomialRow F) :
    rowAdd (rowNeg row) row = zeroRow row.size := by
  apply Array.ext
  · simp [rowAdd, rowNeg, zeroRow]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowNeg row) row) j =
          rowGet (zeroRow (F := F) row.size) j := by
      simp [rowGet_rowAdd, rowGet_rowNeg, rowGet_zeroRow]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowSub_add_cancel
    {a b : PolynomialRow F} (hsize : b.size = a.size) :
    rowAdd (rowSub a b) b = a := by
  unfold rowSub
  rw [rowAdd_assoc, rowAdd_rowNeg_left]
  exact rowAdd_zeroRow_right a hsize.symm

omit [DecidableEq F] in
theorem rowAdd_medial (a b c d : PolynomialRow F) :
    rowAdd (rowAdd a b) (rowAdd c d) =
      rowAdd (rowAdd a c) (rowAdd b d) := by
  apply Array.ext
  · simp [rowAdd]
    omega
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowAdd a b) (rowAdd c d)) j =
          rowGet (rowAdd (rowAdd a c) (rowAdd b d)) j := by
      simp [rowGet_rowAdd]
      abel
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowScalePolynomial_add
    (c d : CPolynomial F) (row : PolynomialRow F) :
    rowAdd (rowScalePolynomial c row) (rowScalePolynomial d row) =
      rowScalePolynomial (c + d) row := by
  apply Array.ext
  · simp [rowScalePolynomial, rowAdd]
  · intro j hj₁ hj₂
    have hget :
        rowGet (rowAdd (rowScalePolynomial c row) (rowScalePolynomial d row)) j =
          rowGet (rowScalePolynomial (c + d) row) j := by
      simp [rowGet_rowAdd, rowGet_rowScalePolynomial, add_mul]
    simpa [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj₁,
      Array.getElem?_eq_getElem hj₂] using hget

omit [DecidableEq F] in
theorem rowScalePolynomial_assoc
    (c d : CPolynomial F) (row : PolynomialRow F) :
    rowScalePolynomial c (rowScalePolynomial d row) =
      rowScalePolynomial (c * d) row := by
  apply Array.ext
  · simp [rowScalePolynomial]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, mul_assoc]

omit [DecidableEq F] in
theorem getD_map_mul
    (coeffs : Array (CPolynomial F)) (c : CPolynomial F) (i : Nat) :
    (coeffs.map (fun q ↦ c * q)).getD i 0 = c * coeffs.getD i 0 := by
  by_cases hi : i < coeffs.size
  · simp [Array.getD_eq_getD_getElem?, hi]
  · have hle : coeffs.size ≤ i := Nat.le_of_not_gt hi
    have hleMap : (coeffs.map (fun q ↦ c * q)).size ≤ i := by
      simpa using hle
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hle,
      Array.getElem?_eq_none hleMap]

omit [DecidableEq F] in
theorem getD_ofFn_add
    (n : Nat) (coeffsA coeffsB : Array (CPolynomial F)) {i : Nat} (hi : i < n) :
    (Array.ofFn
        (fun k : Fin n ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)).getD i 0 =
      coeffsA.getD i 0 + coeffsB.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simp
  · simp [hi]

omit [DecidableEq F] in
theorem rowAdd_rowLinearCombination_range
    {M : PolynomialMatrix F} (coeffsA coeffsB : Array (CPolynomial F)) :
    ∀ n, n ≤ M.size →
      rowAdd
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffsA.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M)))
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffsB.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) =
      ((List.range n).foldl
        (fun acc i ↦
          rowAdd acc
            (rowScalePolynomial
              ((Array.ofFn
                (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)).getD i 0)
              (M.getD i #[])))
        (zeroRow (MatrixWidth M))) := by
  intro n hn
  induction n with
  | zero =>
      simp [rowAdd_zeroRow_zeroRow]
  | succ n ih =>
      have hnM : n < M.size := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowAdd_medial, ih (by omega),
        getD_ofFn_add M.size coeffsA coeffsB hnM, rowScalePolynomial_add]

omit [DecidableEq F] in
theorem rowAdd_rowLinearCombination
    {M : PolynomialMatrix F} (coeffsA coeffsB : Array (CPolynomial F)) :
    rowAdd (rowLinearCombination coeffsA M) (rowLinearCombination coeffsB M) =
      rowLinearCombination
        (Array.ofFn
          (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)) M := by
  simpa [rowLinearCombination] using
    rowAdd_rowLinearCombination_range (M := M) coeffsA coeffsB M.size
      (Nat.le_refl M.size)

omit [DecidableEq F] in
theorem rowAdd_mem_rowSpan
    {M : PolynomialMatrix F} {a b : PolynomialRow F}
    (ha : a ∈ RowSpan M) (hb : b ∈ RowSpan M) :
    rowAdd a b ∈ RowSpan M := by
  rcases ha with ⟨coeffsA, hsizeA, rfl⟩
  rcases hb with ⟨coeffsB, hsizeB, rfl⟩
  refine ⟨Array.ofFn
    (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0), ?_, ?_⟩
  · simp
  · rw [rowAdd_rowLinearCombination]

omit [DecidableEq F] in
theorem C_neg_one_mul (p : CPolynomial F) :
    CPolynomial.C (-1 : F) * p = -p := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly]
  rw [CPolynomial.toPoly_neg]
  have hpoly := congrArg (fun P : Polynomial F ↦ P.coeff i)
    (CPolynomial.toPoly_mul (CPolynomial.C (-1 : F)) p)
  rw [CPolynomial.C_toPoly] at hpoly
  simpa using hpoly

omit [DecidableEq F] in
theorem rowNeg_eq_rowScalePolynomial (row : PolynomialRow F) :
    rowNeg row = rowScalePolynomial (CPolynomial.C (-1 : F)) row := by
  apply Array.ext
  · simp [rowNeg, rowScalePolynomial]
  · intro j hj₁ hj₂
    simp [rowNeg, rowScalePolynomial, C_neg_one_mul]

omit [DecidableEq F] in
theorem rowScalePolynomial_rowLinearCombination_range
    {M : PolynomialMatrix F} (c : CPolynomial F) (coeffs : Array (CPolynomial F)) :
    ∀ n,
      rowScalePolynomial c
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) =
      ((List.range n).foldl
        (fun acc i ↦
          rowAdd acc
            (rowScalePolynomial ((coeffs.map fun q ↦ c * q).getD i 0)
              (M.getD i #[])))
        (zeroRow (MatrixWidth M))) := by
  intro n
  induction n with
  | zero =>
      simp [rowScalePolynomial_zeroRow]
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowScalePolynomial_rowAdd, ih, getD_map_mul,
        rowScalePolynomial_assoc]

omit [DecidableEq F] in
theorem rowScalePolynomial_rowLinearCombination
    {M : PolynomialMatrix F} (c : CPolynomial F) (coeffs : Array (CPolynomial F)) :
    rowScalePolynomial c (rowLinearCombination coeffs M) =
      rowLinearCombination (coeffs.map fun q ↦ c * q) M := by
  simpa [rowLinearCombination] using
    rowScalePolynomial_rowLinearCombination_range (M := M) c coeffs M.size

omit [DecidableEq F] in
theorem rowScalePolynomial_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
  (c : CPolynomial F) (hrow : row ∈ RowSpan M) :
    rowScalePolynomial c row ∈ RowSpan M := by
  rcases hrow with ⟨coeffs, hsize, rfl⟩
  refine ⟨coeffs.map fun q ↦ c * q, by simp [hsize], ?_⟩
  rw [rowScalePolynomial_rowLinearCombination]

theorem rowScaleMonomial_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
    (c : F) (d : Nat) (hrow : row ∈ RowSpan M) :
    rowScaleMonomial c d row ∈ RowSpan M := by
  unfold rowScaleMonomial
  exact rowScalePolynomial_mem_rowSpan (CPolynomial.monomial d c) hrow

omit [DecidableEq F] in
theorem rowNeg_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
    (hrow : row ∈ RowSpan M) :
    rowNeg row ∈ RowSpan M := by
  rw [rowNeg_eq_rowScalePolynomial]
  exact rowScalePolynomial_mem_rowSpan (CPolynomial.C (-1 : F)) hrow

omit [DecidableEq F] in
theorem rowSub_mem_rowSpan
    {M : PolynomialMatrix F} {a b : PolynomialRow F}
    (ha : a ∈ RowSpan M) (hb : b ∈ RowSpan M) :
    rowSub a b ∈ RowSpan M := by
  unfold rowSub
  exact rowAdd_mem_rowSpan ha (rowNeg_mem_rowSpan hb)

theorem cancelShiftedLeadingTerm_mem_rowSpan
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F} {shift : Array Nat}
    (htarget : target ∈ RowSpan M) (hreducer : reducer ∈ RowSpan M) :
    cancelShiftedLeadingTerm target reducer shift ∈ RowSpan M := by
  unfold cancelShiftedLeadingTerm
  split <;> try assumption
  split <;> try assumption
  split <;> try assumption
  apply rowSub_mem_rowSpan htarget
  exact rowScaleMonomial_mem_rowSpan _ _ hreducer

theorem cancelShiftedLeadingTerm_target_mem_rowSpan
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F} {shift : Array Nat}
    (hcancel : cancelShiftedLeadingTerm target reducer shift ∈ RowSpan M)
    (hreducer : reducer ∈ RowSpan M)
    (hsize : reducer.size = target.size) :
    target ∈ RowSpan M := by
  unfold cancelShiftedLeadingTerm at hcancel
  split at hcancel
  · split at hcancel
    · split at hcancel
      · exact hcancel
      · rename_i _ _ t r _ _ _ _
        let scaled := rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer
        have hscaled : scaled ∈ RowSpan M := by
          exact rowScaleMonomial_mem_rowSpan (t.coeff / r.coeff) (t.degree - r.degree) hreducer
        have hrecovered :
            rowAdd (rowSub target scaled) scaled ∈ RowSpan M :=
          rowAdd_mem_rowSpan hcancel hscaled
        have hscaled_size : scaled.size = target.size := by
          simp [scaled, rowScaleMonomial_size, hsize]
        simpa using
          (show rowAdd (rowSub target scaled) scaled = target from
            rowSub_add_cancel hscaled_size)
            ▸ hrecovered
    · exact hcancel
  · exact hcancel

theorem cancelShiftedLeadingTerm_size
    {target reducer : PolynomialRow F} {shift : Array Nat}
    (hsize : reducer.size = target.size) :
    (cancelShiftedLeadingTerm target reducer shift).size = target.size := by
  unfold cancelShiftedLeadingTerm
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  rw [rowSub_size, rowScaleMonomial_size, hsize, max_self]

end PolynomialMatrix

end CompPoly
