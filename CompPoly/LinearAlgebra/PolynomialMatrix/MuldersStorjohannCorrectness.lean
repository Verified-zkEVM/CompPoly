/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.MuldersStorjohann
import CompPoly.Univariate.ToPoly.Impl

/-!
# Correctness Contract for Mulders-Storjohann Reduction
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

omit [DecidableEq F] in
private theorem rowScalePolynomial_size (c : CPolynomial F) (row : PolynomialRow F) :
    (rowScalePolynomial c row).size = row.size := by
  simp [rowScalePolynomial]

private theorem rowScaleMonomial_size (c : F) (d : Nat) (row : PolynomialRow F) :
    (rowScaleMonomial c d row).size = row.size := by
  simp [rowScaleMonomial, rowScalePolynomial_size]

omit [DecidableEq F] in
private theorem rowNeg_size (row : PolynomialRow F) :
    (rowNeg row).size = row.size := by
  simp [rowNeg]

omit [DecidableEq F] in
private theorem rowAdd_size (a b : PolynomialRow F) :
    (rowAdd a b).size = max a.size b.size := by
  simp [rowAdd]

omit [DecidableEq F] in
private theorem rowSub_size (a b : PolynomialRow F) :
    (rowSub a b).size = max a.size b.size := by
  simp [rowSub, rowAdd_size, rowNeg_size]

omit [DecidableEq F] in
private theorem rowGet_rowAdd (a b : PolynomialRow F) (j : Nat) :
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
private theorem rowGet_rowScalePolynomial
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
private theorem rowGet_rowNeg (row : PolynomialRow F) (j : Nat) :
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
private theorem rowGet_rowSub (a b : PolynomialRow F) (j : Nat) :
    rowGet (rowSub a b) j = rowGet a j - rowGet b j := by
  simp [rowSub, rowGet_rowAdd, rowGet_rowNeg, sub_eq_add_neg]

private theorem rowGet_rowScaleMonomial
    (c : F) (d : Nat) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowScaleMonomial c d row) j =
      CPolynomial.monomial d c * rowGet row j := by
  simp [rowScaleMonomial, rowGet_rowScalePolynomial]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem rowGet_zeroRow (width j : Nat) :
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
private theorem rowScalePolynomial_zeroRow (c : CPolynomial F) (width : Nat) :
    rowScalePolynomial c (zeroRow (F := F) width) = zeroRow width := by
  apply Array.ext
  · simp [rowScalePolynomial, zeroRow]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, zeroRow]

omit [DecidableEq F] in
private theorem rowScalePolynomial_eq_zeroRow_of_rowIsZero
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
private theorem zeroRow_rowIsZero (width : Nat) :
    RowIsZero (zeroRow (F := F) width) := by
  intro p hp
  rw [zeroRow] at hp
  simpa using (List.mem_replicate.mp (by simpa [Array.mem_def] using hp)).2

omit [DecidableEq F] in
private theorem rowScalePolynomial_zero (row : PolynomialRow F) :
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
private theorem rowAdd_zeroRow_zeroRow (width : Nat) :
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
private theorem rowAdd_zeroRow_right
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
private theorem rowScalePolynomial_rowAdd
    (c : CPolynomial F) (a b : PolynomialRow F) :
    rowScalePolynomial c (rowAdd a b) =
      rowAdd (rowScalePolynomial c a) (rowScalePolynomial c b) := by
  apply Array.ext
  · simp [rowScalePolynomial, rowAdd]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, rowAdd, rowGet]
    cases a[j]? <;> cases b[j]? <;> simp [mul_add]

omit [DecidableEq F] in
private theorem rowAdd_assoc (a b c : PolynomialRow F) :
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
private theorem rowAdd_rowNeg_left (row : PolynomialRow F) :
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
private theorem rowSub_add_cancel
    {a b : PolynomialRow F} (hsize : b.size = a.size) :
    rowAdd (rowSub a b) b = a := by
  unfold rowSub
  rw [rowAdd_assoc, rowAdd_rowNeg_left]
  exact rowAdd_zeroRow_right a hsize.symm

omit [DecidableEq F] in
private theorem rowAdd_medial (a b c d : PolynomialRow F) :
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
private theorem rowScalePolynomial_add
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
private theorem rowScalePolynomial_assoc
    (c d : CPolynomial F) (row : PolynomialRow F) :
    rowScalePolynomial c (rowScalePolynomial d row) =
      rowScalePolynomial (c * d) row := by
  apply Array.ext
  · simp [rowScalePolynomial]
  · intro j hj₁ hj₂
    simp [rowScalePolynomial, mul_assoc]

omit [DecidableEq F] in
private theorem getD_map_mul
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
private theorem getD_ofFn_add
    (n : Nat) (coeffsA coeffsB : Array (CPolynomial F)) {i : Nat} (hi : i < n) :
    (Array.ofFn
        (fun k : Fin n ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)).getD i 0 =
      coeffsA.getD i 0 + coeffsB.getD i 0 := by
  rw [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simp
  · simp [hi]

omit [DecidableEq F] in
private theorem rowAdd_rowLinearCombination_range
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
private theorem rowAdd_rowLinearCombination
    {M : PolynomialMatrix F} (coeffsA coeffsB : Array (CPolynomial F)) :
    rowAdd (rowLinearCombination coeffsA M) (rowLinearCombination coeffsB M) =
      rowLinearCombination
        (Array.ofFn
          (fun k : Fin M.size ↦ coeffsA.getD k.1 0 + coeffsB.getD k.1 0)) M := by
  simpa [rowLinearCombination] using
    rowAdd_rowLinearCombination_range (M := M) coeffsA coeffsB M.size
      (Nat.le_refl M.size)

omit [DecidableEq F] in
private theorem rowAdd_mem_rowSpan
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
private theorem C_neg_one_mul (p : CPolynomial F) :
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
private theorem rowNeg_eq_rowScalePolynomial (row : PolynomialRow F) :
    rowNeg row = rowScalePolynomial (CPolynomial.C (-1 : F)) row := by
  apply Array.ext
  · simp [rowNeg, rowScalePolynomial]
  · intro j hj₁ hj₂
    simp [rowNeg, rowScalePolynomial, C_neg_one_mul]

omit [DecidableEq F] in
private theorem rowScalePolynomial_rowLinearCombination_range
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
private theorem rowScalePolynomial_rowLinearCombination
    {M : PolynomialMatrix F} (c : CPolynomial F) (coeffs : Array (CPolynomial F)) :
    rowScalePolynomial c (rowLinearCombination coeffs M) =
      rowLinearCombination (coeffs.map fun q ↦ c * q) M := by
  simpa [rowLinearCombination] using
    rowScalePolynomial_rowLinearCombination_range (M := M) c coeffs M.size

omit [DecidableEq F] in
private theorem rowScalePolynomial_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
  (c : CPolynomial F) (hrow : row ∈ RowSpan M) :
    rowScalePolynomial c row ∈ RowSpan M := by
  rcases hrow with ⟨coeffs, hsize, rfl⟩
  refine ⟨coeffs.map fun q ↦ c * q, by simp [hsize], ?_⟩
  rw [rowScalePolynomial_rowLinearCombination]

private theorem rowScaleMonomial_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
    (c : F) (d : Nat) (hrow : row ∈ RowSpan M) :
    rowScaleMonomial c d row ∈ RowSpan M := by
  unfold rowScaleMonomial
  exact rowScalePolynomial_mem_rowSpan (CPolynomial.monomial d c) hrow

omit [DecidableEq F] in
private theorem rowNeg_mem_rowSpan
    {M : PolynomialMatrix F} {row : PolynomialRow F}
    (hrow : row ∈ RowSpan M) :
    rowNeg row ∈ RowSpan M := by
  rw [rowNeg_eq_rowScalePolynomial]
  exact rowScalePolynomial_mem_rowSpan (CPolynomial.C (-1 : F)) hrow

omit [DecidableEq F] in
private theorem rowSub_mem_rowSpan
    {M : PolynomialMatrix F} {a b : PolynomialRow F}
    (ha : a ∈ RowSpan M) (hb : b ∈ RowSpan M) :
    rowSub a b ∈ RowSpan M := by
  unfold rowSub
  exact rowAdd_mem_rowSpan ha (rowNeg_mem_rowSpan hb)

private theorem cancelShiftedLeadingTerm_mem_rowSpan
    {M : PolynomialMatrix F} {target reducer : PolynomialRow F} {shift : Array Nat}
    (htarget : target ∈ RowSpan M) (hreducer : reducer ∈ RowSpan M) :
    cancelShiftedLeadingTerm target reducer shift ∈ RowSpan M := by
  unfold cancelShiftedLeadingTerm
  split <;> try assumption
  split <;> try assumption
  split <;> try assumption
  apply rowSub_mem_rowSpan htarget
  exact rowScaleMonomial_mem_rowSpan _ _ hreducer

private theorem cancelShiftedLeadingTerm_target_mem_rowSpan
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

private theorem cancelShiftedLeadingTerm_size
    {target reducer : PolynomialRow F} {shift : Array Nat}
    (hsize : reducer.size = target.size) :
    (cancelShiftedLeadingTerm target reducer shift).size = target.size := by
  unfold cancelShiftedLeadingTerm
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  rw [rowSub_size, rowScaleMonomial_size, hsize, max_self]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem replaceRow_size (M : PolynomialMatrix F) (idx : Nat) (row : PolynomialRow F) :
    (replaceRow M idx row).size = M.size := by
  simp [replaceRow, Array.size_setIfInBounds]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem replaceRow_matrixWidth
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hrow : row.size = MatrixWidth M) :
    MatrixWidth (replaceRow M idx row) = MatrixWidth M := by
  unfold MatrixWidth replaceRow
  by_cases hM0 : 0 < M.size
  · rw [Array.getElem?_setIfInBounds]
    by_cases hidx : idx = 0
    · subst idx
      simpa [hM0, MatrixWidth] using hrow
    · simp [hidx]
  · have hsize : M.size = 0 := Nat.eq_zero_of_not_pos hM0
    simp [hsize]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem replaceRow_shape
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hrow : row.size = MatrixWidth M) :
    MatrixShape (replaceRow M idx row) = MatrixShape M := by
  simp [MatrixShape, replaceRow_size, replaceRow_matrixWidth hrow]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem replaceRow_wellFormed
    {M : PolynomialMatrix F} {idx : Nat} {row : PolynomialRow F}
    (hM : WellFormed M) (hrow : row.size = MatrixWidth M) :
    WellFormed (replaceRow M idx row) := by
  intro stored hstored
  have hwidth : MatrixWidth (replaceRow M idx row) = MatrixWidth M :=
    replaceRow_matrixWidth hrow
  rw [hwidth]
  rcases List.getElem_of_mem hstored with ⟨k, hk, hget⟩
  have hkReplace : k < (replaceRow M idx row).size := by
    simpa [MatrixRows] using hk
  have hkM : k < M.size := by
    simpa [replaceRow_size] using hkReplace
  have hstored_eq : (replaceRow M idx row)[k] = stored := by
    simpa [MatrixRows, Array.getElem_toList] using hget
  rw [← hstored_eq]
  by_cases hidx : k = idx
  · subst idx
    simpa [replaceRow, Array.getElem_setIfInBounds, hkM] using hrow
  · have hmem : M[k] ∈ MatrixRows M := by
      simp [MatrixRows, Array.getElem_mem_toList hkM]
    have hstoredM : M[k].size = MatrixWidth M := hM M[k] hmem
    have hidx' : idx ≠ k := fun h ↦ hidx h.symm
    simpa [replaceRow, Array.getElem_setIfInBounds, hidx', hkM] using hstoredM

private theorem replaceRow_rows_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) {idx : Nat} {newRow row : PolynomialRow F}
    (hnew : newRow ∈ RowSpan M)
    (hrow : row ∈ MatrixRows (replaceRow M idx newRow)) :
    row ∈ RowSpan M := by
  rcases List.getElem_of_mem hrow with ⟨k, hk, hget⟩
  have hkReplace : k < (replaceRow M idx newRow).size := by
    simpa [MatrixRows] using hk
  have hkM : k < M.size := by
    simpa [replaceRow_size] using hkReplace
  have hstored_eq : (replaceRow M idx newRow)[k] = row := by
    simpa [MatrixRows, Array.getElem_toList] using hget
  rw [← hstored_eq]
  by_cases hidx : idx = k
  · subst idx
    simpa [replaceRow, Array.getElem_setIfInBounds, hkM] using hnew
  · have hstoredM : (replaceRow M idx newRow)[k] = M[k] := by
      simp [replaceRow, hidx, hkM]
    rw [hstoredM]
    exact matrix_row_mem_rowSpan hM
      (by simp [MatrixRows, Array.getElem_mem_toList hkM])

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem replaceRow_newRow_mem
    {M : PolynomialMatrix F} {idx : Nat} {newRow : PolynomialRow F}
    (hidx : idx < M.size) :
    newRow ∈ MatrixRows (replaceRow M idx newRow) := by
  have hidxReplace : idx < (replaceRow M idx newRow).size := by
    simpa [replaceRow_size] using hidx
  have hget : (replaceRow M idx newRow)[idx] = newRow := by
    simp [replaceRow]
  have hmem : (replaceRow M idx newRow)[idx] ∈ MatrixRows (replaceRow M idx newRow) := by
    exact Array.getElem_mem_toList hidxReplace
  simpa [hget] using hmem

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem replaceRow_oldRow_mem
    {M : PolynomialMatrix F} {idx k : Nat} {newRow : PolynomialRow F}
    (hk : k < M.size) (hne : idx ≠ k) :
    M[k] ∈ MatrixRows (replaceRow M idx newRow) := by
  have hkReplace : k < (replaceRow M idx newRow).size := by
    simpa [replaceRow_size] using hk
  have hget : (replaceRow M idx newRow)[k] = M[k] := by
    simp [replaceRow, hne, hk]
  rw [← hget]
  simp [MatrixRows, Array.getElem_mem_toList hkReplace]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem matrix_getD_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    (M.getD i #[]).size = MatrixWidth M := by
  have hget : M.getD i #[] = M[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget]
  exact hM M[i] (by simp [MatrixRows, Array.getElem_mem_toList hi])

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem matrix_getElem?_getD_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    (M[i]?.getD #[]).size = MatrixWidth M := by
  simpa [Array.getElem?_eq_getElem hi] using matrix_getD_size_of_wellFormed hM hi

private theorem matrix_getD_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) {i : Nat} (hi : i < M.size) :
    M.getD i #[] ∈ RowSpan M := by
  have hget : M.getD i #[] = M[i] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [hget]
  exact matrix_row_mem_rowSpan hM
    (by simp [MatrixRows, Array.getElem_mem_toList hi])

omit [DecidableEq F] in
private theorem zeroRow_mem_rowSpan
    {M : PolynomialMatrix F} (hM : WellFormed M) :
    zeroRow (F := F) (MatrixWidth M) ∈ RowSpan M := by
  let coeffs := Array.replicate M.size (0 : CPolynomial F)
  refine ⟨coeffs, by simp [coeffs], ?_⟩
  unfold rowLinearCombination
  have hfold :
      ∀ n, n ≤ M.size →
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) = zeroRow (F := F) (MatrixWidth M) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hnM : n < M.size := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (by omega)]
        have hcoeff : coeffs.getD n 0 = 0 := by
          simp [coeffs, hnM]
        rw [hcoeff, rowScalePolynomial_zero]
        rw [matrix_getD_size_of_wellFormed hM hnM]
        exact rowAdd_zeroRow_zeroRow (MatrixWidth M)
  exact (hfold M.size (Nat.le_refl M.size)).symm

omit [DecidableEq F] in
private theorem rowLinearCombination_mem_rowSpan_of_rows_mem
    {A B : PolynomialMatrix F} (hB : WellFormed B)
    (hwidth : MatrixWidth A = MatrixWidth B)
    (hrows : ∀ row, row ∈ MatrixRows A → row ∈ RowSpan B)
    (coeffs : Array (CPolynomial F)) :
    rowLinearCombination coeffs A ∈ RowSpan B := by
  unfold rowLinearCombination
  have hfold :
      ∀ n, n ≤ A.size →
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (A.getD i #[])))
          (zeroRow (MatrixWidth A))) ∈ RowSpan B := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [hwidth]
        exact zeroRow_mem_rowSpan hB
    | succ n ih =>
        intro hn
        have hnA : n < A.size := by omega
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        apply rowAdd_mem_rowSpan
        · exact ih (by omega)
        · apply rowScalePolynomial_mem_rowSpan
          have hget : A.getD n #[] = A[n] := by
            simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hnA]
          rw [hget]
          exact hrows A[n] (by simp [MatrixRows, Array.getElem_mem_toList hnA])
  exact hfold A.size (Nat.le_refl A.size)

omit [DecidableEq F] in
private theorem rowSpan_subset_of_rows_mem
    {A B : PolynomialMatrix F} (hB : WellFormed B)
    (hwidth : MatrixWidth A = MatrixWidth B)
    (hrows : ∀ row, row ∈ MatrixRows A → row ∈ RowSpan B) :
    RowSpan A ⊆ RowSpan B := by
  intro row hrow
  rcases hrow with ⟨coeffs, _hsize, rfl⟩
  exact rowLinearCombination_mem_rowSpan_of_rows_mem hB hwidth hrows coeffs

private theorem cancelShiftedLeadingTerm_size_of_wellFormed
    {M : PolynomialMatrix F} (hM : WellFormed M) {i j : Nat}
    (hi : i < M.size) (hj : j < M.size) (shift : Array Nat) :
    (cancelShiftedLeadingTerm (M.getD i #[]) (M.getD j #[]) shift).size =
      MatrixWidth M := by
  rw [cancelShiftedLeadingTerm_size
      (hsize := (matrix_getD_size_of_wellFormed hM hj).trans
        (matrix_getD_size_of_wellFormed hM hi).symm)]
  exact matrix_getD_size_of_wellFormed hM hi

omit [LawfulBEq F] [DecidableEq F] in
private theorem index_lt_of_rowShiftedDegree?_getElem?_eq_some
    {M : PolynomialMatrix F} {shift : Array Nat} {i d : Nat}
    (hdeg : rowShiftedDegree? (M[i]?.getD #[]) shift = some d) :
    i < M.size := by
  by_contra hnot
  have hle : M.size ≤ i := Nat.le_of_not_gt hnot
  have hnone : rowShiftedDegree? (M[i]?.getD #[]) shift = none := by
    rw [Array.getElem?_eq_none hle]
    simp [rowShiftedDegree?]
  rw [hnone] at hdeg
  contradiction

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private def ConflictBounds (M : PolynomialMatrix F) : Option (Nat × Nat) → Prop
  | none => True
  | some (i, j) => i < M.size ∧ j < M.size ∧ i < j

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRowFold_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) (xs : List Nat)
    (found : Option (Nat × Nat))
    (hxs : ∀ j, j ∈ xs → i < j ∧ j < M.size)
    (hfound : ConflictBounds M found) :
    ConflictBounds M
      (xs.foldl
        (fun found j ↦
          match found with
          | some _ => found
          | none =>
              match rowShiftedLeadingPosition? (M.getD i #[]) shift,
                  rowShiftedLeadingPosition? (M.getD j #[]) shift with
              | some pi, some pj =>
                  if pi == pj then some (i, j) else none
              | _, _ => none)
        found) := by
  induction xs generalizing found with
  | nil =>
      simpa using hfound
  | cons j xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        exact hxs k (by simp [hk])
      · cases found with
        | none =>
            cases rowShiftedLeadingPosition? (M.getD i #[]) shift <;>
              cases rowShiftedLeadingPosition? (M.getD j #[]) shift
            · simp [ConflictBounds]
            · simp [ConflictBounds]
            · simp [ConflictBounds]
            · rename_i pi pj
              by_cases hpos : pi == pj
              · have hjBounds := hxs j (by simp)
                have hiM : i < M.size := by omega
                simp [hpos, ConflictBounds, hjBounds, hiM]
              · simp [hpos, ConflictBounds]
        | some pair =>
            rcases pair with ⟨a, b⟩
            simpa [ConflictBounds] using hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRow?_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) {i : Nat} {found : Option (Nat × Nat)}
    (hi : i < M.size) (hfound : ConflictBounds M found) :
    ConflictBounds M (shiftedLeadingConflictInRow? M shift i found) := by
  unfold shiftedLeadingConflictInRow?
  apply shiftedLeadingConflictInRowFold_bounds
  · intro j hj
    have hj' := (List.mem_range'.1 hj)
    omega
  · exact hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFromFold_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat)
    (found : Option (Nat × Nat))
    (hxs : ∀ i, i ∈ xs → i < M.size)
    (hfound : ConflictBounds M found) :
    ConflictBounds M
      (xs.foldl
        (fun found i ↦ shiftedLeadingConflictInRow? M shift i found)
        found) := by
  induction xs generalizing found with
  | nil =>
      simpa using hfound
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro k hk
        exact hxs k (by simp [hk])
      · exact shiftedLeadingConflictInRow?_bounds M shift (hxs i (by simp)) hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFrom?_bounds
    (M : PolynomialMatrix F) (shift : Array Nat) {found : Option (Nat × Nat)}
    (hfound : ConflictBounds M found) :
    ConflictBounds M (shiftedLeadingConflictFrom? M shift found) := by
  unfold shiftedLeadingConflictFrom?
  apply shiftedLeadingConflictFromFold_bounds
  · intro i hi
    have hi' := (List.mem_range'.1 hi)
    omega
  · exact hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflict?_some_bounds
    {M : PolynomialMatrix F} {shift : Array Nat} {i j : Nat}
    (hconf : shiftedLeadingConflict? M shift = some (i, j)) :
    i < M.size ∧ j < M.size ∧ i < j := by
  have hbounds : ConflictBounds M (shiftedLeadingConflict? M shift) := by
    unfold shiftedLeadingConflict?
    exact shiftedLeadingConflictFrom?_bounds M shift trivial
  rw [hconf] at hbounds
  exact hbounds

private def ConflictValid (M : PolynomialMatrix F) (shift : Array Nat) :
    Option (Nat × Nat) → Prop
  | none => True
  | some (i, j) =>
      ∃ p,
        rowShiftedLeadingPosition? (M.getD i #[]) shift = some p ∧
        rowShiftedLeadingPosition? (M.getD j #[]) shift = some p

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRowStep?_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    {found : Option (Nat × Nat)} (j : Nat)
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift (shiftedLeadingConflictInRowStep? M shift i found j) := by
  unfold shiftedLeadingConflictInRowStep?
  cases found with
  | none =>
      cases hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift with
      | none =>
          simp [ConflictValid]
      | some pi =>
          cases hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift with
          | none =>
              simp [ConflictValid]
          | some pj =>
              by_cases hsame : pi == pj
              · have hpj : pj = pi := (LawfulBEq.eq_of_beq hsame).symm
                subst pj
                change ConflictValid M shift
                  (if (pi == pi) = true then some (i, j) else none)
                rw [hsame]
                refine ⟨pi, ?_, ?_⟩
                · simpa [Array.getD_eq_getD_getElem?] using hposI
                · simpa [Array.getD_eq_getD_getElem?] using hposJ
              · simp [hsame, ConflictValid]
  | some pair =>
      simpa [ConflictValid] using hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRowFold_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    (xs : List Nat) {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift
      (xs.foldl (shiftedLeadingConflictInRowStep? M shift i) found) := by
  induction xs generalizing found with
  | nil =>
      exact hfound
  | cons j xs ih =>
      simp only [List.foldl_cons]
      exact ih (shiftedLeadingConflictInRowStep?_valid M shift i j hfound)

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRow?_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift (shiftedLeadingConflictInRow? M shift i found) := by
  unfold shiftedLeadingConflictInRow?
  exact shiftedLeadingConflictInRowFold_valid M shift i _ hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFromFold_valid
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat)
    {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift
      (xs.foldl (shiftedLeadingConflictFromStep? M shift) found) := by
  induction xs generalizing found with
  | nil =>
      exact hfound
  | cons i xs ih =>
      simp only [List.foldl_cons]
      exact ih (shiftedLeadingConflictInRow?_valid M shift i hfound)

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFrom?_valid
    (M : PolynomialMatrix F) (shift : Array Nat) {found : Option (Nat × Nat)}
    (hfound : ConflictValid M shift found) :
    ConflictValid M shift (shiftedLeadingConflictFrom? M shift found) := by
  unfold shiftedLeadingConflictFrom?
  exact shiftedLeadingConflictFromFold_valid M shift _ hfound

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflict?_some_valid
    {M : PolynomialMatrix F} {shift : Array Nat} {i j : Nat}
    (hconf : shiftedLeadingConflict? M shift = some (i, j)) :
    ∃ p,
      rowShiftedLeadingPosition? (M.getD i #[]) shift = some p ∧
      rowShiftedLeadingPosition? (M.getD j #[]) shift = some p := by
  have hvalid : ConflictValid M shift (shiftedLeadingConflict? M shift) := by
    unfold shiftedLeadingConflict?
    exact shiftedLeadingConflictFrom?_valid M shift trivial
  rw [hconf] at hvalid
  exact hvalid

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRowFold_some
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat)
    (xs : List Nat) (pair : Nat × Nat) :
    xs.foldl (shiftedLeadingConflictInRowStep? M shift i) (some pair) = some pair := by
  induction xs with
  | nil =>
      rfl
  | cons j xs ih =>
      simp [shiftedLeadingConflictInRowStep?, ih]

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRow?_some
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) (pair : Nat × Nat) :
    shiftedLeadingConflictInRow? M shift i (some pair) = some pair := by
  unfold shiftedLeadingConflictInRow?
  exact shiftedLeadingConflictInRowFold_some M shift i _ pair

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFromFold_some
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat) (pair : Nat × Nat) :
    xs.foldl (shiftedLeadingConflictFromStep? M shift) (some pair) = some pair := by
  induction xs with
  | nil =>
      rfl
  | cons i xs ih =>
      simp [shiftedLeadingConflictFromStep?, shiftedLeadingConflictInRow?_some, ih]

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFrom?_some
    (M : PolynomialMatrix F) (shift : Array Nat) (pair : Nat × Nat) :
    shiftedLeadingConflictFrom? M shift (some pair) = some pair := by
  unfold shiftedLeadingConflictFrom?
  exact shiftedLeadingConflictFromFold_some M shift _ pair

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRowFold_none_no_conflict
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) (xs : List Nat)
    (hfold : xs.foldl (shiftedLeadingConflictInRowStep? M shift i) none = none)
    {j p : Nat} (hj : j ∈ xs)
    (hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift = some p)
    (hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift = some p) :
    False := by
  induction xs with
  | nil =>
      cases hj
  | cons x xs ih =>
      simp only [List.foldl_cons] at hfold
      rw [List.mem_cons] at hj
      cases hstep : shiftedLeadingConflictInRowStep? M shift i none x with
      | none =>
          have htail : xs.foldl (shiftedLeadingConflictInRowStep? M shift i) none = none := by
            simpa [hstep] using hfold
          rcases hj with rfl | hj
          · rw [Array.getD_eq_getD_getElem?] at hposI hposJ
            simp [shiftedLeadingConflictInRowStep?, hposI, hposJ] at hstep
          · exact ih htail hj
      | some pair =>
          have hsome := shiftedLeadingConflictInRowFold_some M shift i xs pair
          rw [hstep, hsome] at hfold
          contradiction

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictInRow?_none_no_conflict
    {M : PolynomialMatrix F} {shift : Array Nat} {i j p : Nat}
    (hfold : shiftedLeadingConflictInRow? M shift i none = none)
    (hij : i < j) (hj : j < M.size)
    (hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift = some p)
    (hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift = some p) :
    False := by
  unfold shiftedLeadingConflictInRow? at hfold
  apply shiftedLeadingConflictInRowFold_none_no_conflict (j := j) (p := p) M shift i
    (List.range' (i + 1) (M.size - (i + 1))) hfold
  · rw [List.mem_range']
    refine ⟨j - (i + 1), ?_, ?_⟩ <;> omega
  · exact hposI
  · exact hposJ

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflictFromFold_none_inner_none
    (M : PolynomialMatrix F) (shift : Array Nat) (xs : List Nat)
    (hfold : xs.foldl (shiftedLeadingConflictFromStep? M shift) none = none)
    {i : Nat} (hi : i ∈ xs) :
    shiftedLeadingConflictInRow? M shift i none = none := by
  induction xs with
  | nil =>
      cases hi
  | cons x xs ih =>
      simp only [List.foldl_cons] at hfold
      rw [List.mem_cons] at hi
      cases hstep : shiftedLeadingConflictFromStep? M shift none x with
      | none =>
          have htail : xs.foldl (shiftedLeadingConflictFromStep? M shift) none = none := by
            simpa [hstep] using hfold
          rcases hi with rfl | hi
          · simpa [shiftedLeadingConflictFromStep?] using hstep
          · exact ih htail hi
      | some pair =>
          have hsome := shiftedLeadingConflictFromFold_some M shift xs pair
          rw [hstep, hsome] at hfold
          contradiction

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflict?_none_no_conflict
    {M : PolynomialMatrix F} {shift : Array Nat} {i j p : Nat}
    (hconf : shiftedLeadingConflict? M shift = none)
    (hi : i < M.size) (hj : j < M.size) (hij : i < j)
    (hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift = some p)
    (hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift = some p) :
    False := by
  unfold shiftedLeadingConflict? shiftedLeadingConflictFrom? at hconf
  have hinner :
      shiftedLeadingConflictInRow? M shift i none = none := by
    apply shiftedLeadingConflictFromFold_none_inner_none M shift (List.range' 0 M.size) hconf
    rw [List.mem_range']
    exact ⟨i, hi, by omega⟩
  exact shiftedLeadingConflictInRow?_none_no_conflict hinner hij hj hposI hposJ

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedLeadingConflict?_none_weakPopov
    {M : PolynomialMatrix F} {shift : Array Nat}
    (hconf : shiftedLeadingConflict? M shift = none) :
    ShiftedWeakPopov M shift := by
  intro i j hi hj hne hposI_ne hposJ_ne hsame
  cases hposI : rowShiftedLeadingPosition? (M.getD i #[]) shift with
  | none =>
      exact False.elim (hposI_ne hposI)
  | some p =>
      cases hposJ : rowShiftedLeadingPosition? (M.getD j #[]) shift with
      | none =>
          exact False.elim (hposJ_ne hposJ)
      | some q =>
          have hpq : p = q := by
            have hpqOption : some p = some q := by
              rw [← hposI, ← hposJ]
              exact hsame
            exact Option.some.inj hpqOption
          subst q
          rcases Nat.lt_or_gt_of_ne hne with hij | hji
          · exact False.elim
              (shiftedLeadingConflict?_none_no_conflict hconf hi hj hij hposI hposJ)
          · exact False.elim
              (shiftedLeadingConflict?_none_no_conflict hconf hj hi hji hposJ hposI)

omit [LawfulBEq F] [DecidableEq F] in
private theorem rowShiftedLeadingPosition?_lt
    {row : PolynomialRow F} {shift : Array Nat} {pos : Nat}
    (hpos : rowShiftedLeadingPosition? row shift = some pos) :
    pos < row.size := by
  unfold rowShiftedLeadingPosition? at hpos
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp [hdeg] at hpos
  | some d =>
      simp [hdeg] at hpos
      have hmemReverse :
          pos ∈ (List.range row.size).reverse :=
        List.mem_of_find?_eq_some hpos
      have hmem : pos ∈ List.range row.size := by
        simpa using (List.mem_reverse.mp hmemReverse)
      exact List.mem_range.mp hmem

omit [LawfulBEq F] [DecidableEq F] in
private theorem rowShiftedLeadingPosition?_no_larger_tie
    {row : PolynomialRow F} {shift : Array Nat} {degree pos k : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hpos : rowShiftedLeadingPosition? row shift = some pos)
    (hk : k < row.size) (hposk : pos < k) :
    shiftedEntryDegree? row shift k ≠ some degree := by
  have hposBound : pos < row.size := rowShiftedLeadingPosition?_lt hpos
  unfold rowShiftedLeadingPosition? at hpos
  rw [hdeg] at hpos
  set pred : Nat → Bool :=
    fun j ↦
      match shiftedEntryDegree? row shift j with
      | some dj => dj == degree
      | none => false
  change (List.range row.size).reverse.find? pred = some pos at hpos
  rcases (List.find?_eq_some_iff_getElem.mp hpos) with
    ⟨_, idx, hidx, hget, hbefore⟩
  have hidxLen : idx < row.size := by
    simpa [List.length_reverse] using hidx
  have hindexLt :
      (List.range row.size).length - 1 - idx < (List.range row.size).length := by
    simp only [List.length_range]
    omega
  have hgetIndex :
      (List.range row.size)[(List.range row.size).length - 1 - idx]'hindexLt = pos := by
    simpa [List.getElem_reverse hidx] using hget
  have hidxEq : idx = row.size - 1 - pos := by
    rw [List.getElem_range hindexLt] at hgetIndex
    simp only [List.length_range] at hgetIndex
    omega
  intro hentry
  let kidx := row.size - 1 - k
  have hkidxLen : kidx < (List.range row.size).reverse.length := by
    simp [kidx, List.length_reverse]
    omega
  have hgetK : (List.range row.size).reverse[kidx] = k := by
    rw [List.getElem_reverse hkidxLen]
    have hindexLt :
        (List.range row.size).length - 1 - kidx < (List.range row.size).length := by
      simp only [List.length_range]
      omega
    rw [List.getElem_range hindexLt]
    simp [kidx]
    omega
  have hkidx_lt_idx : kidx < idx := by
    simp [kidx, hidxEq]
    omega
  have hnot := hbefore kidx hkidx_lt_idx
  simp [pred, hgetK, hentry] at hnot

omit [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem list_find?_some_of_exists
    {α : Type*} (xs : List α) (pred : α → Bool)
    (hexists : ∃ x ∈ xs, pred x = true) :
    ∃ x, xs.find? pred = some x := by
  induction xs with
  | nil =>
      rcases hexists with ⟨_, hx, _⟩
      simp at hx
  | cons x xs ih =>
      by_cases hx : pred x = true
      · exact ⟨x, by simp [List.find?, hx]⟩
      · have htail : ∃ y ∈ xs, pred y = true := by
          rcases hexists with ⟨y, hy, hpred⟩
          simp at hy
          rcases hy with rfl | hy
          · contradiction
          · exact ⟨y, hy, hpred⟩
        rcases ih htail with ⟨y, hyfind⟩
        exact ⟨y, by simp [List.find?, hx, hyfind]⟩

omit [LawfulBEq F] [DecidableEq F] in
private theorem rowShiftedLeadingPosition?_some_of_degree
    {row : PolynomialRow F} {shift : Array Nat} {degree : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree) :
    ∃ pos, rowShiftedLeadingPosition? row shift = some pos := by
  unfold rowShiftedLeadingPosition?
  rw [hdeg]
  rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hdeg with
    ⟨j, hj, hentry⟩
  let pred : Nat → Bool :=
    fun j ↦
      match shiftedEntryDegree? row shift j with
      | some dj => dj == degree
      | none => false
  change ∃ pos, (List.range row.size).reverse.find? pred = some pos
  have hexists : ∃ x ∈ (List.range row.size).reverse, pred x = true := by
    refine ⟨j, ?_, ?_⟩
    · simpa using (List.mem_reverse.mpr (List.mem_range.mpr hj))
    · simp [pred, hentry]
  exact list_find?_some_of_exists (List.range row.size).reverse pred hexists

omit [LawfulBEq F] [DecidableEq F] in
private theorem rowShiftedLeadingPosition?_le_of_entry_eq_degree
    {row : PolynomialRow F} {shift : Array Nat} {degree pos k : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hpos : rowShiftedLeadingPosition? row shift = some pos)
    (hk : k < row.size)
    (hentry : shiftedEntryDegree? row shift k = some degree) :
    k ≤ pos := by
  by_contra hnot
  have hposk : pos < k := by omega
  exact rowShiftedLeadingPosition?_no_larger_tie hdeg hpos hk hposk hentry

omit [DecidableEq F] in
private theorem shiftedEntryDegree?_eq_some_of_rowGet_ne_zero
    {row : PolynomialRow F} {shift : Array Nat} {j : Nat}
    (hne : rowGet row j ≠ 0) :
    shiftedEntryDegree? row shift j =
      some ((rowGet row j).natDegree + shift.getD j 0) := by
  have hbeq : (rowGet row j == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hne (LawfulBEq.eq_of_beq htrue)
  simp [shiftedEntryDegree?, hbeq, Array.getD_eq_getD_getElem?]

omit [DecidableEq F] in
private theorem shiftedEntryDegree?_eq_some_iff_data
    {row : PolynomialRow F} {shift : Array Nat} {j d : Nat} :
    shiftedEntryDegree? row shift j = some d ↔
      rowGet row j ≠ 0 ∧
        (rowGet row j).natDegree + shift.getD j 0 = d := by
  constructor
  · intro h
    unfold shiftedEntryDegree? at h
    by_cases hzero : rowGet row j = 0
    · have hbeq : (rowGet row j == 0) = true := by
        rwa [beq_iff_eq]
      simp [hbeq] at h
    · have hbeq : (rowGet row j == 0) = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        exact hzero (LawfulBEq.eq_of_beq htrue)
      simp [hbeq] at h
      exact ⟨hzero, by simpa [Array.getD_eq_getD_getElem?] using h⟩
  · rintro ⟨hne, rfl⟩
    exact shiftedEntryDegree?_eq_some_of_rowGet_ne_zero hne

omit [DecidableEq F] in
private theorem rowShiftedDegree?_entry_bound
    {row : PolynomialRow F} {shift : Array Nat} {degree j : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hj : j < row.size) (hne : rowGet row j ≠ 0) :
    (rowGet row j).natDegree + shift.getD j 0 ≤ degree := by
  exact shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hdeg hj
    (shiftedEntryDegree?_eq_some_of_rowGet_ne_zero hne)

omit [LawfulBEq F] [DecidableEq F] in
private theorem rowShiftedLeadingPosition?_entry_eq
    {row : PolynomialRow F} {shift : Array Nat} {degree pos : Nat}
    (hdeg : rowShiftedDegree? row shift = some degree)
    (hpos : rowShiftedLeadingPosition? row shift = some pos) :
    shiftedEntryDegree? row shift pos = some degree := by
  unfold rowShiftedLeadingPosition? at hpos
  rw [hdeg] at hpos
  have hpred := List.find?_some hpos
  cases hentry : shiftedEntryDegree? row shift pos with
  | none =>
      simp [hentry] at hpred
  | some entryDegree =>
      simp [hentry] at hpred
      simp [hpred]

omit [DecidableEq F] in
private theorem rowShiftedLeadingTerm?_some_of_position
    {row : PolynomialRow F} {shift : Array Nat} {pos : Nat}
    (hpos : rowShiftedLeadingPosition? row shift = some pos) :
    ∃ term : ShiftedLeadingTerm F,
      rowShiftedLeadingTerm? row shift = some term ∧ term.position = pos := by
  have hposOrig := hpos
  unfold rowShiftedLeadingPosition? at hpos
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp [hdeg] at hpos
  | some shiftedDegree =>
      simp [hdeg] at hpos
      have hentry := rowShiftedLeadingPosition?_entry_eq hdeg hposOrig
      rcases shiftedEntryDegree?_eq_some_iff_data.1 hentry with ⟨hne, _⟩
      have hbeq : (rowGet row pos == 0) = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        exact hne (LawfulBEq.eq_of_beq htrue)
      refine ⟨
        { position := pos
          degree := (rowGet row pos).natDegree
          shiftedDegree := shiftedDegree
          coeff := (rowGet row pos).coeff (rowGet row pos).natDegree },
        ?_, rfl⟩
      simp [rowShiftedLeadingTerm?, hdeg, hposOrig, hbeq]

omit [DecidableEq F] in
private theorem rowShiftedLeadingTerm?_some_data
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term) :
    rowShiftedDegree? row shift = some term.shiftedDegree ∧
      rowShiftedLeadingPosition? row shift = some term.position ∧
      rowGet row term.position ≠ 0 ∧
      term.degree = (rowGet row term.position).natDegree ∧
      term.shiftedDegree = term.degree + shift.getD term.position 0 ∧
      term.coeff = (rowGet row term.position).coeff term.degree := by
  unfold rowShiftedLeadingTerm? at hterm
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      simp [hdeg] at hterm
  | some shiftedDegree =>
      cases hpos : rowShiftedLeadingPosition? row shift with
      | none =>
          simp [hdeg, hpos] at hterm
      | some pos =>
          simp [hdeg, hpos] at hterm
          by_cases hzero : rowGet row pos = 0
          · exact False.elim (hterm.1 hzero)
          · have htermEq := hterm.2
            subst term
            have hentry := rowShiftedLeadingPosition?_entry_eq hdeg hpos
            have hentryData := shiftedEntryDegree?_eq_some_iff_data.1 hentry
            rcases hentryData with ⟨_, hshifted⟩
            simpa [hdeg, hpos, hzero, Array.getD_eq_getD_getElem?] using hshifted.symm

omit [DecidableEq F] in
private theorem rowShiftedLeadingTerm?_coeff_ne_zero
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term) :
    term.coeff ≠ 0 := by
  rcases rowShiftedLeadingTerm?_some_data hterm with
    ⟨_, _, hrow, hdegree, _, hcoeff⟩
  intro hzero
  have hlead := CPolynomial.leadingCoeff_ne_zero hrow
  apply hlead
  rw [CPolynomial.leadingCoeff_eq_coeff_natDegree, ← hdegree, ← hcoeff]
  exact hzero

omit [DecidableEq F] in
private theorem cpoly_natDegree_mul_le (P Q : CPolynomial F) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul_le

omit [DecidableEq F] in
private theorem cpoly_natDegree_mul
    {P Q : CPolynomial F} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (P * Q).natDegree = P.natDegree + Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_mul
    ((CPolynomial.toPoly_eq_zero_iff P).not.mpr hP)
    ((CPolynomial.toPoly_eq_zero_iff Q).not.mpr hQ)

omit [DecidableEq F] in
private theorem cpoly_coeff_mul_natDegree_add_ne_zero
    {P Q : CPolynomial F} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (P * Q).coeff (P.natDegree + Q.natDegree) ≠ 0 := by
  have hprod : P * Q ≠ 0 := by
    intro hzero
    have htoProd : (P * Q).toPoly ≠ 0 := by
      rw [CPolynomial.toPoly_mul]
      exact mul_ne_zero
        ((CPolynomial.toPoly_eq_zero_iff P).not.mpr hP)
        ((CPolynomial.toPoly_eq_zero_iff Q).not.mpr hQ)
    exact htoProd (by rw [hzero, CPolynomial.toPoly_zero])
  have hlead := CPolynomial.leadingCoeff_ne_zero hprod
  rw [CPolynomial.leadingCoeff_eq_coeff_natDegree,
    cpoly_natDegree_mul hP hQ] at hlead
  exact hlead

omit [DecidableEq F] in
private theorem cpoly_natDegree_sub_le (P Q : CPolynomial F) :
    (P - Q).natDegree ≤ max P.natDegree Q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_sub,
    CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
  exact Polynomial.natDegree_sub_le P.toPoly Q.toPoly

omit [DecidableEq F] in
private theorem cpoly_natDegree_neg (P : CPolynomial F) :
    (-P).natDegree = P.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_neg,
    CPolynomial.natDegree_toPoly, Polynomial.natDegree_neg]

private theorem cpoly_natDegree_monomial_le (d : Nat) (c : F) :
    (CPolynomial.monomial d c).natDegree ≤ d := by
  by_cases hc : c = 0
  · subst c
    simp [CPolynomial.monomial, CPolynomial.Raw.monomial, CPolynomial.natDegree]
  · rw [CPolynomial.natDegree_monomial hc]

private theorem cpoly_natDegree_monomial_mul_le
    (d : Nat) (c : F) (P : CPolynomial F) :
    (CPolynomial.monomial d c * P).natDegree ≤ d + P.natDegree := by
  have hmul := cpoly_natDegree_mul_le (CPolynomial.monomial d c) P
  have hmono := cpoly_natDegree_monomial_le d c
  omega

private theorem cpoly_coeff_monomial_mul
    (n d : Nat) (c : F) (P : CPolynomial F) :
    (CPolynomial.monomial n c * P).coeff (d + n) =
      c * P.coeff d := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.toPoly_mul]
  have hmono :
      (CPolynomial.monomial n c).toPoly = Polynomial.monomial n c :=
    CPolynomial.monomial_toPoly n c
  rw [hmono]
  rw [Polynomial.coeff_monomial_mul]
  rw [← CPolynomial.coeff_toPoly]

omit [DecidableEq F] in
private theorem cpoly_natDegree_sub_shift_le
    {P Q : CPolynomial F} {shiftDegree bound : Nat}
    (hP : P ≠ 0 → P.natDegree + shiftDegree ≤ bound)
    (hQ : Q ≠ 0 → Q.natDegree + shiftDegree ≤ bound)
    (hne : P - Q ≠ 0) :
    (P - Q).natDegree + shiftDegree ≤ bound := by
  have hsub := cpoly_natDegree_sub_le P Q
  by_cases hPzero : P = 0
  · by_cases hQzero : Q = 0
    · subst P
      subst Q
      simp at hne
    · have hQbound := hQ hQzero
      simpa [hPzero, cpoly_natDegree_neg] using hQbound
  · by_cases hQzero : Q = 0
    · have hPbound := hP hPzero
      simpa [hQzero] using hPbound
    · have hPbound := hP hPzero
      have hQbound := hQ hQzero
      omega

omit [DecidableEq F] in
private theorem cpoly_natDegree_sub_shift_lt
    {P Q : CPolynomial F} {shiftDegree bound : Nat}
    (hP : P ≠ 0 → P.natDegree + shiftDegree < bound)
    (hQ : Q ≠ 0 → Q.natDegree + shiftDegree < bound)
    (hne : P - Q ≠ 0) :
    (P - Q).natDegree + shiftDegree < bound := by
  have hsub := cpoly_natDegree_sub_le P Q
  by_cases hPzero : P = 0
  · by_cases hQzero : Q = 0
    · subst P
      subst Q
      simp at hne
    · have hQbound := hQ hQzero
      simpa [hPzero, cpoly_natDegree_neg] using hQbound
  · by_cases hQzero : Q = 0
    · have hPbound := hP hPzero
      simpa [hQzero] using hPbound
    · have hPbound := hP hPzero
      have hQbound := hQ hQzero
      omega

omit [DecidableEq F] in
private theorem rowShiftedDegree?_le_of_entry_bound
    {row : PolynomialRow F} {shift : Array Nat} {degree bound : Nat}
    (hbound : ∀ k, k < row.size → rowGet row k ≠ 0 →
      (rowGet row k).natDegree + shift.getD k 0 ≤ bound)
    (hdeg : rowShiftedDegree? row shift = some degree) :
    degree ≤ bound := by
  rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hdeg with
    ⟨k, hk, hentry⟩
  rcases shiftedEntryDegree?_eq_some_iff_data.1 hentry with ⟨hne, hentryEq⟩
  have hkBound := hbound k hk hne
  omega

omit [DecidableEq F] in
private theorem rowShiftedLeadingTerm?_entry_bound
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term)
    {k : Nat} (hk : k < row.size) (hne : rowGet row k ≠ 0) :
    (rowGet row k).natDegree + shift.getD k 0 ≤ term.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data hterm with
    ⟨hdeg, _, _, _, _, _⟩
  exact rowShiftedDegree?_entry_bound hdeg hk hne

omit [DecidableEq F] in
private theorem rowShiftedLeadingTerm?_entry_strict_of_pos_lt
    {row : PolynomialRow F} {shift : Array Nat} {term : ShiftedLeadingTerm F}
    (hterm : rowShiftedLeadingTerm? row shift = some term)
    {k : Nat} (hk : k < row.size) (hposlt : term.position < k)
    (hne : rowGet row k ≠ 0) :
    (rowGet row k).natDegree + shift.getD k 0 < term.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data hterm with
    ⟨hdeg, hpos, _, _, _, _⟩
  have hle := rowShiftedDegree?_entry_bound hdeg hk hne
  have hnot :=
    rowShiftedLeadingPosition?_no_larger_tie hdeg hpos hk hposlt
  have hentry := shiftedEntryDegree?_eq_some_of_rowGet_ne_zero (shift := shift) hne
  have hneEq :
      (rowGet row k).natDegree + shift.getD k 0 ≠ term.shiftedDegree := by
    intro heq
    have heq' :
        (rowGet row k).natDegree + shift[k]?.getD 0 = term.shiftedDegree := by
      simpa [Array.getD_eq_getD_getElem?] using heq
    exact hnot (by simpa [heq'] using hentry)
  omega

private theorem rowScaleMonomial_entry_bound_of_leading_terms
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    {k : Nat} (hk : k < reducer.size)
    (hne : rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0) :
    (rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k).natDegree +
        shift.getD k 0 ≤ t.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, _, htShifted, _⟩
  rcases rowShiftedLeadingTerm?_some_data hr with
    ⟨hrRowDegree, _, _, _, hrShifted, _⟩
  have hdegLe : r.degree ≤ t.degree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hdelta : (t.degree - r.degree) + r.shiftedDegree = t.shiftedDegree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hscaledNatDegree :=
    cpoly_natDegree_monomial_mul_le (t.degree - r.degree)
      (t.coeff / r.coeff) (rowGet reducer k)
  have hreducerNonzero : rowGet reducer k ≠ 0 := by
    intro hzero
    apply hne
    simp [rowGet_rowScaleMonomial, hzero]
  have hreducerBound :
      (rowGet reducer k).natDegree + shift.getD k 0 ≤ r.shiftedDegree :=
    rowShiftedDegree?_entry_bound hrRowDegree hk hreducerNonzero
  rw [rowGet_rowScaleMonomial] at hne ⊢
  omega

private theorem rowScaleMonomial_entry_strict_of_pos_lt
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    {k : Nat} (hk : k < reducer.size) (hposlt : t.position < k)
    (hne : rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0) :
    (rowGet
      (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k).natDegree +
        shift.getD k 0 < t.shiftedDegree := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, _, htShifted, _⟩
  rcases rowShiftedLeadingTerm?_some_data hr with
    ⟨_, _, _, _, hrShifted, _⟩
  have hdelta : (t.degree - r.degree) + r.shiftedDegree = t.shiftedDegree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hreducerNonzero : rowGet reducer k ≠ 0 := by
    intro hzero
    apply hne
    simp [rowGet_rowScaleMonomial, hzero]
  have hreducerStrict :
      (rowGet reducer k).natDegree + shift.getD k 0 < r.shiftedDegree := by
    apply rowShiftedLeadingTerm?_entry_strict_of_pos_lt hr hk
    · simpa [← hpos] using hposlt
    · exact hreducerNonzero
  have hscaledNatDegree :=
    cpoly_natDegree_monomial_mul_le (t.degree - r.degree)
      (t.coeff / r.coeff) (rowGet reducer k)
  rw [rowGet_rowScaleMonomial] at hne ⊢
  omega

private theorem cancelShiftedLeadingTerm_coeff_cancel
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hrcoeff : r.coeff ≠ 0) :
    (rowGet (cancelShiftedLeadingTerm target reducer shift) t.position).coeff t.degree = 0 := by
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, htDegree, htShifted, htCoeff⟩
  rcases rowShiftedLeadingTerm?_some_data hr with
    ⟨_, _, _, hrDegree, hrShifted, hrCoeff⟩
  have hdegLe : r.degree ≤ t.degree := by
    have hrShiftedAtTarget :
        r.shiftedDegree = r.degree + shift.getD t.position 0 := by
      simpa [← hpos] using hrShifted
    omega
  have hposBeq : (t.position == r.position) = true := by
    rwa [beq_iff_eq]
  have hrcoeffBeq : (r.coeff == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hrcoeff (LawfulBEq.eq_of_beq htrue)
  unfold cancelShiftedLeadingTerm
  rw [ht, hr]
  simp [hposBeq, hrcoeffBeq, rowGet_rowSub, rowGet_rowScaleMonomial]
  rw [← Array.getD_eq_getD_getElem?]
  change
    (rowGet target t.position -
        CPolynomial.monomial (t.degree - r.degree) (t.coeff / r.coeff) *
          rowGet reducer t.position).coeff t.degree = 0
  rw [CPolynomial.coeff_sub]
  have hreducerCoeff :
      (rowGet reducer t.position).coeff r.degree = r.coeff := by
    have hrCoeffAtTarget :
        r.coeff = (rowGet reducer t.position).coeff r.degree := by
      simpa [← hpos] using hrCoeff
    exact hrCoeffAtTarget.symm
  have hscaled :
      (CPolynomial.monomial (t.degree - r.degree) (t.coeff / r.coeff) *
          rowGet reducer t.position).coeff t.degree = t.coeff := by
    have hsum : r.degree + (t.degree - r.degree) = t.degree := by omega
    have hcoeff := cpoly_coeff_monomial_mul
      (n := t.degree - r.degree) (d := r.degree)
      (c := t.coeff / r.coeff) (P := rowGet reducer t.position)
    rw [hsum, hreducerCoeff] at hcoeff
    simpa [div_mul_cancel₀ t.coeff hrcoeff] using hcoeff
  rw [hscaled]
  simp [htCoeff]

private theorem cancelShiftedLeadingTerm_no_target_shifted_entry
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree) :
    shiftedEntryDegree? (cancelShiftedLeadingTerm target reducer shift) shift t.position ≠
      some t.shiftedDegree := by
  have hrcoeff : r.coeff ≠ 0 := rowShiftedLeadingTerm?_coeff_ne_zero hr
  have hcancelCoeff :=
    cancelShiftedLeadingTerm_coeff_cancel ht hr hpos hle hrcoeff
  rcases rowShiftedLeadingTerm?_some_data ht with
    ⟨_, _, _, _, htShifted, _⟩
  intro hentry
  rcases shiftedEntryDegree?_eq_some_iff_data.1 hentry with
    ⟨hrow, hentryEq⟩
  have hnatDegree :
      (rowGet (cancelShiftedLeadingTerm target reducer shift) t.position).natDegree =
        t.degree := by
    omega
  have hlead :=
    CPolynomial.leadingCoeff_ne_zero hrow
  have hcoeffNonzero :
      (rowGet (cancelShiftedLeadingTerm target reducer shift) t.position).coeff
        t.degree ≠ 0 := by
    rw [← hnatDegree]
    simpa [CPolynomial.leadingCoeff_eq_coeff_natDegree] using hlead
  exact hcoeffNonzero hcancelCoeff

private theorem cancelShiftedLeadingTerm_entry_bound
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hsize : reducer.size = target.size)
    {k : Nat} (hk : k < target.size)
    (hne : rowGet (cancelShiftedLeadingTerm target reducer shift) k ≠ 0) :
    (rowGet (cancelShiftedLeadingTerm target reducer shift) k).natDegree +
        shift.getD k 0 ≤ t.shiftedDegree := by
  have hrcoeff : r.coeff ≠ 0 := rowShiftedLeadingTerm?_coeff_ne_zero hr
  have hposBeq : (t.position == r.position) = true := by
    rwa [beq_iff_eq]
  have hrcoeffBeq : (r.coeff == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hrcoeff (LawfulBEq.eq_of_beq htrue)
  unfold cancelShiftedLeadingTerm at hne ⊢
  rw [ht, hr] at hne ⊢
  simp [hposBeq, hrcoeffBeq, rowGet_rowSub, rowGet_rowScaleMonomial] at hne ⊢
  apply cpoly_natDegree_sub_shift_le
  · intro htargetNonzero
    simpa [Array.getD_eq_getD_getElem?] using
      rowShiftedLeadingTerm?_entry_bound ht hk htargetNonzero
  · intro hscaledNonzero
    have hkReducer : k < reducer.size := by omega
    have hscaledRowNonzero :
        rowGet
          (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0 := by
      simpa [rowGet_rowScaleMonomial] using hscaledNonzero
    have hbound :=
      rowScaleMonomial_entry_bound_of_leading_terms ht hr hpos hle hkReducer
        hscaledRowNonzero
    simpa [rowGet_rowScaleMonomial, Array.getD_eq_getD_getElem?] using hbound
  · exact hne

private theorem cancelShiftedLeadingTerm_entry_strict_of_pos_lt
    {target reducer : PolynomialRow F} {shift : Array Nat}
    {t r : ShiftedLeadingTerm F}
    (ht : rowShiftedLeadingTerm? target shift = some t)
    (hr : rowShiftedLeadingTerm? reducer shift = some r)
    (hpos : t.position = r.position)
    (hle : r.shiftedDegree ≤ t.shiftedDegree)
    (hsize : reducer.size = target.size)
    {k : Nat} (hk : k < target.size) (hposlt : t.position < k)
    (hne : rowGet (cancelShiftedLeadingTerm target reducer shift) k ≠ 0) :
    (rowGet (cancelShiftedLeadingTerm target reducer shift) k).natDegree +
        shift.getD k 0 < t.shiftedDegree := by
  have hrcoeff : r.coeff ≠ 0 := rowShiftedLeadingTerm?_coeff_ne_zero hr
  have hposBeq : (t.position == r.position) = true := by
    rwa [beq_iff_eq]
  have hrcoeffBeq : (r.coeff == 0) = false := by
    rw [Bool.eq_false_iff]
    intro htrue
    exact hrcoeff (LawfulBEq.eq_of_beq htrue)
  unfold cancelShiftedLeadingTerm at hne ⊢
  rw [ht, hr] at hne ⊢
  simp [hposBeq, hrcoeffBeq, rowGet_rowSub, rowGet_rowScaleMonomial] at hne ⊢
  apply cpoly_natDegree_sub_shift_lt
  · intro htargetNonzero
    simpa [Array.getD_eq_getD_getElem?] using
      rowShiftedLeadingTerm?_entry_strict_of_pos_lt ht hk hposlt htargetNonzero
  · intro hscaledNonzero
    have hkReducer : k < reducer.size := by omega
    have hscaledRowNonzero :
        rowGet
          (rowScaleMonomial (t.coeff / r.coeff) (t.degree - r.degree) reducer) k ≠ 0 := by
      simpa [rowGet_rowScaleMonomial] using hscaledNonzero
    have hbound :=
      rowScaleMonomial_entry_strict_of_pos_lt ht hr hpos hle hkReducer hposlt
        hscaledRowNonzero
    simpa [rowGet_rowScaleMonomial, Array.getD_eq_getD_getElem?] using hbound
  · exact hne

private def shiftedRowMeasure (row : PolynomialRow F) (shift : Array Nat) : Nat :=
  match rowShiftedDegree? row shift, rowShiftedLeadingPosition? row shift with
  | some degree, some position => degree * (row.size + 1) + (position + 1)
  | _, _ => 0

private def shiftedMatrixMeasure (M : PolynomialMatrix F) (shift : Array Nat) : Nat :=
  (List.range M.size).foldl
    (fun acc i ↦ acc + shiftedRowMeasure (M.getD i #[]) shift)
    0

private theorem cancelShiftedLeadingTerm_shiftedRowMeasure_lt
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

private theorem foldRange_add_eq_of_pointwise
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

private theorem foldRange_add_lt_of_pointwise_lt
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
private theorem shiftedMatrixMeasure_replaceRow_lt
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

private theorem muldersStorjohannStep_shiftedMatrixMeasure_lt
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

private def matrixShiftedDegreeStep?
    (M : PolynomialMatrix F) (shift : Array Nat)
    (acc : Option Nat) (i : Nat) : Option Nat :=
  match rowShiftedDegree? (M.getD i #[]) shift with
  | none => acc
  | some d => maxOption acc d

private def matrixShiftedDegreeSpec? (M : PolynomialMatrix F) (shift : Array Nat) :
    Option Nat :=
  (List.range M.size).foldl
    (matrixShiftedDegreeStep? M shift)
    none

omit [LawfulBEq F] [DecidableEq F] in
private theorem matrixShiftedDegreeStep?_eq
    (M : PolynomialMatrix F) (shift : Array Nat) :
    matrixShiftedDegreeStep? M shift =
    (fun acc i ↦
      match rowShiftedDegree? (M.getD i #[]) shift with
      | none => acc
      | some d => maxOption acc d) := by
  rfl

omit [LawfulBEq F] [DecidableEq F] in
private theorem matrixShiftedDegree?_eq_spec
    (M : PolynomialMatrix F) (shift : Array Nat) :
    matrixShiftedDegree? M shift = matrixShiftedDegreeSpec? M shift := by
  unfold matrixShiftedDegree? matrixShiftedDegreeSpec?
  rw [matrixShiftedDegreeStep?_eq M shift]
  rfl

omit [LawfulBEq F] [DecidableEq F] in
private theorem matrixShiftedDegreeSpecFold_acc_le
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
private theorem matrixShiftedDegreeSpecFold_row_le
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
private theorem matrixShiftedDegreeSpec?_row_le
    {M : PolynomialMatrix F} {shift : Array Nat} {D i rowDeg : Nat}
    (hmat : matrixShiftedDegreeSpec? M shift = some D)
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    rowDeg ≤ D := by
  unfold matrixShiftedDegreeSpec? at hmat
  exact matrixShiftedDegreeSpecFold_row_le (List.range M.size) hmat
    (List.mem_range.mpr hi) hdeg

omit [LawfulBEq F] [DecidableEq F] in
private theorem matrixShiftedDegree?_row_le
    {M : PolynomialMatrix F} {shift : Array Nat} {D i rowDeg : Nat}
    (hmat : matrixShiftedDegree? M shift = some D)
    (hi : i < M.size)
    (hdeg : rowShiftedDegree? (M.getD i #[]) shift = some rowDeg) :
    rowDeg ≤ D := by
  rw [matrixShiftedDegree?_eq_spec] at hmat
  exact matrixShiftedDegreeSpec?_row_le hmat hi hdeg

omit [LawfulBEq F] [DecidableEq F] in
private theorem matrixShiftedDegreeSpecFold_some_of_acc_some
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
private theorem matrixShiftedDegreeSpecFold_exists_some_of_row
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
private theorem matrixShiftedDegree?_row_le_getD
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
private theorem shiftedRowMeasure_le_of_degree_bound
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
private theorem shiftedMatrixMeasure_range_le_of_degree_bound
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
private theorem shiftedMatrixMeasure_le_of_degree_bound
    {M : PolynomialMatrix F} {shift : Array Nat} {d : Nat}
    (hM : WellFormed M)
    (hbound : ∀ i rowDeg, i < M.size →
      rowShiftedDegree? (M.getD i #[]) shift = some rowDeg → rowDeg ≤ d) :
    shiftedMatrixMeasure M shift ≤
      M.size * ((d + 1) * (MatrixWidth M + 1)) := by
  unfold shiftedMatrixMeasure
  exact shiftedMatrixMeasure_range_le_of_degree_bound hM hbound M.size (Nat.le_refl M.size)

omit [LawfulBEq F] [DecidableEq F] in
private theorem shiftedMatrixMeasure_lt_muldersStorjohannFuel
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

omit [DecidableEq F] in
private theorem rowLinearCombination_range_size
    {M : PolynomialMatrix F} (hM : WellFormed M) (coeffs : Array (CPolynomial F)) :
    ∀ n, n ≤ M.size →
      ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))).size = MatrixWidth M := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [zeroRow]
  | succ n ih =>
      intro hn
      have hnM : n < M.size := by omega
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowAdd_size, ih (by omega), rowScalePolynomial_size,
        matrix_getD_size_of_wellFormed hM hnM, max_self]

omit [DecidableEq F] in
theorem rowLinearCombination_size
    {M : PolynomialMatrix F} (hM : WellFormed M) (coeffs : Array (CPolynomial F)) :
    (rowLinearCombination coeffs M).size = MatrixWidth M := by
  simpa [rowLinearCombination] using
    rowLinearCombination_range_size hM coeffs M.size (Nat.le_refl M.size)

private def rowCombinationTermSupport
    (coeffs : Array (CPolynomial F)) (M : PolynomialMatrix F) (shift : Array Nat) :
    Finset Nat :=
  (Finset.range M.size).filter fun i ↦
    coeffs.getD i 0 ≠ 0 ∧
      rowShiftedDegree? (M.getD i #[]) shift ≠ none

private def rowCombinationTermDegree
    (coeffs : Array (CPolynomial F)) (M : PolynomialMatrix F) (shift : Array Nat)
    (i : Nat) : Nat :=
  match rowShiftedDegree? (M.getD i #[]) shift with
  | some rowDeg => (coeffs.getD i 0).natDegree + rowDeg
  | none => 0

private def rowCombinationTermPosition
    (M : PolynomialMatrix F) (shift : Array Nat) (i : Nat) : Nat :=
  (rowShiftedLeadingPosition? (M.getD i #[]) shift).getD 0

omit [DecidableEq F] in
private theorem rowGet_rowLinearCombination_range_coeff
    {M : PolynomialMatrix F} (coeffs : Array (CPolynomial F))
    (j k : Nat) :
    ∀ n,
      (rowGet
        ((List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M))) j).coeff k =
        ∑ i ∈ Finset.range n,
          ((coeffs.getD i 0) * rowGet (M.getD i #[]) j).coeff k := by
  intro n
  induction n with
  | zero =>
      simp only [List.range_zero, List.foldl_nil, Finset.sum_range_zero]
      rw [rowGet_zeroRow]
      exact CPolynomial.coeff_zero k
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [rowGet_rowAdd, CPolynomial.coeff_add,
        rowGet_rowScalePolynomial, ih, Finset.sum_range_succ]

omit [DecidableEq F] in
theorem rowGet_rowLinearCombination_coeff
    {M : PolynomialMatrix F} (coeffs : Array (CPolynomial F))
    (j k : Nat) :
    (rowGet (rowLinearCombination coeffs M) j).coeff k =
      ∑ i ∈ Finset.range M.size,
        ((coeffs.getD i 0) * rowGet (M.getD i #[]) j).coeff k := by
  simpa [rowLinearCombination] using
    rowGet_rowLinearCombination_range_coeff (M := M) coeffs j k M.size

omit [DecidableEq F] in
private theorem rowLinearCombination_range_eq_zeroRow_of_forall_zero_or_row_zero
    {M : PolynomialMatrix F} (hM : WellFormed M)
    (coeffs : Array (CPolynomial F))
    (hzero : ∀ i, i < M.size →
      coeffs.getD i 0 = 0 ∨ RowIsZero (M.getD i #[])) :
    ∀ n, n ≤ M.size →
      (List.range n).foldl
          (fun acc i ↦
            rowAdd acc
              (rowScalePolynomial (coeffs.getD i 0) (M.getD i #[])))
          (zeroRow (MatrixWidth M)) =
        zeroRow (MatrixWidth M) := by
  intro n hn
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hnM : n < M.size := by omega
      have hrowSize :
          (M.getD n #[]).size = MatrixWidth M :=
        matrix_getD_size_of_wellFormed hM hnM
      have hterm :
          rowScalePolynomial (coeffs.getD n 0) (M.getD n #[]) =
            zeroRow (F := F) (MatrixWidth M) := by
        rcases hzero n hnM with hcoeff | hrowZero
        · rw [hcoeff, rowScalePolynomial_zero, hrowSize]
        · rw [rowScalePolynomial_eq_zeroRow_of_rowIsZero
            (coeffs.getD n 0) hrowZero, hrowSize]
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega), hterm, rowAdd_zeroRow_zeroRow]

omit [DecidableEq F] in
private theorem rowLinearCombination_eq_zeroRow_of_forall_zero_or_row_zero
    {M : PolynomialMatrix F} (hM : WellFormed M)
    (coeffs : Array (CPolynomial F))
    (hzero : ∀ i, i < M.size →
      coeffs.getD i 0 = 0 ∨ RowIsZero (M.getD i #[])) :
    rowLinearCombination coeffs M = zeroRow (F := F) (MatrixWidth M) := by
  simpa [rowLinearCombination] using
    rowLinearCombination_range_eq_zeroRow_of_forall_zero_or_row_zero
      hM coeffs hzero M.size (Nat.le_refl M.size)

private theorem rowCombinationTermSupport_nonempty_of_combination_degree_some
    {M : PolynomialMatrix F} {shift : Array Nat}
    (hM : WellFormed M) {coeffs : Array (CPolynomial F)} {rowDeg : Nat}
    (hdeg : rowShiftedDegree? (rowLinearCombination coeffs M) shift = some rowDeg) :
    (rowCombinationTermSupport coeffs M shift).Nonempty := by
  by_contra hnonempty
  have hzero : ∀ i, i < M.size →
      coeffs.getD i 0 = 0 ∨ RowIsZero (M.getD i #[]) := by
    intro i hi
    have hiNot : i ∉ rowCombinationTermSupport coeffs M shift := by
      intro hiMem
      exact hnonempty ⟨i, hiMem⟩
    by_cases hcoeff : coeffs.getD i 0 = 0
    · exact Or.inl hcoeff
    · right
      have hdegNone : rowShiftedDegree? (M.getD i #[]) shift = none := by
        by_contra hrowDeg
        exact hiNot
          (Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hi, hcoeff, hrowDeg⟩)
      exact (rowShiftedDegree?_eq_none_iff (row := M.getD i #[]) (shift := shift)).1 hdegNone
  have hcombZero :=
    rowLinearCombination_eq_zeroRow_of_forall_zero_or_row_zero hM coeffs hzero
  have hnone :
      rowShiftedDegree? (rowLinearCombination coeffs M) shift = none := by
    rw [hcombZero]
    exact (rowShiftedDegree?_eq_none_iff
      (row := zeroRow (F := F) (MatrixWidth M)) (shift := shift)).2
        (zeroRow_rowIsZero (F := F) (MatrixWidth M))
  rw [hdeg] at hnone
  contradiction

private theorem muldersStorjohannStep_shape_preserved
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    MatrixShape (muldersStorjohannStep M shift i j) = MatrixShape M := by
  simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
  cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      simp
  | some degI =>
      cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
      | none =>
          simp
      | some degJ =>
          simp
          have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
          have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
          split
          · apply replaceRow_shape
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
          · apply replaceRow_shape
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift

private theorem muldersStorjohannStep_rowSpan_subset
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    RowSpan (muldersStorjohannStep M shift i j) ⊆ RowSpan M := by
  apply rowSpan_subset_of_rows_mem hM
  · exact congrArg PolynomialMatrixShape.width
      (muldersStorjohannStep_shape_preserved shift hM)
  · intro row hrow
    simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?] at hrow
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        exact matrix_row_mem_rowSpan hM (by simpa [hI] using hrow)
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            exact matrix_row_mem_rowSpan hM (by simpa [hI, hJ] using hrow)
        | some degJ =>
            have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
            have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
            have hrowI : (M[i]?.getD #[]) ∈ RowSpan M := by
              have hget : M[i]?.getD #[] = M[i] := by
                simp [Array.getElem?_eq_getElem hi]
              rw [hget]
              exact matrix_row_mem_rowSpan hM
                (by simp [MatrixRows, Array.getElem_mem_toList hi])
            have hrowJ : (M[j]?.getD #[]) ∈ RowSpan M := by
              have hget : M[j]?.getD #[] = M[j] := by
                simp [Array.getElem?_eq_getElem hj]
              rw [hget]
              exact matrix_row_mem_rowSpan hM
                (by simp [MatrixRows, Array.getElem_mem_toList hj])
            simp [hI, hJ] at hrow
            split at hrow
            · exact replaceRow_rows_mem_rowSpan hM
                (cancelShiftedLeadingTerm_mem_rowSpan hrowJ hrowI) hrow
            · exact replaceRow_rows_mem_rowSpan hM
                (cancelShiftedLeadingTerm_mem_rowSpan hrowI hrowJ) hrow

private theorem muldersStorjohannStep_rowSpan_superset
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat}
    (hM : WellFormed M) (hi : i < M.size) (hj : j < M.size) (hne : i ≠ j) :
    RowSpan M ⊆ RowSpan (muldersStorjohannStep M shift i j) := by
  apply rowSpan_subset_of_rows_mem
  · simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        simpa [hI] using hM
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            simpa [hI, hJ] using hM
        | some degJ =>
            simp
            split
            · apply replaceRow_wellFormed hM
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
            · apply replaceRow_wellFormed hM
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift
  · exact (congrArg PolynomialMatrixShape.width
      (muldersStorjohannStep_shape_preserved shift hM)).symm
  · intro row hrow
    rcases List.getElem_of_mem hrow with ⟨k, hk, hget⟩
    have hkM : k < M.size := by
      simpa [MatrixRows] using hk
    have hrow_eq : M[k] = row := by
      simpa [MatrixRows, Array.getElem_toList] using hget
    rw [← hrow_eq]
    simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
    cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
    | none =>
        exact matrix_row_mem_rowSpan hM
          (by simp [MatrixRows, Array.getElem_mem_toList hkM])
    | some degI =>
        cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
        | none =>
            exact matrix_row_mem_rowSpan hM
              (by simp [MatrixRows, Array.getElem_mem_toList hkM])
        | some degJ =>
            have hcancelJ_size :
                (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift).size =
                  MatrixWidth M := by
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
            have hreplaceJ_wf :
                WellFormed
                  (replaceRow M j
                    (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) :=
              replaceRow_wellFormed hM hcancelJ_size
            have hcancelI_size :
                (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift).size =
                  MatrixWidth M := by
              simpa [Array.getD_eq_getD_getElem?] using
                cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift
            have hreplaceI_wf :
                WellFormed
                  (replaceRow M i
                    (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) :=
              replaceRow_wellFormed hM hcancelI_size
            have hrowI : (M[i]?.getD #[]) ∈
                RowSpan
                  (replaceRow M j
                    (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) := by
              have hgetI : M[i]?.getD #[] = M[i] := by
                simp [Array.getElem?_eq_getElem hi]
              exact matrix_row_mem_rowSpan hreplaceJ_wf
                (by simpa [hgetI] using replaceRow_oldRow_mem hi (by exact hne.symm))
            have hrowJ : (M[j]?.getD #[]) ∈
                RowSpan
                  (replaceRow M i
                    (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) := by
              have hgetJ : M[j]?.getD #[] = M[j] := by
                simp [Array.getElem?_eq_getElem hj]
              exact matrix_row_mem_rowSpan hreplaceI_wf
                (by simpa [hgetJ] using replaceRow_oldRow_mem hj hne)
            by_cases hdeg : degI ≤ degJ
            · simp only [hdeg, if_true]
              by_cases hkj : k = j
              · subst k
                have hcancel : cancelShiftedLeadingTerm (M[j]?.getD #[])
                    (M[i]?.getD #[]) shift ∈
                    RowSpan
                      (replaceRow M j
                        (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) := by
                  exact matrix_row_mem_rowSpan hreplaceJ_wf (replaceRow_newRow_mem hj)
                have hsize : (M[i]?.getD #[]).size = (M[j]?.getD #[]).size := by
                  rw [matrix_getElem?_getD_size_of_wellFormed hM hi,
                    matrix_getElem?_getD_size_of_wellFormed hM hj]
                have htarget : (M[j]?.getD #[]) ∈
                    RowSpan
                      (replaceRow M j
                        (cancelShiftedLeadingTerm (M[j]?.getD #[]) (M[i]?.getD #[]) shift)) :=
                  cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hrowI hsize
                simpa [Array.getElem?_eq_getElem hj] using htarget
              · have hne' : j ≠ k := fun h ↦ hkj h.symm
                exact matrix_row_mem_rowSpan hreplaceJ_wf (replaceRow_oldRow_mem hkM hne')
            · simp only [hdeg, if_false]
              by_cases hki : k = i
              · subst k
                have hcancel : cancelShiftedLeadingTerm (M[i]?.getD #[])
                    (M[j]?.getD #[]) shift ∈
                    RowSpan
                      (replaceRow M i
                        (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) := by
                  exact matrix_row_mem_rowSpan hreplaceI_wf (replaceRow_newRow_mem hi)
                have hsize : (M[j]?.getD #[]).size = (M[i]?.getD #[]).size := by
                  rw [matrix_getElem?_getD_size_of_wellFormed hM hj,
                    matrix_getElem?_getD_size_of_wellFormed hM hi]
                have htarget : (M[i]?.getD #[]) ∈
                    RowSpan
                      (replaceRow M i
                        (cancelShiftedLeadingTerm (M[i]?.getD #[]) (M[j]?.getD #[]) shift)) :=
                  cancelShiftedLeadingTerm_target_mem_rowSpan hcancel hrowJ hsize
                simpa [Array.getElem?_eq_getElem hi] using htarget
              · have hne' : i ≠ k := fun h ↦ hki h.symm
                exact matrix_row_mem_rowSpan hreplaceI_wf (replaceRow_oldRow_mem hkM hne')

private theorem muldersStorjohannStep_wellFormed
    {M : PolynomialMatrix F} (shift : Array Nat) {i j : Nat} (hM : WellFormed M) :
    WellFormed (muldersStorjohannStep M shift i j) := by
  simp only [muldersStorjohannStep, Array.getD_eq_getD_getElem?]
  cases hI : rowShiftedDegree? (M[i]?.getD #[]) shift with
  | none =>
      simpa [hI] using hM
  | some degI =>
      cases hJ : rowShiftedDegree? (M[j]?.getD #[]) shift with
      | none =>
          simpa [hI, hJ] using hM
      | some degJ =>
          simp
          have hi : i < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hI
          have hj : j < M.size := index_lt_of_rowShiftedDegree?_getElem?_eq_some hJ
          split
          · apply replaceRow_wellFormed hM
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hj hi shift
          · apply replaceRow_wellFormed hM
            simpa [Array.getD_eq_getD_getElem?] using
              cancelShiftedLeadingTerm_size_of_wellFormed hM hi hj shift

private theorem muldersStorjohannReduceWithFuel_shape_preserved
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    MatrixShape (muldersStorjohannReduceWithFuel fuel M shift) = MatrixShape M := by
  induction fuel generalizing M with
  | zero =>
      simp [muldersStorjohannReduceWithFuel]
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · rfl
      · rename_i _ i j hconf
        exact (ih (muldersStorjohannStep M shift i j)
          (muldersStorjohannStep_wellFormed shift hM)).trans
          (muldersStorjohannStep_shape_preserved shift hM)

private theorem muldersStorjohannReduceWithFuel_wellFormed
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    WellFormed (muldersStorjohannReduceWithFuel fuel M shift) := by
  induction fuel generalizing M with
  | zero =>
      simpa [muldersStorjohannReduceWithFuel] using hM
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · exact hM
      · rename_i _ i j hconf
        exact ih (muldersStorjohannStep M shift i j)
          (muldersStorjohannStep_wellFormed shift hM)

private theorem muldersStorjohannReduce_wellFormed
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    WellFormed (muldersStorjohannReduce M shift) := by
  exact muldersStorjohannReduceWithFuel_wellFormed
    (muldersStorjohannFuel M shift) M shift hM

private theorem muldersStorjohannReduceWithFuel_no_conflict_of_measure_lt
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M)
    (hfuel : shiftedMatrixMeasure M shift < fuel) :
    shiftedLeadingConflict? (muldersStorjohannReduceWithFuel fuel M shift) shift = none := by
  induction fuel generalizing M with
  | zero =>
      omega
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      cases hconf : shiftedLeadingConflict? M shift with
      | none =>
          simp [hconf]
      | some pair =>
          rcases pair with ⟨i, j⟩
          have hstepLt :=
            muldersStorjohannStep_shiftedMatrixMeasure_lt hM hconf
          have hstepFuel :
              shiftedMatrixMeasure (muldersStorjohannStep M shift i j) shift < fuel := by
            omega
          exact ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM) hstepFuel

private theorem muldersStorjohannReduce_no_conflict
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    shiftedLeadingConflict? (muldersStorjohannReduce M shift) shift = none := by
  exact muldersStorjohannReduceWithFuel_no_conflict_of_measure_lt
    (muldersStorjohannFuel M shift) M shift hM
    (shiftedMatrixMeasure_lt_muldersStorjohannFuel hM)

private theorem muldersStorjohannReduceWithFuel_rowSpan_subset
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduceWithFuel fuel M shift) ⊆ RowSpan M := by
  induction fuel generalizing M with
  | zero =>
      intro row hrow
      simpa [muldersStorjohannReduceWithFuel] using hrow
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · intro row hrow
        exact hrow
      · rename_i _ i j hconf
        exact Set.Subset.trans
          (ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM))
          (muldersStorjohannStep_rowSpan_subset shift hM)

private theorem muldersStorjohannReduce_rowSpan_subset
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduce M shift) ⊆ RowSpan M := by
  exact muldersStorjohannReduceWithFuel_rowSpan_subset
    (muldersStorjohannFuel M shift) M shift hM

private theorem muldersStorjohannReduceWithFuel_rowSpan_superset
    (fuel : Nat) (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan M ⊆ RowSpan (muldersStorjohannReduceWithFuel fuel M shift) := by
  induction fuel generalizing M with
  | zero =>
      intro row hrow
      simpa [muldersStorjohannReduceWithFuel] using hrow
  | succ fuel ih =>
      rw [muldersStorjohannReduceWithFuel]
      split
      · intro row hrow
        exact hrow
      · rename_i _ i j hconf
        rcases shiftedLeadingConflict?_some_bounds hconf with ⟨hi, hj, hij⟩
        have hne : i ≠ j := by omega
        exact Set.Subset.trans
          (muldersStorjohannStep_rowSpan_superset shift hM hi hj hne)
          (ih (muldersStorjohannStep M shift i j)
            (muldersStorjohannStep_wellFormed shift hM))

private theorem muldersStorjohannReduce_rowSpan_superset
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan M ⊆ RowSpan (muldersStorjohannReduce M shift) := by
  exact muldersStorjohannReduceWithFuel_rowSpan_superset
    (muldersStorjohannFuel M shift) M shift hM

theorem muldersStorjohannReduce_shape_preserved
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    MatrixShape (muldersStorjohannReduce M shift) = MatrixShape M := by
  exact muldersStorjohannReduceWithFuel_shape_preserved
    (muldersStorjohannFuel M shift) M shift hM

theorem muldersStorjohannReduce_rowSpan_eq
    (M : PolynomialMatrix F) (shift : Array Nat) (hM : WellFormed M) :
    RowSpan (muldersStorjohannReduce M shift) = RowSpan M := by
  apply Set.Subset.antisymm
  · exact muldersStorjohannReduce_rowSpan_subset M shift hM
  · exact muldersStorjohannReduce_rowSpan_superset M shift hM

theorem muldersStorjohannReduce_weakPopov
    (M : PolynomialMatrix F) (shift : Array Nat)
    (hM : WellFormed M) (_hshift : shift.size = MatrixWidth M) :
    ShiftedWeakPopov (muldersStorjohannReduce M shift) shift := by
  exact shiftedLeadingConflict?_none_weakPopov
    (muldersStorjohannReduce_no_conflict M shift hM)

theorem muldersStorjohannReduce_least_row_minimal
    (M : PolynomialMatrix F) (shift : Array Nat) (row : PolynomialRow F)
    (hM : WellFormed M) (hshift : shift.size = MatrixWidth M)
    (hrow : row ∈ RowSpan M)
    (hdeg : rowShiftedDegree? row shift ≠ none) :
    ∃ outRow outDeg rowDeg,
      outRow ∈ MatrixRows (muldersStorjohannReduce M shift) ∧
      rowShiftedDegree? outRow shift = some outDeg ∧
      rowShiftedDegree? row shift = some rowDeg ∧
      outDeg ≤ rowDeg := by
  let R := muldersStorjohannReduce M shift
  have hRwf : WellFormed R := muldersStorjohannReduce_wellFormed M shift hM
  have hwp : ShiftedWeakPopov R shift :=
    muldersStorjohannReduce_weakPopov M shift hM hshift
  have hspan : RowSpan R = RowSpan M :=
    muldersStorjohannReduce_rowSpan_eq M shift hM
  have hrowR : row ∈ RowSpan R := by
    rwa [hspan]
  rcases hrowR with ⟨coeffs, _hcoeffsSize, hrowEq⟩
  subst row
  cases hrowDeg : rowShiftedDegree? (rowLinearCombination coeffs R) shift with
  | none =>
      exact False.elim (hdeg hrowDeg)
  | some rowDeg =>
      let S := rowCombinationTermSupport coeffs R shift
      have hS : S.Nonempty :=
        rowCombinationTermSupport_nonempty_of_combination_degree_some
          hRwf hrowDeg
      obtain ⟨imax, himaxS, hmaxDegree⟩ :=
        Finset.exists_max_image S
          (rowCombinationTermDegree coeffs R shift) hS
      let D := rowCombinationTermDegree coeffs R shift imax
      let T := S.filter fun i ↦ rowCombinationTermDegree coeffs R shift i = D
      have hT : T.Nonempty := by
        refine ⟨imax, ?_⟩
        exact Finset.mem_filter.mpr ⟨himaxS, rfl⟩
      obtain ⟨i, hiT, hmaxPos⟩ :=
        Finset.exists_max_image T (rowCombinationTermPosition R shift) hT
      have hiS : i ∈ S := (Finset.mem_filter.mp hiT).1
      have hiDegreeEq :
          rowCombinationTermDegree coeffs R shift i = D :=
        (Finset.mem_filter.mp hiT).2
      rcases (Finset.mem_filter.mp hiS) with
        ⟨hiRange, hcoeffI, hrowDegI_ne⟩
      have hi : i < R.size := Finset.mem_range.mp hiRange
      cases hrowDegI : rowShiftedDegree? (R.getD i #[]) shift with
      | none =>
          exact False.elim (hrowDegI_ne hrowDegI)
      | some outDeg =>
          rcases rowShiftedLeadingPosition?_some_of_degree hrowDegI with
            ⟨posI, hposI⟩
          have hposIRow : posI < (R.getD i #[]).size :=
            rowShiftedLeadingPosition?_lt hposI
          have hposIWidth : posI < MatrixWidth R := by
            rw [matrix_getD_size_of_wellFormed hRwf hi] at hposIRow
            exact hposIRow
          have hentryIData :=
            shiftedEntryDegree?_eq_some_iff_data.1
              (rowShiftedLeadingPosition?_entry_eq hrowDegI hposI)
          rcases hentryIData with ⟨hentryINe, hentryIShift⟩
          let coeffI := coeffs.getD i 0
          let entryI := rowGet (R.getD i #[]) posI
          let k := coeffI.natDegree + entryI.natDegree
          have hdegreeI_expr :
              rowCombinationTermDegree coeffs R shift i =
                coeffI.natDegree + outDeg := by
            unfold rowCombinationTermDegree coeffI
            rw [hrowDegI]
          have hD_eq : D = k + shift.getD posI 0 := by
            rw [← hiDegreeEq, hdegreeI_expr, ← hentryIShift]
            unfold k entryI
            omega
          have hselectedCoeffNe :
              (coeffs.getD i 0 * rowGet (R.getD i #[]) posI).coeff k ≠ 0 := by
            simpa [coeffI, entryI, k] using
              cpoly_coeff_mul_natDegree_add_ne_zero
                (P := coeffI) (Q := entryI) hcoeffI hentryINe
          have hotherCoeffZero :
              ∀ l, l < R.size → l ≠ i →
                (coeffs.getD l 0 * rowGet (R.getD l #[]) posI).coeff k = 0 := by
            intro l hl hli
            by_contra hcoeffAtK
            let coeffL := coeffs.getD l 0
            let entryL := rowGet (R.getD l #[]) posI
            have hprodNonzero : coeffL * entryL ≠ 0 := by
              intro hprodZero
              exact hcoeffAtK (by
                have hprodZero' :
                    coeffs.getD l 0 * rowGet (R.getD l #[]) posI = 0 := by
                  simpa [coeffL, entryL] using hprodZero
                rw [hprodZero']
                exact CPolynomial.coeff_zero k)
            have hcoeffL : coeffL ≠ 0 := by
              intro hzero
              exact hprodNonzero (by simp [coeffL, hzero])
            have hentryL : entryL ≠ 0 := by
              intro hzero
              exact hprodNonzero (by simp [entryL, hzero])
            have hposIRowL : posI < (R.getD l #[]).size := by
              rw [matrix_getD_size_of_wellFormed hRwf hl]
              exact hposIWidth
            have hrowDegL_ne :
                rowShiftedDegree? (R.getD l #[]) shift ≠ none := by
              intro hnone
              have hrowZero :=
                (rowShiftedDegree?_eq_none_iff
                  (row := R.getD l #[]) (shift := shift)).1 hnone
              have hentryZero : rowGet (R.getD l #[]) posI = 0 := by
                unfold rowGet
                rw [Array.getD_eq_getD_getElem?,
                  Array.getElem?_eq_getElem hposIRowL]
                exact hrowZero (R.getD l #[])[posI]
                  (by simpa only [Array.mem_def] using
                    Array.getElem_mem_toList hposIRowL)
              exact hentryL (by simpa [entryL] using hentryZero)
            have hlS : l ∈ S :=
              Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hl, hcoeffL, hrowDegL_ne⟩
            cases hrowDegL : rowShiftedDegree? (R.getD l #[]) shift with
            | none =>
                exact hrowDegL_ne hrowDegL
            | some outDegL =>
                rcases rowShiftedLeadingPosition?_some_of_degree hrowDegL with
                  ⟨posL, hposL⟩
                have hdegreeL_le_D :
                    rowCombinationTermDegree coeffs R shift l ≤ D := by
                  simpa [D] using hmaxDegree l hlS
                have hk_le_prod :
                    k ≤ (coeffL * entryL).natDegree :=
                  CPolynomial.le_natDegree_of_ne_zero hcoeffAtK
                have hprodDeg_le :
                    (coeffL * entryL).natDegree ≤
                      coeffL.natDegree + entryL.natDegree :=
                  cpoly_natDegree_mul_le coeffL entryL
                have hentryBound :
                    entryL.natDegree + shift.getD posI 0 ≤ outDegL := by
                  exact rowShiftedDegree?_entry_bound hrowDegL
                    hposIRowL (by simpa [entryL] using hentryL)
                have hD_le_degreeL : D ≤ coeffL.natDegree + outDegL := by
                  rw [hD_eq]
                  omega
                have hdegreeL_eq_D : coeffL.natDegree + outDegL = D := by
                  have hdegreeL_expr :
                      rowCombinationTermDegree coeffs R shift l =
                        coeffL.natDegree + outDegL := by
                    unfold rowCombinationTermDegree coeffL
                    rw [hrowDegL]
                  have hle : coeffL.natDegree + outDegL ≤ D := by
                    simpa [hdegreeL_expr] using hdegreeL_le_D
                  exact le_antisymm hle hD_le_degreeL
                have hD_le_entry :
                    D ≤ coeffL.natDegree +
                      (entryL.natDegree + shift.getD posI 0) := by
                  rw [hD_eq]
                  omega
                have hentryShiftEq :
                    entryL.natDegree + shift.getD posI 0 = outDegL := by
                  omega
                have hentryShiftL :
                    shiftedEntryDegree? (R.getD l #[]) shift posI =
                      some outDegL := by
                  have hsome :=
                    shiftedEntryDegree?_eq_some_of_rowGet_ne_zero
                      (row := R.getD l #[]) (shift := shift) (j := posI)
                      (by simpa [entryL] using hentryL)
                  have hentryShiftEq' :
                      (rowGet (R.getD l #[]) posI).natDegree +
                          shift.getD posI 0 = outDegL := by
                    simpa [entryL] using hentryShiftEq
                  rw [hentryShiftEq'] at hsome
                  exact hsome
                have hposI_le_posL : posI ≤ posL :=
                  rowShiftedLeadingPosition?_le_of_entry_eq_degree
                    hrowDegL hposL hposIRowL hentryShiftL
                have hlDegreeEq :
                    rowCombinationTermDegree coeffs R shift l = D := by
                  have hdegreeL_expr :
                      rowCombinationTermDegree coeffs R shift l =
                        coeffL.natDegree + outDegL := by
                    unfold rowCombinationTermDegree coeffL
                    rw [hrowDegL]
                  rw [hdegreeL_expr, hdegreeL_eq_D]
                have hlT : l ∈ T :=
                  Finset.mem_filter.mpr ⟨hlS, hlDegreeEq⟩
                have hposL_le_posI : posL ≤ posI := by
                  have hle := hmaxPos l hlT
                  have hposLval :
                      rowCombinationTermPosition R shift l = posL := by
                    unfold rowCombinationTermPosition
                    rw [hposL]
                    rfl
                  have hposIval :
                      rowCombinationTermPosition R shift i = posI := by
                    unfold rowCombinationTermPosition
                    rw [hposI]
                    rfl
                  rwa [hposLval, hposIval] at hle
                have hposEq : posL = posI :=
                  le_antisymm hposL_le_posI hposI_le_posL
                have hposNe :=
                  hwp l i hl hi hli
                    (by rw [hposL]; simp)
                    (by rw [hposI]; simp)
                exact hposNe (by rw [hposL, hposI, hposEq])
          have hcomboCoeffNe :
              (rowGet (rowLinearCombination coeffs R) posI).coeff k ≠ 0 := by
            rw [rowGet_rowLinearCombination_coeff]
            rw [Finset.sum_eq_single i]
            · exact hselectedCoeffNe
            · intro l hlRange hli
              exact hotherCoeffZero l (Finset.mem_range.mp hlRange) hli
            · intro hiNot
              exact False.elim (hiNot (Finset.mem_range.mpr hi))
          have hcomboEntryNe :
              rowGet (rowLinearCombination coeffs R) posI ≠ 0 := by
            intro hzero
            exact hcomboCoeffNe (by
              rw [hzero]
              exact CPolynomial.coeff_zero k)
          have hcomboPos : posI < (rowLinearCombination coeffs R).size := by
            simpa [rowLinearCombination_size hRwf coeffs] using hposIWidth
          have hcomboEntryBound :
              (rowGet (rowLinearCombination coeffs R) posI).natDegree +
                  shift.getD posI 0 ≤ rowDeg :=
            rowShiftedDegree?_entry_bound hrowDeg hcomboPos hcomboEntryNe
          have hk_le_combo :
              k ≤ (rowGet (rowLinearCombination coeffs R) posI).natDegree :=
            CPolynomial.le_natDegree_of_ne_zero hcomboCoeffNe
          have hD_le_rowDeg : D ≤ rowDeg := by
            rw [hD_eq]
            exact le_trans (Nat.add_le_add_right hk_le_combo _)
              hcomboEntryBound
          have houtDeg_le_D : outDeg ≤ D := by
            rw [← hiDegreeEq, hdegreeI_expr]
            omega
          refine ⟨R.getD i #[], outDeg, rowDeg, ?_, hrowDegI, rfl, ?_⟩
          · rw [MatrixRows]
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
            exact Array.getElem_mem_toList hi
          · exact le_trans houtDeg_le_D hD_le_rowDeg

/-- Certified direct Mulders-Storjohann shifted row-reducer context. -/
def muldersStorjohannReducerContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] : ShiftedRowReducerContext F where
  reduce := muldersStorjohannReduce
  shape_preserved := by
    intro M shift hM
    exact muldersStorjohannReduce_shape_preserved M shift hM
  rowSpan_eq := by
    intro M shift hM
    exact muldersStorjohannReduce_rowSpan_eq M shift hM
  weakPopov := by
    intro M shift hM hshift
    exact muldersStorjohannReduce_weakPopov M shift hM hshift
  least_row_minimal := by
    intro M shift row hM hshift hrow hdeg
    exact muldersStorjohannReduce_least_row_minimal M shift row hM hshift hrow hdeg

end PolynomialMatrix

end CompPoly
