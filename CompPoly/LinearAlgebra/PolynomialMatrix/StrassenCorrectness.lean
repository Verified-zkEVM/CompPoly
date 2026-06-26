/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Operations
import Mathlib.Tactic.Abel

/-!
# Strassen Polynomial-Matrix Product Correctness

Correctness proofs for the Strassen-style polynomial-matrix products in
`CompPoly.LinearAlgebra.PolynomialMatrix.Operations`:

* `rowGet_rowMulMatrixWith`: entry semantics of the naive row-by-matrix product.
* `mulBoundedWith_eq_mulWith`: the degree-capped low-product reconstruction equals
  the naive product.
* `mulStrassenWith_eq_mulWith` and `mulStrassenWithFuel_eq_mulWith`: the Strassen
  recursion computes exactly the naive matrix product, as arrays.
* `mulTruncColumnStrassenWith_eq_truncateColumns` and
  `mulTruncColumnStrassenWith_entry`: the column-truncated Strassen recursion
  computes exactly the column-truncated naive product.
-/

namespace CompPoly

namespace PolynomialMatrix

variable {F : Type*}

/-! ## Generic array and fold helpers -/

private theorem getD_of_lt {α : Type*} (a : Array α) (d : α) {i : Nat}
    (hi : i < a.size) : a.getD i d = a[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

private theorem getD_of_le {α : Type*} (a : Array α) (d : α) {i : Nat}
    (hi : a.size ≤ i) : a.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi, Option.getD_none]

private theorem getD_list_range_map {α : Type*} (g : Nat → α) (n j : Nat) (d : α) :
    (((List.range n).map g).toArray).getD j d = if j < n then g j else d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  by_cases hj : j < n
  · rw [List.getElem?_range hj]
    simp [hj]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)]
    simp [hj]

private theorem foldl_add_eq_add_sum {M : Type*} [AddCommMonoid M] (g : Nat → M) :
    ∀ (n : Nat) (init : M),
      (List.range n).foldl (fun acc k ↦ acc + g k) init =
        init + ∑ k ∈ Finset.range n, g k
  | 0, init => by simp
  | n + 1, init => by
      rw [List.range_succ, List.foldl_append, foldl_add_eq_add_sum g n init,
        List.foldl_cons, List.foldl_nil, Finset.sum_range_succ, add_assoc]

private theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M] (g : Nat → M) (n : Nat) :
    (List.range n).foldl (fun acc k ↦ acc + g k) 0 = ∑ k ∈ Finset.range n, g k := by
  rw [foldl_add_eq_add_sum, zero_add]

private theorem le_foldl_max_init (g : Nat → Nat) :
    ∀ (l : List Nat) (init : Nat), init ≤ l.foldl (fun acc k ↦ max acc (g k)) init
  | [], _ => Nat.le_refl _
  | x :: t, init =>
      Nat.le_trans (Nat.le_max_left init (g x)) (le_foldl_max_init g t (max init (g x)))

private theorem le_foldl_max (g : Nat → Nat) :
    ∀ (l : List Nat) (init : Nat) {k : Nat}, k ∈ l →
      g k ≤ l.foldl (fun acc i ↦ max acc (g i)) init
  | x :: t, init, k, hk => by
      rcases List.mem_cons.1 hk with rfl | hk
      · exact Nat.le_trans (Nat.le_max_right init (g k)) (le_foldl_max_init g t _)
      · exact le_foldl_max g t _ hk

/-- The fuel-bounded doubling loop reaches its target when given enough fuel. -/
private theorem le_nextPowerOfTwoAtLeastLoop (target : Nat) :
    ∀ (fuel current : Nat), 1 ≤ current → target ≤ current + fuel →
      target ≤ nextPowerOfTwoAtLeastLoop target fuel current
  | 0, current, _, h => by
      simpa [nextPowerOfTwoAtLeastLoop] using h
  | fuel + 1, current, hcur, h => by
      rw [nextPowerOfTwoAtLeastLoop]
      split
      · assumption
      · exact le_nextPowerOfTwoAtLeastLoop target fuel (2 * current) (by omega) (by omega)

/-- `nextPowerOfTwoAtLeast` is at least its target. -/
theorem le_nextPowerOfTwoAtLeast (target : Nat) :
    target ≤ nextPowerOfTwoAtLeast target :=
  le_nextPowerOfTwoAtLeastLoop target (target + 1) 1 (Nat.le_refl 1) (by omega)

/-- Entry access for `natArraySlice`. -/
theorem natArraySlice_getD (values : Array Nat) (start count j : Nat) :
    (natArraySlice values start count).getD j 0 =
      if j < count then values.getD (start + j) 0 else 0 := by
  rw [natArraySlice, getD_list_range_map]

/-- Entry access for `maxNatArrays`. -/
theorem maxNatArrays_getD (a b : Array Nat) (j : Nat) :
    (maxNatArrays a b).getD j 0 = max (a.getD j 0) (b.getD j 0) := by
  rw [maxNatArrays, getD_list_range_map]
  split
  · rfl
  · rename_i h
    rw [getD_of_le a 0 (by omega), getD_of_le b 0 (by omega), Nat.max_self]

/-! ## Row access helpers -/

/-- Reading a row past its width yields zero. -/
theorem rowGet_of_size_le [Zero F] {row : PolynomialRow F} {j : Nat}
    (hj : row.size ≤ j) : rowGet row j = 0 :=
  getD_of_le row 0 hj

private theorem rowGet_getD_of_size_le [Zero F] {M : PolynomialMatrix F} {i : Nat}
    (hi : M.size ≤ i) (j : Nat) : rowGet (M.getD i #[]) j = 0 := by
  rw [getD_of_le M #[] hi]
  exact rowGet_of_size_le (Nat.zero_le j)

private theorem rowGet_list_range_map [Zero F] (g : Nat → CPolynomial F) (w j : Nat) :
    rowGet (((List.range w).map g).toArray) j = if j < w then g j else 0 := by
  rw [rowGet, getD_list_range_map]

/-! ## `truncateX` algebra -/

/-- Truncation of the zero polynomial. -/
theorem truncateX_zero [Semiring F] [BEq F] [LawfulBEq F] (order : Nat) :
    truncateX order (0 : CPolynomial F) = 0 := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  simp only [truncateX_coeff, CPolynomial.coeff_zero, ite_self]

/-- Truncation distributes over addition. -/
theorem truncateX_add [Semiring F] [BEq F] [LawfulBEq F] (order : Nat)
    (p q : CPolynomial F) :
    truncateX order (p + q) = truncateX order p + truncateX order q := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  simp only [truncateX_coeff, CPolynomial.coeff_add]
  by_cases hi : i < order
  · simp only [if_pos hi]
  · simp only [if_neg hi, add_zero]

/-- Truncation distributes over subtraction. -/
theorem truncateX_sub [Ring F] [BEq F] [LawfulBEq F] (order : Nat)
    (p q : CPolynomial F) :
    truncateX order (p - q) = truncateX order p - truncateX order q := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  simp only [truncateX_coeff, CPolynomial.coeff_sub]
  by_cases hi : i < order
  · simp only [if_pos hi]
  · simp only [if_neg hi, sub_zero]

/-- Nested truncations keep the smaller order. -/
theorem truncateX_truncateX [Semiring F] [BEq F] [LawfulBEq F] (o o' : Nat)
    (p : CPolynomial F) :
    truncateX o (truncateX o' p) = truncateX (min o o') p := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  simp only [truncateX_coeff]
  by_cases h₁ : i < o
  · by_cases h₂ : i < o'
    · rw [if_pos h₁, if_pos h₂, if_pos (by omega)]
    · rw [if_pos h₁, if_neg h₂, if_neg (by omega)]
  · rw [if_neg h₁, if_neg (by omega)]

/-- Truncation distributes over finite range sums. -/
theorem truncateX_sum [Semiring F] [BEq F] [LawfulBEq F] (order n : Nat)
    (f : Nat → CPolynomial F) :
    truncateX order (∑ k ∈ Finset.range n, f k) =
      ∑ k ∈ Finset.range n, truncateX order (f k) := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  rw [truncateX_coeff, CPolynomial.coeff_finset_sum, CPolynomial.coeff_finset_sum]
  simp only [truncateX_coeff]
  by_cases hi : i < order
  · simp only [if_pos hi]
  · simp only [if_neg hi, Finset.sum_const_zero]

private theorem coeff_eq_zero_of_natDegree_lt [Zero F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {i : Nat} (h : p.natDegree < i) :
    CPolynomial.coeff p i = 0 := by
  by_contra hne
  exact absurd (CPolynomial.le_natDegree_of_ne_zero hne) (by omega)

private theorem coeff_mul_eq_zero_of_natDegree_lt [Semiring F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} {i : Nat} (h : p.natDegree + q.natDegree < i) :
    CPolynomial.coeff (p * q) i = 0 := by
  rw [CPolynomial.coeff_mul]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rcases Nat.lt_or_ge p.natDegree k with hk' | hk'
  · rw [coeff_eq_zero_of_natDegree_lt hk', zero_mul]
  · rw [coeff_eq_zero_of_natDegree_lt (p := q) (by omega), mul_zero]

/-- A product is unchanged by truncation past its coefficient cap. -/
theorem truncateX_mul_of_productCoeffCap_le [Semiring F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} {order : Nat} (h : productCoeffCap p q ≤ order) :
    truncateX order (p * q) = p * q := by
  by_cases hz : (p == 0 || q == 0) = true
  · simp only [Bool.or_eq_true, beq_iff_eq] at hz
    rcases hz with hp | hq
    · rw [hp, CPolynomial.zero_mul, truncateX_zero]
    · rw [hq, CPolynomial.mul_zero, truncateX_zero]
  · rw [productCoeffCap, if_neg hz] at h
    rw [CPolynomial.eq_iff_coeff]
    intro i
    rw [truncateX_coeff]
    split
    · rfl
    · exact (coeff_mul_eq_zero_of_natDegree_lt (by omega)).symm

/-! ## `ofFn` access toolkit -/

/-- Row count of `ofFn`. -/
theorem ofFn_size [Zero F] (rows width : Nat) (entry : Nat → Nat → CPolynomial F) :
    (ofFn rows width entry).size = rows := by
  simp only [ofFn, List.size_toArray, List.length_map, List.length_range]

private theorem getElem_ofFn [Zero F] {rows width : Nat}
    {entry : Nat → Nat → CPolynomial F} {i : Nat}
    (hi : i < (ofFn rows width entry).size) :
    (ofFn rows width entry)[i] = ((List.range width).map (entry i)).toArray := by
  simp only [ofFn, List.getElem_toArray, List.getElem_map, List.getElem_range]

/-- Row access for `ofFn` with zero defaults. -/
theorem getD_ofFn [Zero F] (rows width : Nat) (entry : Nat → Nat → CPolynomial F)
    (i : Nat) :
    (ofFn rows width entry).getD i #[] =
      if i < rows then ((List.range width).map (entry i)).toArray else #[] := by
  rw [ofFn, getD_list_range_map]

/-- Entry access for `ofFn` with zero defaults. -/
theorem rowGet_ofFn [Zero F] (rows width : Nat) (entry : Nat → Nat → CPolynomial F)
    (i j : Nat) :
    rowGet ((ofFn rows width entry).getD i #[]) j =
      if i < rows ∧ j < width then entry i j else 0 := by
  rw [getD_ofFn]
  by_cases hi : i < rows
  · rw [if_pos hi, rowGet_list_range_map]
    by_cases hj : j < width
    · rw [if_pos hj, if_pos ⟨hi, hj⟩]
    · rw [if_neg hj, if_neg (fun hc ↦ hj hc.2)]
  · rw [if_neg hi, if_neg (fun hc ↦ hi hc.1)]
    exact rowGet_of_size_le (Nat.zero_le j)

private theorem matrixWidth_eq_getD_size [Zero F] (M : PolynomialMatrix F) :
    MatrixWidth M = (M.getD 0 #[]).size := by
  unfold MatrixWidth
  rw [Array.getD_eq_getD_getElem?]
  cases M[0]? <;> rfl

/-- Width of `ofFn`. -/
theorem MatrixWidth_ofFn [Zero F] (rows width : Nat)
    (entry : Nat → Nat → CPolynomial F) :
    MatrixWidth (ofFn rows width entry) = if rows = 0 then 0 else width := by
  rw [matrixWidth_eq_getD_size, getD_ofFn]
  by_cases h : rows = 0
  · subst h
    rw [if_neg (by omega), if_pos rfl]
    rfl
  · rw [if_pos (by omega), if_neg h]
    simp only [List.size_toArray, List.length_map, List.length_range]

/-- Width of a square `ofFn`. -/
theorem MatrixWidth_ofFn_square [Zero F] (n : Nat)
    (entry : Nat → Nat → CPolynomial F) :
    MatrixWidth (ofFn n n entry) = n := by
  rw [MatrixWidth_ofFn]
  split <;> omega

/-- Two `ofFn` matrices with entrywise-equal in-range entries are equal. -/
theorem ofFn_congr [Zero F] {rows width : Nat} {f g : Nat → Nat → CPolynomial F}
    (h : ∀ i < rows, ∀ j < width, f i j = g i j) :
    ofFn rows width f = ofFn rows width g := by
  rw [ofFn, ofFn]
  refine congrArg List.toArray (List.map_congr_left fun i hi ↦ ?_)
  refine congrArg List.toArray (List.map_congr_left fun j hj ↦ ?_)
  exact h i (List.mem_range.mp hi) j (List.mem_range.mp hj)

private theorem map_eq_ofFn [Zero F] {M : PolynomialMatrix F} {w : Nat}
    {f : PolynomialRow F → PolynomialRow F} {entry : Nat → Nat → CPolynomial F}
    (hf : ∀ i, i < M.size →
      f (M.getD i #[]) = ((List.range w).map (entry i)).toArray) :
    M.map f = ofFn M.size w entry := by
  refine Array.ext (by rw [Array.size_map, ofFn_size]) fun i hi₁ hi₂ ↦ ?_
  rw [Array.size_map] at hi₁
  rw [Array.getElem_map, getElem_ofFn, ← getD_of_lt M #[] hi₁]
  exact hf i hi₁

/-! ## Naive product semantics -/

/-- Width of a naive row-by-matrix product. -/
theorem rowMulMatrixWith_size [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) :
    (rowMulMatrixWith mulCtx row M).size = MatrixWidth M := by
  simp only [rowMulMatrixWith, List.size_toArray, List.length_map, List.length_range]

/-- Entry semantics of the naive row-by-matrix product. -/
theorem rowGet_rowMulMatrixWith [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) {j : Nat} (hj : j < MatrixWidth M) :
    rowGet (rowMulMatrixWith mulCtx row M) j =
      ∑ k ∈ Finset.range row.size, rowGet row k * rowGet (M.getD k #[]) j := by
  rw [rowMulMatrixWith, rowGet_list_range_map, if_pos hj, foldl_add_eq_sum]
  simp only [mulCtx.mul_eq_mul]

/-- The naive row-by-matrix product is zero past the matrix width. -/
theorem rowGet_rowMulMatrixWith_of_width_le [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) {j : Nat} (hj : MatrixWidth M ≤ j) :
    rowGet (rowMulMatrixWith mulCtx row M) j = 0 :=
  rowGet_of_size_le (by rw [rowMulMatrixWith_size]; exact hj)

private theorem sum_entry_eq_of_matrix_le [Semiring F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (B : PolynomialMatrix F) (j : Nat) {n : Nat}
    (hn : B.size ≤ n) :
    ∑ k ∈ Finset.range n, rowGet row k * rowGet (B.getD k #[]) j =
      ∑ k ∈ Finset.range B.size, rowGet row k * rowGet (B.getD k #[]) j :=
  Finset.eventually_constant_sum
    (fun k hk ↦ by rw [rowGet_getD_of_size_le hk, CPolynomial.mul_zero]) hn

private theorem sum_entry_eq_of_row_le [Semiring F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (B : PolynomialMatrix F) (j : Nat) {n : Nat}
    (hn : row.size ≤ n) :
    ∑ k ∈ Finset.range n, rowGet row k * rowGet (B.getD k #[]) j =
      ∑ k ∈ Finset.range row.size, rowGet row k * rowGet (B.getD k #[]) j :=
  Finset.eventually_constant_sum
    (fun k hk ↦ by rw [rowGet_of_size_le hk, CPolynomial.zero_mul]) hn

private theorem sum_entry_row_size_eq [Semiring F] [BEq F] [LawfulBEq F]
    (row : PolynomialRow F) (B : PolynomialMatrix F) (j : Nat) :
    ∑ k ∈ Finset.range row.size, rowGet row k * rowGet (B.getD k #[]) j =
      ∑ k ∈ Finset.range B.size, rowGet row k * rowGet (B.getD k #[]) j := by
  rw [← sum_entry_eq_of_row_le row B j (Nat.le_max_left row.size B.size),
    sum_entry_eq_of_matrix_le row B j (Nat.le_max_right row.size B.size)]

/-- The naive matrix product as an `ofFn` matrix of convolution sums. -/
theorem mulWith_eq_ofFn [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (A B : PolynomialMatrix F) :
    mulWith mulCtx A B =
      ofFn A.size (MatrixWidth B) (fun i j ↦
        ∑ k ∈ Finset.range B.size,
          rowGet (A.getD i #[]) k * rowGet (B.getD k #[]) j) := by
  refine map_eq_ofFn fun i hi ↦ ?_
  rw [rowMulMatrixWith]
  refine congrArg List.toArray (List.map_congr_left fun j hj ↦ ?_)
  rw [foldl_add_eq_sum]
  simp only [mulCtx.mul_eq_mul]
  exact sum_entry_row_size_eq (A.getD i #[]) B j

/-- Row count of the naive matrix product. -/
theorem mulWith_size [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (A B : PolynomialMatrix F) :
    (mulWith mulCtx A B).size = A.size := by
  rw [mulWith, Array.size_map]

/-- Rows of the naive matrix product. -/
theorem mulWith_getD [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (A B : PolynomialMatrix F) {i : Nat}
    (hi : i < A.size) :
    (mulWith mulCtx A B).getD i #[] = rowMulMatrixWith mulCtx (A.getD i #[]) B := by
  rw [mulWith, Array.getD_map_of_lt _ _ _ hi, getD_of_lt A #[] hi]

/-- Row list of the naive matrix product. -/
theorem matrixRows_mulWith [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (A B : PolynomialMatrix F) :
    MatrixRows (mulWith mulCtx A B) =
      (MatrixRows A).map fun row ↦ rowMulMatrixWith mulCtx row B := by
  rw [MatrixRows, MatrixRows, mulWith, Array.toList_map]

/-! ## Bounded product correctness -/

/-- The degree-capped row product equals the naive row product. -/
theorem rowMulMatrixBoundedWith_eq_rowMulMatrixWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (row : PolynomialRow F) (M : PolynomialMatrix F) :
    rowMulMatrixBoundedWith lowCtx row M =
      rowMulMatrixWith lowCtx.mulContext row M := by
  simp only [rowMulMatrixBoundedWith, rowMulMatrixWith]
  refine congrArg List.toArray (List.map_congr_left fun j hj ↦ ?_)
  rw [foldl_add_eq_sum, foldl_add_eq_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [mulLowXWith, lowCtx.mulLow_eq, lowCtx.mulContext.mul_eq_mul]
  refine truncateX_mul_of_productCoeffCap_le ?_
  rw [rowMulMatrixEntryCoeffCap]
  exact le_foldl_max
    (fun k ↦ productCoeffCap (rowGet row k) (rowGet (M.getD k #[]) j)) _ _
    (List.mem_range.mpr (Finset.mem_range.mp hk))

/-- The degree-capped matrix product equals the naive matrix product. -/
theorem mulBoundedWith_eq_mulWith [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (A B : PolynomialMatrix F) :
    mulBoundedWith lowCtx A B = mulWith lowCtx.mulContext A B := by
  rw [mulBoundedWith, mulWith]
  exact congrArg (fun f ↦ Array.map f A)
    (funext fun row ↦ rowMulMatrixBoundedWith_eq_rowMulMatrixWith lowCtx row B)

/-! ## Column-truncated naive product semantics -/

/-- Entry access for column truncation of a row. -/
theorem rowGet_rowTruncateColumns [Semiring F] [BEq F] [LawfulBEq F]
    (orders : Array Nat) (row : PolynomialRow F) (j : Nat) :
    rowGet (rowTruncateColumns orders row) j =
      truncateX (orders.getD j 0) (rowGet row j) := by
  rw [rowTruncateColumns, rowGet_list_range_map]
  split
  · rfl
  · rename_i h
    rw [rowGet_of_size_le (Nat.le_of_not_lt h), truncateX_zero]

/-- Row count of a column-truncated matrix. -/
theorem truncateColumns_size [Semiring F] [BEq F] [LawfulBEq F]
    (orders : Array Nat) (M : PolynomialMatrix F) :
    (truncateColumns orders M).size = M.size := by
  rw [truncateColumns, Array.size_map]

/-- Rows of a column-truncated matrix. -/
theorem truncateColumns_getD [Semiring F] [BEq F] [LawfulBEq F]
    (orders : Array Nat) (M : PolynomialMatrix F) {i : Nat} (hi : i < M.size) :
    (truncateColumns orders M).getD i #[] =
      rowTruncateColumns orders (M.getD i #[]) := by
  rw [truncateColumns, Array.getD_map_of_lt _ _ _ hi, getD_of_lt M #[] hi]

/-- The truncated row product is the truncation of the naive row product. -/
theorem rowMulMatrixTruncColumnWith_eq [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (orders : Array Nat) (row : PolynomialRow F)
    (M : PolynomialMatrix F) :
    rowMulMatrixTruncColumnWith lowCtx orders row M =
      rowTruncateColumns orders (rowMulMatrixWith lowCtx.mulContext row M) := by
  simp only [rowMulMatrixTruncColumnWith, rowTruncateColumns, rowMulMatrixWith_size]
  refine congrArg List.toArray (List.map_congr_left fun j hj ↦ ?_)
  rw [foldl_add_eq_sum,
    rowGet_rowMulMatrixWith lowCtx.mulContext row M (List.mem_range.mp hj),
    truncateX_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mulLowXWith, lowCtx.mulLow_eq]

/-- The column-truncated product is the truncation of the naive product. -/
theorem mulTruncColumnWith_eq [Semiring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (orders : Array Nat) (A B : PolynomialMatrix F) :
    mulTruncColumnWith lowCtx orders A B =
      truncateColumns orders (mulWith lowCtx.mulContext A B) := by
  rw [mulTruncColumnWith, truncateColumns, mulWith, Array.map_map]
  refine congrArg (fun f ↦ Array.map f A) (funext fun row ↦ ?_)
  simp only [Function.comp_apply]
  exact rowMulMatrixTruncColumnWith_eq lowCtx orders row B

/-! ## Structural `ofFn` rewrites for the block combinators -/

/-- Pointwise addition of equally shaped `ofFn` matrices. -/
theorem add_ofFn [Semiring F] [BEq F] [LawfulBEq F] (rows width : Nat)
    (f g : Nat → Nat → CPolynomial F) :
    add (ofFn rows width f) (ofFn rows width g) =
      ofFn rows width (fun i j ↦ f i j + g i j) := by
  by_cases h : rows = 0
  · subst h
    simp [add, ofFn]
  · simp only [add, ofFn_size, MatrixWidth_ofFn, if_neg h, Nat.max_self]
    refine ofFn_congr fun i hi j hj ↦ ?_
    rw [rowGet_ofFn, rowGet_ofFn, if_pos ⟨hi, hj⟩, if_pos ⟨hi, hj⟩]

/-- Pointwise subtraction of equally shaped `ofFn` matrices. -/
theorem sub_ofFn [Ring F] [BEq F] [LawfulBEq F] (rows width : Nat)
    (f g : Nat → Nat → CPolynomial F) :
    sub (ofFn rows width f) (ofFn rows width g) =
      ofFn rows width (fun i j ↦ f i j - g i j) := by
  by_cases h : rows = 0
  · subst h
    simp [sub, ofFn]
  · simp only [sub, ofFn_size, MatrixWidth_ofFn, if_neg h, Nat.max_self]
    refine ofFn_congr fun i hi j hj ↦ ?_
    rw [rowGet_ofFn, rowGet_ofFn, if_pos ⟨hi, hj⟩, if_pos ⟨hi, hj⟩]

/-- The naive product of square `ofFn` matrices. -/
theorem mulWith_ofFn_ofFn [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (n : Nat)
    (f g : Nat → Nat → CPolynomial F) :
    mulWith mulCtx (ofFn n n f) (ofFn n n g) =
      ofFn n n (fun i j ↦ ∑ k ∈ Finset.range n, f i k * g k j) := by
  rw [mulWith_eq_ofFn, ofFn_size, MatrixWidth_ofFn_square]
  refine ofFn_congr fun i hi j hj ↦ ?_
  rw [ofFn_size]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  rw [rowGet_ofFn, rowGet_ofFn, if_pos ⟨hi, hk'⟩, if_pos ⟨hk', hj⟩]

/-- Column truncation of an `ofFn` matrix. -/
theorem truncateColumns_ofFn [Semiring F] [BEq F] [LawfulBEq F] (orders : Array Nat)
    (rows width : Nat) (entry : Nat → Nat → CPolynomial F) :
    truncateColumns orders (ofFn rows width entry) =
      ofFn rows width (fun i j ↦ truncateX (orders.getD j 0) (entry i j)) := by
  rw [truncateColumns]
  have h : ∀ i, i < (ofFn rows width entry).size →
      rowTruncateColumns orders ((ofFn rows width entry).getD i #[]) =
        ((List.range width).map
          (fun j ↦ truncateX (orders.getD j 0) (entry i j))).toArray := by
    intro i hi
    rw [ofFn_size] at hi
    rw [getD_ofFn, if_pos hi, rowTruncateColumns]
    simp only [List.size_toArray, List.length_map, List.length_range]
    refine congrArg List.toArray (List.map_congr_left fun j hj ↦ ?_)
    rw [rowGet_list_range_map, if_pos (List.mem_range.mp hj)]
  rw [map_eq_ofFn h, ofFn_size]

/-! ## Strassen seven-product sum identities -/

private theorem mul_neg' [Ring F] [BEq F] [LawfulBEq F] (p q : CPolynomial F) :
    p * -q = -(p * q) :=
  eq_neg_of_add_eq_zero_left
    (by rw [← CPolynomial.mul_add, CPolynomial.neg_add_cancel, CPolynomial.mul_zero])

private theorem neg_mul' [Ring F] [BEq F] [LawfulBEq F] (p q : CPolynomial F) :
    (-p) * q = -(p * q) :=
  eq_neg_of_add_eq_zero_left
    (by rw [← CPolynomial.add_mul, CPolynomial.neg_add_cancel, CPolynomial.zero_mul])

private theorem mul_sub' [Ring F] [BEq F] [LawfulBEq F] (p q r : CPolynomial F) :
    p * (q - r) = p * q - p * r := by
  rw [sub_eq_add_neg, CPolynomial.mul_add, mul_neg', ← sub_eq_add_neg]

private theorem sub_mul' [Ring F] [BEq F] [LawfulBEq F] (p q r : CPolynomial F) :
    (p - q) * r = p * r - q * r := by
  rw [sub_eq_add_neg, CPolynomial.add_mul, neg_mul', ← sub_eq_add_neg]

private theorem strassen_sum₁₁ [Ring F] [BEq F] [LawfulBEq F] (h : Nat)
    (x₁ x₂ x₄ y₁ y₃ y₄ : Nat → CPolynomial F) :
    ((∑ k ∈ Finset.range h, (x₁ k + x₄ k) * (y₁ k + y₄ k)) +
          (∑ k ∈ Finset.range h, x₄ k * (y₃ k - y₁ k)) -
        ∑ k ∈ Finset.range h, (x₁ k + x₂ k) * y₄ k) +
        ∑ k ∈ Finset.range h, (x₂ k - x₄ k) * (y₃ k + y₄ k) =
      (∑ k ∈ Finset.range h, x₁ k * y₁ k) + ∑ k ∈ Finset.range h, x₂ k * y₃ k := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [CPolynomial.mul_add, CPolynomial.add_mul, mul_sub', sub_mul']
  abel

private theorem strassen_sum₁₂ [Ring F] [BEq F] [LawfulBEq F] (h : Nat)
    (x₁ x₂ y₂ y₄ : Nat → CPolynomial F) :
    (∑ k ∈ Finset.range h, x₁ k * (y₂ k - y₄ k)) +
        ∑ k ∈ Finset.range h, (x₁ k + x₂ k) * y₄ k =
      (∑ k ∈ Finset.range h, x₁ k * y₂ k) + ∑ k ∈ Finset.range h, x₂ k * y₄ k := by
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [CPolynomial.add_mul, mul_sub']
  abel

private theorem strassen_sum₂₁ [Ring F] [BEq F] [LawfulBEq F] (h : Nat)
    (x₃ x₄ y₁ y₃ : Nat → CPolynomial F) :
    (∑ k ∈ Finset.range h, (x₃ k + x₄ k) * y₁ k) +
        ∑ k ∈ Finset.range h, x₄ k * (y₃ k - y₁ k) =
      (∑ k ∈ Finset.range h, x₃ k * y₁ k) + ∑ k ∈ Finset.range h, x₄ k * y₃ k := by
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [CPolynomial.add_mul, mul_sub']
  abel

private theorem strassen_sum₂₂ [Ring F] [BEq F] [LawfulBEq F] (h : Nat)
    (x₁ x₃ x₄ y₁ y₂ y₄ : Nat → CPolynomial F) :
    ((∑ k ∈ Finset.range h, (x₁ k + x₄ k) * (y₁ k + y₄ k)) +
          (∑ k ∈ Finset.range h, x₁ k * (y₂ k - y₄ k)) -
        ∑ k ∈ Finset.range h, (x₃ k + x₄ k) * y₁ k) +
        ∑ k ∈ Finset.range h, (x₃ k - x₁ k) * (y₁ k + y₂ k) =
      (∑ k ∈ Finset.range h, x₃ k * y₂ k) + ∑ k ∈ Finset.range h, x₄ k * y₄ k := by
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [CPolynomial.mul_add, CPolynomial.add_mul, mul_sub', sub_mul']
  abel

/-! ## Padding step -/

private theorem multiplicationDimension_bounds [Zero F] (A B : PolynomialMatrix F) :
    A.size ≤ multiplicationDimension A B ∧ B.size ≤ multiplicationDimension A B ∧
      MatrixWidth B ≤ multiplicationDimension A B := by
  unfold multiplicationDimension
  omega

private theorem pad_step [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (A B : PolynomialMatrix F) {s : Nat}
    (hA : A.size ≤ s) (hBs : B.size ≤ s) (hBw : MatrixWidth B ≤ s) :
    trimShape A.size (MatrixWidth B) (mulWith mulCtx (padSquare s A) (padSquare s B)) =
      mulWith mulCtx A B := by
  conv_rhs => rw [mulWith_eq_ofFn]
  simp only [padSquare, trimShape, block, Nat.zero_add, mulWith_ofFn_ofFn]
  refine ofFn_congr fun i hi j hj ↦ ?_
  rw [rowGet_ofFn, if_pos ⟨lt_of_lt_of_le hi hA, lt_of_lt_of_le hj hBw⟩]
  exact sum_entry_eq_of_matrix_le (A.getD i #[]) B j hBs

private theorem trunc_pad_step [Semiring F] [BEq F] [LawfulBEq F]
    (mulCtx : CPolynomial.MulContext F) (orders : Array Nat)
    (A B : PolynomialMatrix F) {s : Nat}
    (hA : A.size ≤ s) (hBs : B.size ≤ s) (hBw : MatrixWidth B ≤ s) :
    trimShape A.size (MatrixWidth B)
        (truncateColumns (natArraySlice orders 0 s)
          (mulWith mulCtx (padSquare s A) (padSquare s B))) =
      truncateColumns orders (mulWith mulCtx A B) := by
  conv_rhs => rw [mulWith_eq_ofFn, truncateColumns_ofFn]
  simp only [padSquare, trimShape, block, Nat.zero_add, mulWith_ofFn_ofFn,
    truncateColumns_ofFn]
  refine ofFn_congr fun i hi j hj ↦ ?_
  rw [rowGet_ofFn, if_pos ⟨lt_of_lt_of_le hi hA, lt_of_lt_of_le hj hBw⟩,
    natArraySlice_getD, if_pos (lt_of_lt_of_le hj hBw), Nat.zero_add]
  exact congrArg (truncateX (orders.getD j 0))
    (sum_entry_eq_of_matrix_le (A.getD i #[]) B j hBs)

/-! ## Full Strassen correctness -/

/-- The fuel-bounded Strassen product equals the naive matrix product. -/
theorem mulStrassenWithFuel_eq_mulWith [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff fuel : Nat) (A B : PolynomialMatrix F) :
    mulStrassenWithFuel lowCtx leafCutoff fuel A B = mulWith lowCtx.mulContext A B := by
  induction fuel generalizing A B with
  | zero =>
      simp only [mulStrassenWithFuel]
      exact mulBoundedWith_eq_mulWith lowCtx A B
  | succ fuel ih =>
      simp only [mulStrassenWithFuel]
      split
      · exact mulBoundedWith_eq_mulWith lowCtx A B
      split
      · rename_i hguard
        simp only [Bool.and_eq_true, beq_iff_eq] at hguard
        obtain ⟨⟨⟨_hAw, hBs⟩, hBw⟩, heven⟩ := hguard
        simp only [ih]
        generalize hh : A.size / 2 = h
        have hAs : A.size = h + h := by omega
        conv_rhs => rw [mulWith_eq_ofFn]
        simp only [hBw, hBs, hAs]
        simp only [block, joinSquareBlocks, two_mul, Nat.zero_add, add_ofFn, sub_ofFn,
          mulWith_ofFn_ofFn]
        refine ofFn_congr fun i hi j hj ↦ ?_
        by_cases hi' : i < h <;> by_cases hj' : j < h
        · rw [if_pos hi', if_pos hj', rowGet_ofFn, if_pos ⟨hi', hj'⟩,
            Finset.sum_range_add]
          exact strassen_sum₁₁ h _ _ _ _ _ _
        · obtain ⟨j', rfl⟩ : ∃ j', j = h + j' := ⟨j - h, by omega⟩
          have hj'' : j' < h := by omega
          rw [if_pos hi', if_neg hj', Nat.add_sub_cancel_left, rowGet_ofFn,
            if_pos ⟨hi', hj''⟩, Finset.sum_range_add]
          exact strassen_sum₁₂ h _ _ _ _
        · obtain ⟨i', rfl⟩ : ∃ i', i = h + i' := ⟨i - h, by omega⟩
          have hi'' : i' < h := by omega
          rw [if_neg hi', Nat.add_sub_cancel_left, if_pos hj', rowGet_ofFn,
            if_pos ⟨hi'', hj'⟩, Finset.sum_range_add]
          exact strassen_sum₂₁ h _ _ _ _
        · obtain ⟨i', rfl⟩ : ∃ i', i = h + i' := ⟨i - h, by omega⟩
          obtain ⟨j', rfl⟩ : ∃ j', j = h + j' := ⟨j - h, by omega⟩
          have hi'' : i' < h := by omega
          have hj'' : j' < h := by omega
          rw [if_neg hi', if_neg hj', Nat.add_sub_cancel_left,
            Nat.add_sub_cancel_left, rowGet_ofFn, if_pos ⟨hi'', hj''⟩,
            Finset.sum_range_add]
          exact strassen_sum₂₂ h _ _ _ _ _ _
      · rw [ih]
        obtain ⟨hdA, hdB, hdW⟩ := multiplicationDimension_bounds A B
        have hs := le_nextPowerOfTwoAtLeast (multiplicationDimension A B)
        exact pad_step lowCtx.mulContext A B (hdA.trans hs) (hdB.trans hs)
          (hdW.trans hs)

/-- The Strassen product equals the naive matrix product. -/
theorem mulStrassenWith_eq_mulWith [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (A B : PolynomialMatrix F) :
    mulStrassenWith lowCtx leafCutoff A B = mulWith lowCtx.mulContext A B :=
  mulStrassenWithFuel_eq_mulWith lowCtx leafCutoff (multiplicationDimension A B + 1) A B

/-- Row count of the Strassen product. -/
theorem mulStrassenWith_size [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (A B : PolynomialMatrix F) :
    (mulStrassenWith lowCtx leafCutoff A B).size = A.size := by
  rw [mulStrassenWith_eq_mulWith, mulWith_size]

/-- Rows of the Strassen product are the naive row-by-matrix products. -/
theorem mulStrassenWith_getD [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (A B : PolynomialMatrix F)
    {i : Nat} (hi : i < A.size) :
    (mulStrassenWith lowCtx leafCutoff A B).getD i #[] =
      rowMulMatrixWith lowCtx.mulContext (A.getD i #[]) B := by
  rw [mulStrassenWith_eq_mulWith, mulWith_getD lowCtx.mulContext A B hi]

/-- Row list of the Strassen product. -/
theorem matrixRows_mulStrassenWith [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (A B : PolynomialMatrix F) :
    MatrixRows (mulStrassenWith lowCtx leafCutoff A B) =
      (MatrixRows A).map fun row ↦ rowMulMatrixWith lowCtx.mulContext row B := by
  rw [mulStrassenWith_eq_mulWith, matrixRows_mulWith]

/-! ## Column-truncated Strassen correctness -/

/-- The fuel-bounded column-truncated Strassen product equals the
column-truncated naive matrix product. -/
theorem mulTruncColumnStrassenWithFuel_eq_truncateColumns [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff fuel : Nat) (orders : Array Nat)
    (A B : PolynomialMatrix F) :
    mulTruncColumnStrassenWithFuel lowCtx leafCutoff fuel orders A B =
      truncateColumns orders (mulWith lowCtx.mulContext A B) := by
  induction fuel generalizing orders A B with
  | zero =>
      simp only [mulTruncColumnStrassenWithFuel]
      exact mulTruncColumnWith_eq lowCtx orders A B
  | succ fuel ih =>
      simp only [mulTruncColumnStrassenWithFuel]
      split
      · exact mulTruncColumnWith_eq lowCtx orders A B
      split
      · rename_i hguard
        simp only [Bool.and_eq_true, beq_iff_eq] at hguard
        obtain ⟨⟨⟨_hAw, hBs⟩, hBw⟩, heven⟩ := hguard
        simp only [ih]
        generalize hh : A.size / 2 = h
        have hAs : A.size = h + h := by omega
        conv_rhs => rw [mulWith_eq_ofFn, truncateColumns_ofFn]
        simp only [hBw, hBs, hAs]
        simp only [block, joinSquareBlocks, two_mul, Nat.zero_add, add_ofFn, sub_ofFn,
          mulWith_ofFn_ofFn, truncateColumns_ofFn]
        refine ofFn_congr fun i hi j hj ↦ ?_
        by_cases hi' : i < h <;> by_cases hj' : j < h
        · rw [if_pos hi', if_pos hj', rowGet_ofFn, if_pos ⟨hi', hj'⟩]
          simp only [natArraySlice_getD, maxNatArrays_getD, if_pos hj', Nat.zero_add]
          have hmin₁ : min (orders.getD j 0)
              (max (orders.getD j 0) (orders.getD (h + j) 0)) = orders.getD j 0 :=
            Nat.min_eq_left (Nat.le_max_left _ _)
          simp only [truncateX_add, truncateX_sub, truncateX_truncateX, hmin₁,
            Nat.min_self]
          simp only [← truncateX_add, ← truncateX_sub]
          rw [Finset.sum_range_add]
          exact congrArg (truncateX (orders.getD j 0)) (strassen_sum₁₁ h _ _ _ _ _ _)
        · obtain ⟨j', rfl⟩ : ∃ j', j = h + j' := ⟨j - h, by omega⟩
          have hj'' : j' < h := by omega
          rw [if_pos hi', if_neg hj', Nat.add_sub_cancel_left, rowGet_ofFn,
            if_pos ⟨hi', hj''⟩]
          simp only [natArraySlice_getD, maxNatArrays_getD, if_pos hj'', Nat.zero_add]
          have hmin₁ : min (orders.getD (h + j') 0)
              (max (orders.getD j' 0) (orders.getD (h + j') 0)) =
                orders.getD (h + j') 0 :=
            Nat.min_eq_left (Nat.le_max_right _ _)
          simp only [truncateX_add, truncateX_truncateX, hmin₁, Nat.min_self]
          simp only [← truncateX_add]
          rw [Finset.sum_range_add]
          exact congrArg (truncateX (orders.getD (h + j') 0))
            (strassen_sum₁₂ h _ _ _ _)
        · obtain ⟨i', rfl⟩ : ∃ i', i = h + i' := ⟨i - h, by omega⟩
          have hi'' : i' < h := by omega
          rw [if_neg hi', Nat.add_sub_cancel_left, if_pos hj', rowGet_ofFn,
            if_pos ⟨hi'', hj'⟩]
          simp only [natArraySlice_getD, maxNatArrays_getD, if_pos hj', Nat.zero_add]
          have hmin₁ : min (orders.getD j 0)
              (max (orders.getD j 0) (orders.getD (h + j) 0)) = orders.getD j 0 :=
            Nat.min_eq_left (Nat.le_max_left _ _)
          simp only [truncateX_add, truncateX_truncateX, hmin₁, Nat.min_self]
          simp only [← truncateX_add]
          rw [Finset.sum_range_add]
          exact congrArg (truncateX (orders.getD j 0)) (strassen_sum₂₁ h _ _ _ _)
        · obtain ⟨i', rfl⟩ : ∃ i', i = h + i' := ⟨i - h, by omega⟩
          obtain ⟨j', rfl⟩ : ∃ j', j = h + j' := ⟨j - h, by omega⟩
          have hi'' : i' < h := by omega
          have hj'' : j' < h := by omega
          rw [if_neg hi', if_neg hj', Nat.add_sub_cancel_left,
            Nat.add_sub_cancel_left, rowGet_ofFn, if_pos ⟨hi'', hj''⟩]
          simp only [natArraySlice_getD, maxNatArrays_getD, if_pos hj'', Nat.zero_add]
          have hmin₁ : min (orders.getD (h + j') 0)
              (max (orders.getD j' 0) (orders.getD (h + j') 0)) =
                orders.getD (h + j') 0 :=
            Nat.min_eq_left (Nat.le_max_right _ _)
          simp only [truncateX_add, truncateX_sub, truncateX_truncateX, hmin₁,
            Nat.min_self]
          simp only [← truncateX_add, ← truncateX_sub]
          rw [Finset.sum_range_add]
          exact congrArg (truncateX (orders.getD (h + j') 0))
            (strassen_sum₂₂ h _ _ _ _ _ _)
      · rw [ih]
        obtain ⟨hdA, hdB, hdW⟩ := multiplicationDimension_bounds A B
        have hs := le_nextPowerOfTwoAtLeast (multiplicationDimension A B)
        exact trunc_pad_step lowCtx.mulContext orders A B (hdA.trans hs)
          (hdB.trans hs) (hdW.trans hs)

/-- The column-truncated Strassen product equals the column-truncated naive
matrix product. -/
theorem mulTruncColumnStrassenWith_eq_truncateColumns [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (orders : Array Nat)
    (A B : PolynomialMatrix F) :
    mulTruncColumnStrassenWith lowCtx leafCutoff orders A B =
      truncateColumns orders (mulWith lowCtx.mulContext A B) :=
  mulTruncColumnStrassenWithFuel_eq_truncateColumns lowCtx leafCutoff
    (multiplicationDimension A B + 1) orders A B

/-- Row count of the column-truncated Strassen product. -/
theorem mulTruncColumnStrassenWith_size [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (orders : Array Nat)
    (A B : PolynomialMatrix F) :
    (mulTruncColumnStrassenWith lowCtx leafCutoff orders A B).size = A.size := by
  rw [mulTruncColumnStrassenWith_eq_truncateColumns, truncateColumns_size,
    mulWith_size]

/-- Entries of the column-truncated Strassen product are the order-truncated
naive product entries. -/
theorem mulTruncColumnStrassenWith_entry [Ring F] [BEq F] [LawfulBEq F]
    (lowCtx : MulLowContext F) (leafCutoff : Nat) (orders : Array Nat)
    (A B : PolynomialMatrix F) {i : Nat} (hi : i < A.size) (j : Nat) :
    rowGet ((mulTruncColumnStrassenWith lowCtx leafCutoff orders A B).getD i #[]) j =
      truncateX (orders.getD j 0)
        (rowGet (rowMulMatrixWith lowCtx.mulContext (A.getD i #[]) B) j) := by
  rw [mulTruncColumnStrassenWith_eq_truncateColumns,
    truncateColumns_getD orders _ (by rw [mulWith_size]; exact hi),
    mulWith_getD lowCtx.mulContext A B hi, rowGet_rowTruncateColumns]

end PolynomialMatrix

end CompPoly
