/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.ModularEquation.Basic
import CompPoly.Univariate.DivisionCorrectness

/-!
# Filtered Modular Solver Completeness

Completeness/minimality of the filtered PM-basis modular solver: every
nonzero in-width solution of a monic diagonal modular equation is dominated
by a returned row, via the certified verification window.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Completeness/minimality of the filtered PM-basis modular solver

The argument routes every modular solution through the certified verification
window.  A nonzero in-width solution row of shifted degree `e ≤ bound` lifts
to an exact row of the reduced exact-nullspace problem whose expanded shifted
degree is at most `e + bound + 1`.  The PM-basis minimality contract yields a
basis row of dominated expanded degree, the verification orders force its
column products to vanish exactly, and its principal truncation is therefore a
modular solution of shifted degree at most `e` surviving both filters.
Solutions above the verification window are handled either by the adaptive
rows themselves or by falling back to the always-available solution
`e_p * prod(moduli)`, which fits the saturated window. -/

section CompleteMinimal

/-! ### Generic access and summation helpers -/

private theorem me_getD_list_range_map {α : Type*} (g : Nat → α) (n j : Nat) (d : α) :
    (((List.range n).map g).toArray).getD j d = if j < n then g j else d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  by_cases hj : j < n
  · rw [List.getElem?_range hj, Option.map_some, Option.getD_some, if_pos hj]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj), Option.map_none,
      Option.getD_none, if_neg hj]

private theorem me_getD_append_left {α : Type*} {A B : Array α} {i : Nat} (d : α)
    (hi : i < A.size) :
    (A ++ B).getD i d = A.getD i d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left hi]

private theorem me_getD_append_right {α : Type*} {A B : Array α} {i : Nat} (d : α)
    (hi : A.size ≤ i) :
    (A ++ B).getD i d = B.getD (i - A.size) d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_right hi]

private theorem me_getD_replicate {α : Type*} {n : Nat} (a d : α) {i : Nat}
    (hi : i < n) :
    (Array.replicate n a).getD i d = a := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hi, Option.getD_some]

/-- In-bounds `getD` values are list members. -/
theorem me_getD_mem_toList {α : Type*} {xs : Array α} {i : Nat} (d : α)
    (hi : i < xs.size) : xs.getD i d ∈ xs.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  exact Array.getElem_mem_toList hi

omit [BEq F] [LawfulBEq F] in
private theorem me_matrixWidth_eq_getD (M : PolynomialMatrix F) :
    MatrixWidth M = (M.getD 0 #[]).size := by
  unfold MatrixWidth
  rw [Array.getD_eq_getD_getElem?]
  cases M[0]? <;> rfl

private theorem me_sum_range_add {M : Type*} [AddCommMonoid M] (f : Nat → M)
    (m n : Nat) :
    ∑ k ∈ Finset.range (m + n), f k =
      (∑ k ∈ Finset.range m, f k) + ∑ k ∈ Finset.range n, f (m + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = (m + n) + 1 from rfl, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, add_assoc]

private theorem me_toPoly_sum (f : Nat → CPolynomial F) (n : Nat) :
    (∑ k ∈ Finset.range n, f k).toPoly = ∑ k ∈ Finset.range n, (f k).toPoly := by
  induction n with
  | zero => simp [CPolynomial.toPoly_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, CPolynomial.toPoly_add, ih]

/-- Column entries of a row-by-matrix product as `toPoly` sums over any index
range covering the row.  The matrix multiplication context is irrelevant to
the value. -/
private theorem me_rowMul_toPoly (mulCtx : CPolynomial.MulContext F)
    (row : PolynomialRow F) (M : PolynomialMatrix F) {j n : Nat}
    (hj : j < MatrixWidth M) (hn : row.size ≤ n) :
    (rowGet (rowMulMatrixWith mulCtx row M) j).toPoly =
      ∑ k ∈ Finset.range n,
        (rowGet row k).toPoly * (rowGet (M.getD k #[]) j).toPoly := by
  rw [rowGet_rowMulMatrixWith mulCtx row M hj, me_toPoly_sum]
  rw [show ∑ k ∈ Finset.range row.size,
        (rowGet row k * rowGet (M.getD k #[]) j).toPoly =
      ∑ k ∈ Finset.range row.size,
        (rowGet row k).toPoly * (rowGet (M.getD k #[]) j).toPoly from
    Finset.sum_congr rfl fun k _ ↦ CPolynomial.toPoly_mul _ _]
  refine Finset.sum_subset
    (fun x hx ↦ Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) hn))
    fun k _hk hknot ↦ ?_
  have hk : row.size ≤ k := by simpa using hknot
  rw [rowGet_of_size_le hk, CPolynomial.toPoly_zero, zero_mul]

omit [BEq F] [LawfulBEq F] in
private theorem me_natDegree_sum_le {n : Nat} (f : Nat → Polynomial F) {D : Nat}
    (h : ∀ k, k < n → (f k).natDegree ≤ D) :
    (∑ k ∈ Finset.range n, f k).natDegree ≤ D := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      exact max_le (ih fun k hk ↦ h k (by omega)) (h n (by omega))

omit [BEq F] [LawfulBEq F] in
private theorem me_eq_zero_of_X_pow_dvd_of_natDegree_lt {p : Polynomial F} {n : Nat}
    (hdvd : (Polynomial.X : Polynomial F) ^ n ∣ p) (hdeg : p.natDegree < n) :
    p = 0 := by
  by_contra hp
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp
  rw [Polynomial.natDegree_X_pow] at hle
  omega

/-! ### Zero-row and shifted-degree helpers -/

private theorem me_rowIsZero_false_of_entry {row : PolynomialRow F} {j : Nat}
    (hj : j < row.size) (hne : rowGet row j ≠ 0) :
    rowIsZero row = false := by
  cases hzero : rowIsZero row with
  | false => rfl
  | true =>
      exfalso
      refine hne (rowIsZero_iff.mp hzero (rowGet row j) ?_)
      rw [rowGet]
      exact me_getD_mem_toList 0 hj

private theorem me_rowGet_eq_zero_of_rowIsZero {row : PolynomialRow F}
    (h : rowIsZero row = true) (k : Nat) : rowGet row k = 0 := by
  rcases Nat.lt_or_ge k row.size with hk | hk
  · refine rowIsZero_iff.mp h (rowGet row k) ?_
    rw [rowGet]
    exact me_getD_mem_toList 0 hk
  · exact rowGet_of_size_le hk

omit [LawfulBEq F] in
private theorem me_rowIsZero_of_forall {row : PolynomialRow F}
    (h : ∀ j, j < row.size → rowGet row j = 0) :
    RowIsZero row := by
  intro p hp
  rcases List.getElem_of_mem hp with ⟨j, hj, hget⟩
  have hj' : j < row.size := by simpa using hj
  have hzero := h j hj'
  rw [rowGet, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj',
    Option.getD_some] at hzero
  rw [← hget]
  simpa [Array.getElem_toList] using hzero

/-- Nonzero rows have a shifted degree. -/
theorem me_rowShiftedDegree_isSome {row : PolynomialRow F} {shift : Array Nat}
    (hnz : rowIsZero row = false) :
    ∃ d, rowShiftedDegree? row shift = some d := by
  cases hdeg : rowShiftedDegree? row shift with
  | none =>
      rw [rowIsZero_iff.mpr (rowShiftedDegree?_eq_none_iff.mp hdeg)] at hnz
      simp at hnz
  | some d => exact ⟨d, rfl⟩

private theorem me_shiftedEntryDegree_eq {row : PolynomialRow F} {shift : Array Nat}
    {j : Nat} (hne : rowGet row j ≠ 0) :
    shiftedEntryDegree? row shift j =
      some ((rowGet row j).natDegree + shift.getD j 0) := by
  rw [shiftedEntryDegree?, if_neg (by simpa using hne)]

private theorem me_shiftedEntryDegree_some {row : PolynomialRow F} {shift : Array Nat}
    {j e : Nat} (h : shiftedEntryDegree? row shift j = some e) :
    rowGet row j ≠ 0 ∧ e = (rowGet row j).natDegree + shift.getD j 0 := by
  by_cases hne : rowGet row j = 0
  · rw [shiftedEntryDegree?] at h
    simp [hne] at h
  · rw [me_shiftedEntryDegree_eq hne] at h
    exact ⟨hne, (Option.some.inj h).symm⟩

private theorem me_entry_le_of_rowShiftedDegree {row : PolynomialRow F}
    {shift : Array Nat} {d j : Nat}
    (hdeg : rowShiftedDegree? row shift = some d) (hne : rowGet row j ≠ 0) :
    (rowGet row j).natDegree + shift.getD j 0 ≤ d := by
  have hj : j < row.size := by
    by_contra hj
    exact hne (rowGet_of_size_le (Nat.le_of_not_lt hj))
  exact shiftedEntryDegree?_le_of_rowShiftedDegree?_eq_some hdeg hj
    (me_shiftedEntryDegree_eq hne)

private theorem me_rowShiftedDegree_attained {row : PolynomialRow F}
    {shift : Array Nat} {d : Nat} (hdeg : rowShiftedDegree? row shift = some d) :
    ∃ j, j < row.size ∧ rowGet row j ≠ 0 ∧
      d = (rowGet row j).natDegree + shift.getD j 0 := by
  rcases exists_shiftedEntryDegree?_eq_of_rowShiftedDegree?_eq_some hdeg with
    ⟨j, hj, hentry⟩
  rcases me_shiftedEntryDegree_some hentry with ⟨hne, he⟩
  exact ⟨j, hj, hne, he⟩

/-! ### `maxShiftDegree` and modulus-product bounds -/

private theorem me_foldl_max_init_le (g : Nat → Nat) :
    ∀ (l : List Nat) (acc : Nat), acc ≤ l.foldl (fun a i ↦ max a (g i)) acc := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl _
  | cons x l ih =>
      intro acc
      exact le_trans (Nat.le_max_left acc (g x)) (ih (max acc (g x)))

private theorem me_le_foldl_max (g : Nat → Nat) :
    ∀ (l : List Nat) (acc : Nat) (x : Nat), x ∈ l →
      g x ≤ l.foldl (fun a i ↦ max a (g i)) acc := by
  intro l
  induction l with
  | nil => intro acc x hx; cases hx
  | cons y l ih =>
      intro acc x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (Nat.le_max_right acc (g x)) (me_foldl_max_init_le g l _)
      · exact ih _ x hx

private theorem me_shift_le_maxShiftDegree (shift : Array Nat) (j : Nat) :
    shift.getD j 0 ≤ maxShiftDegree shift := by
  rw [maxShiftDegree]
  rcases Nat.lt_or_ge j shift.size with hj | hj
  · exact me_le_foldl_max (fun i ↦ shift.getD i 0) (List.range shift.size) 0 j
      (List.mem_range.mpr hj)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hj]
    exact Nat.zero_le _

/-- Product of all moduli, used as the universal fallback solution entry. -/
private def me_moduliProduct (moduli : Array (CPolynomial F)) : CPolynomial F :=
  moduli.foldl (fun acc m ↦ acc * m) 1

private theorem me_foldl_mul_toPoly :
    ∀ (l : List (CPolynomial F)) (acc : CPolynomial F),
      (l.foldl (fun a m ↦ a * m) acc).toPoly =
        acc.toPoly * (l.map CPolynomial.toPoly).prod := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons m l ih =>
      intro acc
      rw [List.foldl_cons, ih, CPolynomial.toPoly_mul, List.map_cons, List.prod_cons]
      ring

private theorem me_moduliProduct_toPoly (moduli : Array (CPolynomial F)) :
    (me_moduliProduct moduli).toPoly = (moduli.toList.map CPolynomial.toPoly).prod := by
  rw [me_moduliProduct, ← Array.foldl_toList, me_foldl_mul_toPoly,
    CPolynomial.toPoly_one, one_mul]

private theorem me_moduliProduct_dvd {moduli : Array (CPolynomial F)} {b : Nat}
    (hb : b < moduli.size) :
    (moduli.getD b 0).toPoly ∣ (me_moduliProduct moduli).toPoly := by
  rw [me_moduliProduct_toPoly]
  exact List.dvd_prod (List.mem_map.mpr ⟨moduli.getD b 0, me_getD_mem_toList 0 hb, rfl⟩)

omit [BEq F] [LawfulBEq F] in
private theorem me_list_prod_ne_zero :
    ∀ (l : List (Polynomial F)), (∀ p ∈ l, p ≠ 0) → l.prod ≠ 0
  | [], _ => by simp
  | p :: l, h => by
      rw [List.prod_cons]
      exact mul_ne_zero (h p (by simp))
        (me_list_prod_ne_zero l fun q hq ↦ h q (by simp [hq]))

private theorem me_moduliProduct_ne_zero {moduli : Array (CPolynomial F)}
    (hmonic : ∀ b, b < moduli.size → (moduli.getD b 0).monic) :
    me_moduliProduct moduli ≠ 0 := by
  intro hzero
  have htoPoly : (me_moduliProduct moduli).toPoly = 0 := by
    rw [hzero, CPolynomial.toPoly_zero]
  rw [me_moduliProduct_toPoly] at htoPoly
  refine me_list_prod_ne_zero (moduli.toList.map CPolynomial.toPoly) ?_ htoPoly
  intro p hp
  rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
  rcases List.getElem_of_mem hq with ⟨b, hb, hget⟩
  have hb' : b < moduli.size := by simpa using hb
  have hqd : moduli.getD b 0 = q := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb', Option.getD_some]
    simpa [Array.getElem_toList] using hget
  have hmq := hmonic b hb'
  rw [hqd] at hmq
  exact Polynomial.Monic.ne_zero ((CPolynomial.monic_toPoly_iff q).mp hmq)

omit [BEq F] [LawfulBEq F] in
private theorem me_foldl_add_mono :
    ∀ (l : List (CPolynomial F)) (a b : Nat), a ≤ b →
      l.foldl (fun acc m ↦ acc + m.natDegree) a ≤
        l.foldl (fun acc m ↦ acc + m.natDegree) b := by
  intro l
  induction l with
  | nil => intro a b h; exact h
  | cons m l ih => intro a b h; exact ih _ _ (Nat.add_le_add_right h _)

private theorem me_foldl_mul_natDegree_le :
    ∀ (l : List (CPolynomial F)) (acc : CPolynomial F),
      (l.foldl (fun a m ↦ a * m) acc).toPoly.natDegree ≤
        l.foldl (fun a m ↦ a + m.natDegree) acc.toPoly.natDegree := by
  intro l
  induction l with
  | nil => intro acc; exact Nat.le_refl _
  | cons m l ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons]
      refine le_trans (ih (acc * m)) (me_foldl_add_mono l _ _ ?_)
      rw [CPolynomial.toPoly_mul]
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [CPolynomial.natDegree_toPoly]

private theorem me_moduliProduct_natDegree_le (moduli : Array (CPolynomial F)) :
    (me_moduliProduct moduli).toPoly.natDegree ≤ modulusDegreeMass moduli := by
  rw [me_moduliProduct, modulusDegreeMass, ← Array.foldl_toList, ← Array.foldl_toList]
  have h := me_foldl_mul_natDegree_le moduli.toList 1
  simpa [CPolynomial.toPoly_one] using h

/-! ### Modular-reduction semantics (local copies of the GS bridge lemmas) -/

private theorem me_modByMonicWith_toPoly (modCtx : CPolynomial.ModContext F)
    {p M : CPolynomial F} (hM : Polynomial.Monic M.toPoly) :
    (modByMonicWith modCtx p M).toPoly = p.toPoly %ₘ M.toPoly := by
  have hMne : M ≠ 0 := by
    intro hzero
    have : M.toPoly = 0 := by rw [hzero, CPolynomial.toPoly_zero]
    exact hM.ne_zero this
  rw [modByMonicWith, if_neg (by simpa using hMne), modCtx.modByMonic_eq_modByMonic]
  exact CPolynomial.modByMonic_toPoly_eq_modByMonic p M
    ((CPolynomial.monic_toPoly_iff M).mpr hM)

private theorem me_dvd_modByMonicWith_sub (modCtx : CPolynomial.ModContext F)
    {p M : CPolynomial F} (hM : Polynomial.Monic M.toPoly) :
    M.toPoly ∣ (modByMonicWith modCtx p M).toPoly - p.toPoly := by
  rw [me_modByMonicWith_toPoly modCtx hM]
  refine ⟨-(p.toPoly /ₘ M.toPoly), ?_⟩
  calc p.toPoly %ₘ M.toPoly - p.toPoly
      = p.toPoly %ₘ M.toPoly -
          (p.toPoly %ₘ M.toPoly + M.toPoly * (p.toPoly /ₘ M.toPoly)) := by
        rw [Polynomial.modByMonic_add_div p.toPoly M.toPoly]
    _ = M.toPoly * -(p.toPoly /ₘ M.toPoly) := by ring

private theorem me_modByMonicWith_eq_zero_iff_dvd (modCtx : CPolynomial.ModContext F)
    {p M : CPolynomial F} (hM : Polynomial.Monic M.toPoly) :
    modByMonicWith modCtx p M = 0 ↔ M.toPoly ∣ p.toPoly := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hM, ← me_modByMonicWith_toPoly modCtx hM]
  constructor
  · intro h
    rw [h, CPolynomial.toPoly_zero]
  · intro h
    exact (CPolynomial.toPoly_eq_zero_iff _).mp h

private theorem me_divByMonic_mul_eq {p M : CPolynomial F} (hM : M.monic)
    (hdvd : M.toPoly ∣ p.toPoly) :
    (p.divByMonic M).toPoly * M.toPoly = p.toPoly := by
  have hMonic : Polynomial.Monic M.toPoly := (CPolynomial.monic_toPoly_iff M).mp hM
  have hmod : p.toPoly %ₘ M.toPoly = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hMonic).mpr hdvd
  have hdecomp := Polynomial.modByMonic_add_div p.toPoly M.toPoly
  rw [hmod, zero_add] at hdecomp
  rw [CPolynomial.divByMonic_toPoly_eq_divByMonic p M hM, mul_comm]
  exact hdecomp

/-- The executable modular row predicate, columnwise. -/
private theorem me_rowSatisfies_iff (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (row : PolynomialRow F)
    (M : PolynomialMatrix F) (moduli : Array (CPolynomial F)) :
    rowSatisfiesModularBool mulCtx modCtx row M moduli = true ↔
      ∀ b, b < moduli.size →
        modByMonicWith modCtx (rowGet (rowMulMatrixWith mulCtx row M) b)
          (moduli.getD b 0) = 0 := by
  rw [rowSatisfiesModularBool, rowMulMatrixModDiagonalWith, rowModDiagonalWith,
    Array.all_eq_true]
  constructor
  · intro h b hb
    have hb' : b < (((List.range moduli.size).map fun j ↦
        modByMonicWith modCtx (rowGet (rowMulMatrixWith mulCtx row M) j)
          (moduli.getD j 0)).toArray).size := by
      simpa using hb
    have := h b hb'
    simpa using this
  · intro h b hb
    have hb' : b < moduli.size := by simpa using hb
    simpa using h b hb'

/-! ### Membership plumbing for the pipeline filters -/

/-- Filtered modular-solution rows come from the input rows. -/
theorem me_filterModularSolutionRows_subset
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {equation : ModularEquation F} {rows : PolynomialMatrix F}
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (filterModularSolutionRows mulCtx modCtx equation rows)) :
    row ∈ MatrixRows rows := by
  rw [MatrixRows, filterModularSolutionRows] at hrow
  rw [MatrixRows]
  have hmem : row ∈ rows ∧ rowIsZero row = false ∧
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true := by
    simpa using hrow
  simpa using hmem.1

private theorem me_mem_filterModularSolutionRows
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {equation : ModularEquation F} {rows : PolynomialMatrix F}
    {row : PolynomialRow F}
    (hmem : row ∈ MatrixRows rows) (hnz : rowIsZero row = false)
    (hsat : rowSatisfiesModularBool mulCtx modCtx row equation.matrix
      equation.moduli = true) :
    row ∈ MatrixRows (filterModularSolutionRows mulCtx modCtx equation rows) := by
  rw [MatrixRows] at hmem
  rw [MatrixRows, filterModularSolutionRows]
  have h : row ∈ rows ∧ rowIsZero row = false ∧
      rowSatisfiesModularBool mulCtx modCtx row equation.matrix equation.moduli = true :=
    ⟨by simpa using hmem, hnz, hsat⟩
  simpa using h

omit [LawfulBEq F] in
private theorem me_mem_compactNonzeroRows {rows : PolynomialMatrix F}
    {row : PolynomialRow F} (hmem : row ∈ MatrixRows rows)
    (hnz : rowIsZero row = false) :
    row ∈ MatrixRows (compactNonzeroRows rows) := by
  rw [MatrixRows] at hmem
  rw [MatrixRows, compactNonzeroRows]
  have h : row ∈ rows ∧ rowIsZero row = false := ⟨by simpa using hmem, hnz⟩
  simpa using h

omit [BEq F] [LawfulBEq F] in
private theorem me_mem_principalSolutionRows {sW : Nat} {basis : PolynomialMatrix F}
    {row : PolynomialRow F} (hmem : row ∈ MatrixRows basis) :
    ((List.range sW).map fun j ↦ rowGet row j).toArray ∈
      MatrixRows (principalSolutionRows sW basis) := by
  rw [MatrixRows, principalSolutionRows, Array.toList_map]
  exact List.mem_map.mpr ⟨row, hmem, rfl⟩

omit [BEq F] [LawfulBEq F] in
/-- Principal solution rows keep the basis row width. -/
theorem me_principalSolutionRows_width {sW : Nat}
    {basis : PolynomialMatrix F} {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (principalSolutionRows sW basis)) :
    row.size = sW := by
  rw [MatrixRows, principalSolutionRows, Array.toList_map] at hrow
  rcases List.mem_map.mp hrow with ⟨r, _hr, rfl⟩
  simp

/-! ### Width discipline of the adaptive pipeline -/

private theorem me_solutionBasisWithPlan_width
    {modCtx : CPolynomial.ModContext F} {pmCtx : PMBasisContext F}
    {equation : ModularEquation F} {shift : Array Nat}
    {plan : PartialLinearizationPlan} {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows
      (solutionBasisWithPlanViaPMBasis modCtx pmCtx equation shift plan)) :
    row.size = plan.solutionWidth := by
  simp only [solutionBasisWithPlanViaPMBasis] at hrow
  have hsub := compactNonzeroRows_subset hrow
  rw [MatrixRows, compressChunkedPrincipalRows, Array.toList_map] at hsub
  rcases List.mem_map.mp hsub with ⟨r, _hr, rfl⟩
  simp [compressChunkedPrincipalRow]

private theorem me_adaptiveRound_width
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {state : AdaptiveSolveState F}
    (hstate : ∀ r ∈ MatrixRows state.filtered, r.size = equation.solutionWidth) :
    ∀ r ∈ MatrixRows
        (adaptiveSolutionRound mulCtx modCtx pmCtx equation shift state).filtered,
      r.size = equation.solutionWidth := by
  intro r hr
  simp only [adaptiveSolutionRound, MatrixRows, Array.toList_append,
    List.mem_append] at hr
  rcases hr with hold | hnew
  · exact hstate r hold
  · have hsub := me_filterModularSolutionRows_subset hnew
    have hsize := me_solutionBasisWithPlan_width hsub
    rw [hsize]
    simp [partialLinearizationPlanFromPivotDegrees]

private theorem me_adaptiveLoop_width
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {degreeBound? : Option Nat} {cap : Nat} :
    ∀ (fuel : Nat) (state : AdaptiveSolveState F),
      (∀ r ∈ MatrixRows state.filtered, r.size = equation.solutionWidth) →
      ∀ r ∈ MatrixRows
          (adaptiveSolutionLoop mulCtx modCtx pmCtx equation shift degreeBound?
            cap fuel state).filtered,
        r.size = equation.solutionWidth := by
  intro fuel
  induction fuel with
  | zero =>
      intro state hstate r hr
      exact hstate r hr
  | succ fuel ih =>
      intro state hstate r hr
      rw [adaptiveSolutionLoop] at hr
      have hnext := me_adaptiveRound_width (mulCtx := mulCtx) (modCtx := modCtx)
        (pmCtx := pmCtx) (shift := shift) (state := state) hstate
      split at hr
      · exact hnext r hr
      · split at hr
        · exact hnext r hr
        · split at hr
          · exact hnext r hr
          · dsimp only [] at hr
            split at hr
            · exact hnext r hr
            · refine ih _ ?_ r hr
              intro r' hr'
              exact hnext r' hr'

/-- Every adaptive solution-basis row has the linearized width. -/
theorem me_adaptiveBasis_width
    {mulCtx : CPolynomial.MulContext F} {modCtx : CPolynomial.ModContext F}
    {pmCtx : PMBasisContext F} {equation : ModularEquation F}
    {shift : Array Nat} {degreeBound? : Option Nat} :
    ∀ r ∈ MatrixRows
        (adaptiveSolutionBasis mulCtx modCtx pmCtx equation shift
          degreeBound?).filtered,
      r.size = equation.solutionWidth := by
  rw [adaptiveSolutionBasis]
  exact me_adaptiveLoop_width _ _ (by intro r hr; simp [MatrixRows] at hr)

/-! ### The fallback solution `e_p * prod(moduli)` -/

/-- Structure of the fallback row `e_p * prod(moduli)`. -/
theorem me_prodRow_facts (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (equation : ModularEquation F)
    (shift : Array Nat) {p : Nat}
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hp : p < equation.solutionWidth) :
    ∃ (prow : PolynomialRow F) (e : Nat),
      rowSatisfiesModularBool mulCtx modCtx prow equation.matrix
        equation.moduli = true ∧
      rowIsZero prow = false ∧
      prow.size = equation.solutionWidth ∧
      rowShiftedDegree? prow shift = some e ∧
      e ≤ pivotWindowCap equation + maxShiftDegree shift := by
  classical
  set sW := equation.solutionWidth with hsW
  set prod := me_moduliProduct equation.moduli with hprodDef
  set prow : PolynomialRow F :=
    ((List.range sW).map fun j ↦ if j = p then prod else 0).toArray with hprow
  have hsize : prow.size = sW := by simp [hprow]
  have hget : ∀ j, rowGet prow j =
      if j < sW then (if j = p then prod else 0) else 0 := by
    intro j
    rw [hprow, rowGet, me_getD_list_range_map]
  have hprodne : prod ≠ 0 := me_moduliProduct_ne_zero hmonic
  have hnz : rowIsZero prow = false := by
    refine me_rowIsZero_false_of_entry (j := p) (by omega) ?_
    rw [hget, if_pos hp, if_pos rfl]
    exact hprodne
  have hsat : rowSatisfiesModularBool mulCtx modCtx prow equation.matrix
      equation.moduli = true := by
    rw [me_rowSatisfies_iff]
    intro b hb
    rw [me_modByMonicWith_eq_zero_iff_dvd modCtx
      ((CPolynomial.monic_toPoly_iff _).mp (hmonic b hb))]
    rw [me_rowMul_toPoly mulCtx prow equation.matrix (lt_of_lt_of_le hb hcols)
      (le_of_eq hsize)]
    refine Finset.dvd_sum fun k hk ↦ ?_
    rw [hget, if_pos (Finset.mem_range.mp hk)]
    by_cases hkp : k = p
    · rw [if_pos hkp]
      exact Dvd.dvd.mul_right (me_moduliProduct_dvd hb) _
    · rw [if_neg hkp, CPolynomial.toPoly_zero, zero_mul]
      exact dvd_zero _
  obtain ⟨e, he⟩ := me_rowShiftedDegree_isSome (shift := shift) hnz
  refine ⟨prow, e, hsat, hnz, hsize, he, ?_⟩
  obtain ⟨j, hjsize, hjne, hjeq⟩ := me_rowShiftedDegree_attained he
  rw [hsize] at hjsize
  have hjp : j = p := by
    by_contra hne
    refine hjne ?_
    rw [hget, if_pos hjsize, if_neg hne]
  rw [hget, if_pos hjsize, if_pos hjp] at hjeq
  have hdeg : prod.natDegree ≤ pivotWindowCap equation := by
    rw [CPolynomial.natDegree_toPoly]
    exact me_moduliProduct_natDegree_le equation.moduli
  have hshiftle := me_shift_le_maxShiftDegree shift j
  omega

/-! ### The certified verification window -/

/-- Certified-window domination: any nonzero in-width modular solution row
whose shifted degree fits inside the verification window `bound` is
degree-dominated by a row of the filtered verification basis. -/
theorem me_verification_dominates
    (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (pmCtx : PMBasisContext F) (equation : ModularEquation F)
    (shift : Array Nat) (bound : Nat) {rowStar : PolynomialRow F} {e : Nat}
    (hmonic : ∀ b, b < equation.moduli.size → (equation.moduli.getD b 0).monic)
    (hcols : equation.moduli.size ≤ MatrixWidth equation.matrix)
    (hshift : shift.size = equation.solutionWidth)
    (hpos : 0 < equation.solutionWidth)
    (hsat : rowSatisfiesModularBool mulCtx modCtx rowStar equation.matrix
      equation.moduli = true)
    (hnz : rowIsZero rowStar = false)
    (hwidth : rowStar.size ≤ equation.solutionWidth)
    (hdeg : rowShiftedDegree? rowStar shift = some e)
    (hebound : e ≤ bound) :
    ∃ basisRow degree,
      basisRow ∈ MatrixRows (filterModularSolutionRows mulCtx modCtx equation
        (compactNonzeroRows (principalSolutionRows equation.solutionWidth
          (pmCtx.basis (fullWindowExactNullspaceProblem modCtx equation bound)
            (exactNullspaceShift shift equation.modularWidth bound))))) ∧
      rowShiftedDegree? basisRow shift = some degree ∧ degree ≤ e := by
  classical
  rw [show equation.modularWidth = equation.moduli.size from rfl]
  set sW := equation.solutionWidth with hsWdef
  set mW := equation.moduli.size with hmWdef
  -- The reduced principal block and the lift matrix.
  set Fred : PolynomialMatrix F := ofFn sW mW
    (fun i j ↦ modByMonicWith modCtx (rowGet (equation.matrix.getD i #[]) j)
      (equation.moduli.getD j 0)) with hFred
  set liftM : PolynomialMatrix F := Fred ++ negativeDiagonalRows equation.moduli
    with hliftM
  have hFredSize : Fred.size = sW := ofFn_size _ _ _
  have hnegSize : (negativeDiagonalRows equation.moduli).size = mW := ofFn_size _ _ _
  have hliftSize : liftM.size = sW + mW := by
    rw [hliftM, Array.size_append, hFredSize, hnegSize]
  have hFredWidth : MatrixWidth Fred = mW := by
    rw [hFred, MatrixWidth_ofFn, if_neg (by omega)]
  have hFredEntry : ∀ {k b : Nat}, k < sW → b < mW →
      rowGet (Fred.getD k #[]) b =
        modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
          (equation.moduli.getD b 0) := by
    intro k b hk hb
    rw [hFred, rowGet_ofFn, if_pos ⟨hk, hb⟩]
  have hliftWidth : MatrixWidth liftM = mW := by
    rw [me_matrixWidth_eq_getD, hliftM, me_getD_append_left _ (by omega), hFred,
      getD_ofFn, if_pos (by omega)]
    simp
  have hliftRows : ∀ r ∈ MatrixRows liftM, r.size = mW := by
    intro r hr
    rw [MatrixRows, hliftM, Array.toList_append, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
      have hi' : i < Fred.size := by simpa using hi
      have hgetD : Fred.getD i #[] = r := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
        simpa [Array.getElem_toList] using hget
      rw [← hgetD, hFred, getD_ofFn, if_pos (by omega)]
      simp
    · rcases List.getElem_of_mem hr with ⟨i, hi, hget⟩
      have hi' : i < (negativeDiagonalRows equation.moduli).size := by simpa using hi
      have hgetD : (negativeDiagonalRows equation.moduli).getD i #[] = r := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
        simpa [Array.getElem_toList] using hget
      rw [← hgetD, negativeDiagonalRows, getD_ofFn, if_pos (by omega)]
      simp only [List.size_toArray, List.length_map, List.length_range]
      omega
  have hwf : WellFormed liftM := by
    intro r hr
    rw [hliftWidth]
    exact hliftRows r hr
  have hliftL : ∀ {k b : Nat}, k < sW → b < mW →
      rowGet (liftM.getD k #[]) b =
        modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
          (equation.moduli.getD b 0) := by
    intro k b hk hb
    rw [hliftM, me_getD_append_left _ (by omega)]
    exact hFredEntry hk hb
  have hliftR : ∀ {c b : Nat}, c < mW → b < mW →
      rowGet (liftM.getD (sW + c) #[]) b =
        (if c == b then -(equation.moduli.getD c 0) else 0) := by
    intro c b hc hb
    rw [hliftM, me_getD_append_right _ (by omega)]
    rw [show sW + c - Fred.size = c from by omega]
    rw [negativeDiagonalRows, rowGet_ofFn, if_pos ⟨by omega, by omega⟩]
  -- Monicity facts.
  have hMon : ∀ {b : Nat}, b < mW →
      Polynomial.Monic ((equation.moduli.getD b 0).toPoly) :=
    fun {b} hb ↦ (CPolynomial.monic_toPoly_iff _).mp (hmonic b hb)
  have hMne : ∀ {b : Nat}, b < mW → ((equation.moduli.getD b 0).toPoly) ≠ 0 :=
    fun {b} hb ↦ (hMon hb).ne_zero
  -- The verification problem and shift.
  set P := fullWindowExactNullspaceProblem modCtx equation bound with hP
  have hPmatrix : P.matrix = liftM := rfl
  have hPordersSize : P.orders.size = mW := by
    rw [hP, fullWindowExactNullspaceProblem]
    simp only [Array.size_map]
    omega
  have hPorders : ∀ {b : Nat}, b < mW →
      P.orders.getD b 0 = (equation.moduli.getD b 0).natDegree + bound + 2 := by
    intro b hb
    show (equation.moduli.map fun m ↦ m.natDegree + bound + 2).getD b 0 = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega), Option.map_some, Option.getD_some,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some]
  set eShift := exactNullspaceShift shift equation.moduli.size bound with heShift
  have heShiftL : ∀ {k : Nat}, k < sW →
      eShift.getD k 0 = shift.getD k 0 + bound + 1 := by
    intro k hk
    rw [heShift, exactNullspaceShift, liftedPrincipalShift, principalShiftOffset,
      me_getD_append_left _ (by simp [hshift]; omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_eq_getElem (by omega : k < shift.size), Option.map_some,
      Option.getD_some, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega : k < shift.size), Option.getD_some]
    omega
  have heShiftR : ∀ {c : Nat}, c < mW →
      eShift.getD (sW + c) 0 = bound := by
    intro c hc
    rw [heShift, exactNullspaceShift, quotientShift,
      me_getD_append_right _ (by simp [liftedPrincipalShift, hshift])]
    rw [show sW + c - (liftedPrincipalShift shift bound).size = c from by
      simp [liftedPrincipalShift, hshift]]
    exact me_getD_replicate _ _ hc
  -- Divisibility of the original products.
  have hdvdF : ∀ {b : Nat}, b < mW →
      (equation.moduli.getD b 0).toPoly ∣
        ∑ k ∈ Finset.range sW, (rowGet rowStar k).toPoly *
          (rowGet (equation.matrix.getD k #[]) b).toPoly := by
    intro b hb
    have hsat' := (me_rowSatisfies_iff mulCtx modCtx rowStar equation.matrix
      equation.moduli).mp hsat b hb
    have hdvd := (me_modByMonicWith_eq_zero_iff_dvd modCtx (hMon hb)).mp hsat'
    rwa [me_rowMul_toPoly mulCtx rowStar equation.matrix
      (lt_of_lt_of_le hb hcols) hwidth] at hdvd
  -- The reduced products and their exact quotients.
  set prodE := fun b ↦ rowGet (rowMulMatrixWith mulCtx rowStar Fred) b with hprodE
  have hprodE_toPoly : ∀ {b : Nat}, b < mW →
      (prodE b).toPoly = ∑ k ∈ Finset.range sW, (rowGet rowStar k).toPoly *
        (rowGet (Fred.getD k #[]) b).toPoly := by
    intro b hb
    rw [hprodE]
    exact me_rowMul_toPoly mulCtx rowStar Fred (by omega) hwidth
  have hdvdRed : ∀ {b : Nat}, b < mW →
      (equation.moduli.getD b 0).toPoly ∣ (prodE b).toPoly := by
    intro b hb
    have hdiff : (equation.moduli.getD b 0).toPoly ∣
        (prodE b).toPoly -
          ∑ k ∈ Finset.range sW, (rowGet rowStar k).toPoly *
            (rowGet (equation.matrix.getD k #[]) b).toPoly := by
      rw [hprodE_toPoly hb, ← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun k hk ↦ ?_
      have hk' : k < sW := Finset.mem_range.mp hk
      rw [hFredEntry hk' hb]
      have hsub := me_dvd_modByMonicWith_sub modCtx
        (p := rowGet (equation.matrix.getD k #[]) b) (hMon hb)
      have hfac : (rowGet rowStar k).toPoly *
          (modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
            (equation.moduli.getD b 0)).toPoly -
          (rowGet rowStar k).toPoly *
            (rowGet (equation.matrix.getD k #[]) b).toPoly =
          (rowGet rowStar k).toPoly *
            ((modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) b)
              (equation.moduli.getD b 0)).toPoly -
              (rowGet (equation.matrix.getD k #[]) b).toPoly) := by
        ring
      rw [hfac]
      exact Dvd.dvd.mul_left hsub _
    have hsum := dvd_add hdiff (hdvdF hb)
    simpa using hsum
  obtain ⟨quot, hquot⟩ : ∃ q : Nat → CPolynomial F,
      ∀ b, q b = (prodE b).divByMonic (equation.moduli.getD b 0) :=
    ⟨fun b ↦ (prodE b).divByMonic (equation.moduli.getD b 0), fun _ ↦ rfl⟩
  have hquotExact : ∀ {b : Nat}, b < mW →
      (quot b).toPoly * (equation.moduli.getD b 0).toPoly = (prodE b).toPoly := by
    intro b hb
    rw [hquot b]
    exact me_divByMonic_mul_eq (hmonic b hb) (hdvdRed hb)
  -- Degree bounds on the witness entries and quotients.
  have hrowStarEntry : ∀ {k : Nat}, rowGet rowStar k ≠ 0 →
      (rowGet rowStar k).toPoly.natDegree + shift.getD k 0 ≤ e := by
    intro k hk
    have h := me_entry_le_of_rowShiftedDegree hdeg hk
    rwa [CPolynomial.natDegree_toPoly] at h
  have hFredZero : ∀ {k b : Nat}, k < sW → b < mW →
      (equation.moduli.getD b 0).natDegree = 0 →
      (rowGet (Fred.getD k #[]) b).toPoly = 0 := by
    intro k b hk hb hMdeg
    rw [hFredEntry hk hb, me_modByMonicWith_toPoly modCtx (hMon hb)]
    have hMone : (equation.moduli.getD b 0).toPoly = 1 := by
      refine (Polynomial.Monic.natDegree_eq_zero (hMon hb)).mp ?_
      rwa [CPolynomial.natDegree_toPoly] at hMdeg
    rw [hMone, Polynomial.modByMonic_one]
  have hFredDegLt : ∀ {k b : Nat}, k < sW → b < mW →
      (rowGet (Fred.getD k #[]) b).toPoly ≠ 0 →
      (rowGet (Fred.getD k #[]) b).toPoly.natDegree <
        (equation.moduli.getD b 0).natDegree := by
    intro k b hk hb hne
    rw [hFredEntry hk hb, me_modByMonicWith_toPoly modCtx (hMon hb)] at hne ⊢
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_lt_natDegree hne
      (Polynomial.degree_modByMonic_lt _ (hMon hb))
  have hquotDeg : ∀ {b : Nat}, b < mW → quot b ≠ 0 →
      (quot b).toPoly.natDegree ≤ e := by
    intro b hb hqz
    have hqpoly : (quot b).toPoly ≠ 0 :=
      fun h ↦ hqz ((CPolynomial.toPoly_eq_zero_iff _).mp h)
    by_cases hMdeg : (equation.moduli.getD b 0).natDegree = 0
    · exfalso
      have hzero : (prodE b).toPoly = 0 := by
        rw [hprodE_toPoly hb]
        refine Finset.sum_eq_zero fun k hk ↦ ?_
        rw [hFredZero (Finset.mem_range.mp hk) hb hMdeg, mul_zero]
      have hmul := hquotExact hb
      rw [hzero] at hmul
      rcases mul_eq_zero.mp hmul with h | h
      · exact hqpoly h
      · exact hMne hb h
    · have h2 : (prodE b).toPoly.natDegree =
          (quot b).toPoly.natDegree + (equation.moduli.getD b 0).natDegree := by
        rw [← hquotExact hb, CPolynomial.natDegree_toPoly (equation.moduli.getD b 0)]
        exact Polynomial.natDegree_mul hqpoly (hMne hb)
      have h1 : (prodE b).toPoly.natDegree ≤
          e + (equation.moduli.getD b 0).natDegree - 1 := by
        rw [hprodE_toPoly hb]
        refine me_natDegree_sum_le _ fun k hk ↦ ?_
        by_cases hz : (rowGet rowStar k).toPoly = 0
        · rw [hz, zero_mul, Polynomial.natDegree_zero]
          exact Nat.zero_le _
        by_cases hzF : (rowGet (Fred.getD k #[]) b).toPoly = 0
        · rw [hzF, mul_zero, Polynomial.natDegree_zero]
          exact Nat.zero_le _
        · have hne : rowGet rowStar k ≠ 0 :=
            fun h ↦ hz (by rw [h, CPolynomial.toPoly_zero])
          have ha := hrowStarEntry hne
          have hbnd := hFredDegLt hk hb hzF
          refine le_trans Polynomial.natDegree_mul_le ?_
          omega
      omega
  -- The lifted exact-nullspace row.
  set lifted : PolynomialRow F := ((List.range (sW + mW)).map
    (fun k ↦ if k < sW then rowGet rowStar k else quot (k - sW))).toArray
    with hlifted
  have hliftedSize : lifted.size = sW + mW := by simp [hlifted]
  have hliftedGet : ∀ k, rowGet lifted k =
      if k < sW + mW then (if k < sW then rowGet rowStar k else quot (k - sW))
      else 0 := by
    intro k
    rw [hlifted, rowGet, me_getD_list_range_map]
  have hliftedL : ∀ {k : Nat}, k < sW → rowGet lifted k = rowGet rowStar k := by
    intro k hk
    rw [hliftedGet, if_pos (by omega), if_pos hk]
  have hliftedR : ∀ {c : Nat}, c < mW → rowGet lifted (sW + c) = quot c := by
    intro c hc
    rw [hliftedGet, if_pos (by omega), if_neg (by omega)]
    rw [show sW + c - sW = c from by omega]
  obtain ⟨j0, hj0, hj0ne⟩ := exists_nonzero_entry_of_rowIsZero_false hnz
  have hj0sW : j0 < sW := by omega
  have hnzL : rowIsZero lifted = false := by
    refine me_rowIsZero_false_of_entry (j := j0) (by omega) ?_
    rw [hliftedL hj0sW]
    exact hj0ne
  -- The lifted row is an exact solution of the verification problem.
  have happroxL : ∀ j, j < P.orders.size →
      truncateX (P.orders.getD j 0)
        (rowGet (rowMulMatrixWith pmCtx.runtime.mulContext lifted P.matrix) j) = 0 := by
    intro j hj
    have hjm : j < mW := by omega
    have hzero : rowGet (rowMulMatrixWith pmCtx.runtime.mulContext lifted
        P.matrix) j = 0 := by
      refine (CPolynomial.toPoly_eq_zero_iff _).mp ?_
      rw [hPmatrix]
      rw [me_rowMul_toPoly pmCtx.runtime.mulContext lifted liftM (by omega)
        (le_of_eq hliftedSize)]
      rw [me_sum_range_add (fun k ↦ (rowGet lifted k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly) sW mW]
      have hfirst : ∑ k ∈ Finset.range sW, (rowGet lifted k).toPoly *
          (rowGet (liftM.getD k #[]) j).toPoly = (prodE j).toPoly := by
        rw [hprodE_toPoly hjm]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk' : k < sW := Finset.mem_range.mp hk
        rw [hliftedL hk', hliftM, me_getD_append_left _ (by omega)]
      have hsecond : ∑ k ∈ Finset.range mW, (rowGet lifted (sW + k)).toPoly *
          (rowGet (liftM.getD (sW + k) #[]) j).toPoly =
          -((quot j).toPoly * (equation.moduli.getD j 0).toPoly) := by
        rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm) ?_]
        · rw [hliftedR hjm, hliftR hjm hjm, if_pos (by simp),
            CPolynomial.toPoly_neg]
          ring
        · intro c hc hcj
          rw [hliftR (Finset.mem_range.mp hc) hjm, if_neg (by simpa using hcj),
            CPolynomial.toPoly_zero, mul_zero]
      rw [hfirst, hsecond, hquotExact hjm]
      ring
    rw [hzero]
    exact truncateX_zero _
  -- Apply the PM-basis minimality contract to the lifted row.
  obtain ⟨bRow, Db, hbMem, hbSize, hbDeg, hbDom⟩ :=
    pmCtx.complete_minimal P eShift lifted (by rw [hPmatrix]; omega)
      (by rw [hPmatrix]; exact hwf) happroxL hnzL
      (by rw [hPmatrix]; omega)
  have hbSizeLe : bRow.size ≤ sW + mW := by
    rw [hPmatrix, hliftSize] at hbSize
    exact hbSize
  -- The lifted row stays inside the expanded window.
  obtain ⟨Dl, hDl⟩ := me_rowShiftedDegree_isSome (shift := eShift) hnzL
  have hDlle : Dl ≤ e + bound + 1 := by
    obtain ⟨j, hjsize, hjne, hjeq⟩ := me_rowShiftedDegree_attained hDl
    rw [hliftedSize] at hjsize
    rcases Nat.lt_or_ge j sW with hjL | hjR
    · rw [heShiftL hjL, hliftedL hjL] at hjeq
      have hne' : rowGet rowStar j ≠ 0 := by rwa [hliftedL hjL] at hjne
      have h := me_entry_le_of_rowShiftedDegree hdeg hne'
      rw [CPolynomial.natDegree_toPoly] at h
      rw [CPolynomial.natDegree_toPoly] at hjeq
      omega
    · have hcm : j - sW < mW := by omega
      rw [show j = sW + (j - sW) from by omega] at hjne hjeq
      rw [hliftedR hcm] at hjne hjeq
      rw [heShiftR hcm] at hjeq
      have hqd := hquotDeg hcm hjne
      rw [CPolynomial.natDegree_toPoly] at hjeq
      omega
  have hDb : Db ≤ e + bound + 1 := le_trans (hbDom Dl hDl) hDlle
  -- Entry bounds on the dominated basis row.
  have hbEntryL : ∀ {k : Nat}, k < sW → rowGet bRow k ≠ 0 →
      (rowGet bRow k).toPoly.natDegree + shift.getD k 0 ≤ e := by
    intro k hk hne
    have h := me_entry_le_of_rowShiftedDegree hbDeg hne
    rw [heShiftL hk] at h
    rw [CPolynomial.natDegree_toPoly] at h
    omega
  have hbEntryR : ∀ {c : Nat}, c < mW → rowGet bRow (sW + c) ≠ 0 →
      (rowGet bRow (sW + c)).toPoly.natDegree ≤ e + 1 := by
    intro c hc hne
    have h := me_entry_le_of_rowShiftedDegree hbDeg hne
    rw [heShiftR hc] at h
    rw [CPolynomial.natDegree_toPoly] at h
    omega
  -- The verification orders force exact column products for the basis row.
  have hsound := pmCtx.sound P eShift bRow hbMem
  have hTzero : ∀ {j : Nat}, j < mW →
      ∑ k ∈ Finset.range (sW + mW), (rowGet bRow k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly = 0 := by
    intro j hjm
    have hX := hsound j (by omega)
    rw [truncateX_eq_zero_iff_X_pow_dvd] at hX
    rw [hPmatrix] at hX
    rw [me_rowMul_toPoly pmCtx.runtime.mulContext bRow liftM (by omega)
      hbSizeLe] at hX
    rw [hPorders hjm] at hX
    refine me_eq_zero_of_X_pow_dvd_of_natDegree_lt hX ?_
    have hdegT : (∑ k ∈ Finset.range (sW + mW), (rowGet bRow k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly).natDegree ≤
        (equation.moduli.getD j 0).natDegree + bound + 1 := by
      refine me_natDegree_sum_le _ fun k hk ↦ ?_
      by_cases hz : (rowGet bRow k).toPoly = 0
      · rw [hz, zero_mul, Polynomial.natDegree_zero]
        exact Nat.zero_le _
      have hne : rowGet bRow k ≠ 0 :=
        fun h ↦ hz (by rw [h, CPolynomial.toPoly_zero])
      rcases Nat.lt_or_ge k sW with hkL | hkR
      · by_cases hzF : (rowGet (liftM.getD k #[]) j).toPoly = 0
        · rw [hzF, mul_zero, Polynomial.natDegree_zero]
          exact Nat.zero_le _
        · have hzF' : (rowGet (Fred.getD k #[]) j).toPoly ≠ 0 := by
            rwa [hliftM, me_getD_append_left _ (by omega)] at hzF
          have hMdeg1 : 1 ≤ (equation.moduli.getD j 0).natDegree := by
            by_contra hcon
            exact hzF' (hFredZero hkL hjm (by omega))
          have hFle := hFredDegLt hkL hjm hzF'
          have ha := hbEntryL hkL hne
          have hentry : rowGet (liftM.getD k #[]) j = rowGet (Fred.getD k #[]) j := by
            rw [hliftM, me_getD_append_left _ (by omega)]
          rw [hentry]
          refine le_trans Polynomial.natDegree_mul_le ?_
          omega
      · have hcm : k - sW < mW := by omega
        rw [show k = sW + (k - sW) from by omega, hliftR hcm hjm]
        by_cases hcj : k - sW = j
        · rw [if_pos (by simpa using hcj)]
          have hb1 : (rowGet bRow (sW + j)).toPoly.natDegree ≤ e + 1 := by
            refine hbEntryR hjm ?_
            rwa [show sW + j = k from by omega]
          refine le_trans Polynomial.natDegree_mul_le ?_
          rw [hcj, CPolynomial.toPoly_neg, Polynomial.natDegree_neg,
            ← CPolynomial.natDegree_toPoly (equation.moduli.getD j 0)]
          omega
        · rw [if_neg (by simpa using hcj), CPolynomial.toPoly_zero, mul_zero,
            Polynomial.natDegree_zero]
          exact Nat.zero_le _
    omega
  have hbProd : ∀ {j : Nat}, j < mW →
      ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (Fred.getD k #[]) j).toPoly =
      (rowGet bRow (sW + j)).toPoly * (equation.moduli.getD j 0).toPoly := by
    intro j hjm
    have h0 := hTzero hjm
    rw [me_sum_range_add (fun k ↦ (rowGet bRow k).toPoly *
      (rowGet (liftM.getD k #[]) j).toPoly) sW mW] at h0
    have hfirst : ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (liftM.getD k #[]) j).toPoly =
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (Fred.getD k #[]) j).toPoly := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk' : k < sW := Finset.mem_range.mp hk
      rw [hliftM, me_getD_append_left _ (by omega)]
    have hsecond : ∑ k ∈ Finset.range mW, (rowGet bRow (sW + k)).toPoly *
        (rowGet (liftM.getD (sW + k) #[]) j).toPoly =
        -((rowGet bRow (sW + j)).toPoly * (equation.moduli.getD j 0).toPoly) := by
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjm) ?_]
      · rw [hliftR hjm hjm, if_pos (by simp), CPolynomial.toPoly_neg]
        ring
      · intro c hc hcj
        rw [hliftR (Finset.mem_range.mp hc) hjm, if_neg (by simpa using hcj),
          CPolynomial.toPoly_zero, mul_zero]
    rw [hfirst, hsecond] at h0
    have h0' : ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (Fred.getD k #[]) j).toPoly -
        (rowGet bRow (sW + j)).toPoly * (equation.moduli.getD j 0).toPoly = 0 := by
      rw [sub_eq_add_neg]
      exact h0
    exact sub_eq_zero.mp h0'
  -- The principal truncation of the basis row.
  set bPrin : PolynomialRow F :=
    ((List.range sW).map fun j ↦ rowGet bRow j).toArray with hbPrin
  have hbPrinSize : bPrin.size = sW := by simp [hbPrin]
  have hbPrinGet : ∀ k, rowGet bPrin k = if k < sW then rowGet bRow k else 0 := by
    intro k
    rw [hbPrin, rowGet, me_getD_list_range_map]
  have hbDvdF : ∀ {j : Nat}, j < mW → (equation.moduli.getD j 0).toPoly ∣
      ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
        (rowGet (equation.matrix.getD k #[]) j).toPoly := by
    intro j hjm
    have hsumdvd : (equation.moduli.getD j 0).toPoly ∣
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (Fred.getD k #[]) j).toPoly := by
      rw [hbProd hjm]
      exact dvd_mul_left _ _
    have hdiff : (equation.moduli.getD j 0).toPoly ∣
        (∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (Fred.getD k #[]) j).toPoly) -
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (equation.matrix.getD k #[]) j).toPoly := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.dvd_sum fun k hk ↦ ?_
      rw [hFredEntry (Finset.mem_range.mp hk) hjm]
      have hsub := me_dvd_modByMonicWith_sub modCtx
        (p := rowGet (equation.matrix.getD k #[]) j) (hMon hjm)
      have hfac : (rowGet bRow k).toPoly *
          (modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) j)
            (equation.moduli.getD j 0)).toPoly -
          (rowGet bRow k).toPoly *
            (rowGet (equation.matrix.getD k #[]) j).toPoly =
          (rowGet bRow k).toPoly *
            ((modByMonicWith modCtx (rowGet (equation.matrix.getD k #[]) j)
              (equation.moduli.getD j 0)).toPoly -
              (rowGet (equation.matrix.getD k #[]) j).toPoly) := by
        ring
      rw [hfac]
      exact Dvd.dvd.mul_left hsub _
    have h := dvd_sub hsumdvd hdiff
    simpa using h
  have hbPrinSat : rowSatisfiesModularBool mulCtx modCtx bPrin equation.matrix
      equation.moduli = true := by
    rw [me_rowSatisfies_iff]
    intro b hb
    rw [me_modByMonicWith_eq_zero_iff_dvd modCtx (hMon hb)]
    rw [me_rowMul_toPoly mulCtx bPrin equation.matrix (lt_of_lt_of_le hb hcols)
      (le_of_eq hbPrinSize)]
    have hcong : ∑ k ∈ Finset.range sW, (rowGet bPrin k).toPoly *
        (rowGet (equation.matrix.getD k #[]) b).toPoly =
        ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
          (rowGet (equation.matrix.getD k #[]) b).toPoly := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hbPrinGet, if_pos (Finset.mem_range.mp hk)]
    rw [hcong]
    exact hbDvdF hb
  have hbPrinNz : rowIsZero bPrin = false := by
    cases hzero : rowIsZero bPrin with
    | false => rfl
    | true =>
        exfalso
        have hallP : ∀ k, k < sW → rowGet bRow k = 0 := by
          intro k hk
          have h := me_rowGet_eq_zero_of_rowIsZero hzero k
          rwa [hbPrinGet, if_pos hk] at h
        have hallQ : ∀ c, c < mW → rowGet bRow (sW + c) = 0 := by
          intro c hc
          have hprod := hbProd hc
          have hzeroSum : ∑ k ∈ Finset.range sW, (rowGet bRow k).toPoly *
              (rowGet (Fred.getD k #[]) c).toPoly = 0 :=
            Finset.sum_eq_zero fun k hk ↦ by
              rw [hallP k (Finset.mem_range.mp hk), CPolynomial.toPoly_zero,
                zero_mul]
          rw [hzeroSum] at hprod
          rcases mul_eq_zero.mp hprod.symm with h | h
          · exact (CPolynomial.toPoly_eq_zero_iff _).mp h
          · exact absurd h (hMne hc)
        have hzRow : RowIsZero bRow := by
          refine me_rowIsZero_of_forall fun k hk ↦ ?_
          rcases Nat.lt_or_ge k sW with h1 | h1
          · exact hallP k h1
          · have hcm : k - sW < mW := by omega
            rw [show k = sW + (k - sW) from by omega]
            exact hallQ _ hcm
        have hnone := (rowShiftedDegree?_eq_none_iff
          (row := bRow) (shift := eShift)).mpr hzRow
        rw [hbDeg] at hnone
        cases hnone
  have hbPrinMemF : bPrin ∈ MatrixRows (filterModularSolutionRows mulCtx modCtx
      equation (compactNonzeroRows (principalSolutionRows sW
        (pmCtx.basis P eShift)))) := by
    refine me_mem_filterModularSolutionRows ?_ hbPrinNz hbPrinSat
    refine me_mem_compactNonzeroRows ?_ hbPrinNz
    exact me_mem_principalSolutionRows hbMem
  obtain ⟨degB, hdegB⟩ := me_rowShiftedDegree_isSome (shift := shift) hbPrinNz
  have hdegBle : degB ≤ e := by
    obtain ⟨j, hjsize, hjne, hjeq⟩ := me_rowShiftedDegree_attained hdegB
    rw [hbPrinSize] at hjsize
    have hjne' : rowGet bRow j ≠ 0 := by rwa [hbPrinGet, if_pos hjsize] at hjne
    have h := hbEntryL hjsize hjne'
    rw [hbPrinGet, if_pos hjsize] at hjeq
    rw [CPolynomial.natDegree_toPoly] at hjeq
    omega
  exact ⟨bPrin, degB, hbPrinMemF, hdegB, hdegBle⟩

end CompleteMinimal

end Approximant

end PolynomialMatrix

end CompPoly
