/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.XAdicSoundness
import CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeafScalar

/-!
# Kernel-Leaf Basis Soundness

Every row of the kernel-leaf basis satisfies the X-adic approximant
conditions and has the principal row width: kernel vectors reconstruct to
solutions, and the reduction, completion, and compaction steps preserve
soundness.
-/

namespace CompPoly

namespace PolynomialMatrix

namespace Approximant

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## Kernel-leaf basis soundness -/

/-- Coefficient-shift row scaling preserves the row size. -/
theorem rowScaleCoeffX_size (c : F) (d : Nat) (row : PolynomialRow F) :
    (rowScaleCoeffX c d row).size = row.size := by
  simp [rowScaleCoeffX]

private theorem insertKernelLeafPivotRowWithFuel_invariant
    (Q : PolynomialRow F → Prop)
    (hclosed : ∀ (target reducer : PolynomialRow F) (shift : Array Nat),
      Q target → Q reducer → Q (cancelKernelLeafLeadingTerm target reducer shift)) :
    ∀ (fuel : Nat) (pivots : Array (Option (PolynomialRow F)))
      (shift : Array Nat) (row : PolynomialRow F),
      (∀ p r, pivots.getD p none = some r → Q r) → Q row →
      ∀ p r,
        (insertKernelLeafPivotRowWithFuel fuel pivots shift row).getD p none =
          some r → Q r := by
  intro fuel
  induction fuel with
  | zero =>
      intro pivots shift row hpivots _hrow p r hget
      exact hpivots p r hget
  | succ fuel ih =>
      intro pivots shift row hpivots hrow p r hget
      rw [insertKernelLeafPivotRowWithFuel] at hget
      have hset : ∀ (position : Nat) (newRow : PolynomialRow F),
          Q newRow →
          ∀ p' r',
            (pivots.setIfInBounds position (some newRow)).getD p' none = some r' →
            Q r' := by
        intro position newRow hnew p' r' hget'
        by_cases hpos : p' = position ∧ position < pivots.size
        · rcases hpos with ⟨hp, hlt⟩
          subst hp
          rw [Array.getD_eq_getD_getElem?,
            Array.getElem?_setIfInBounds_self_of_lt hlt, Option.getD_some] at hget'
          cases hget'
          exact hnew
        · rcases Nat.lt_or_ge p' pivots.size with hplt | hpge
          · have hne : p' ≠ position := fun hcontra ↦ hpos ⟨hcontra, hcontra ▸ hplt⟩
            rw [Array.getD_eq_getD_getElem?,
              Array.getElem?_setIfInBounds_ne (by omega)] at hget'
            exact hpivots p' r' (by rw [Array.getD_eq_getD_getElem?]; exact hget')
          · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none
              (by simpa using hpge)] at hget'
            cases hget'
      cases hterm : rowShiftedLeadingTerm? row shift with
      | none =>
          simp only [hterm] at hget
          exact hpivots p r hget
      | some target =>
          simp only [hterm] at hget
          cases hpivot : pivots.getD target.position none with
          | none =>
              simp only [hpivot] at hget
              exact hset target.position row hrow p r hget
          | some pivot =>
              simp only [hpivot] at hget
              cases hpterm : rowShiftedLeadingTerm? pivot shift with
              | none =>
                  simp only [hpterm] at hget
                  exact hset target.position row hrow p r hget
              | some reducer =>
                  simp only [hpterm] at hget
                  have hpivotrow : Q pivot := hpivots target.position pivot hpivot
                  split at hget
                  · exact ih (pivots.setIfInBounds target.position (some row)) shift
                      (cancelKernelLeafLeadingTerm pivot row shift)
                      (fun p' r' hget' ↦ hset target.position row hrow p' r' hget')
                      (hclosed _ _ _ hpivotrow hrow) p r hget
                  · exact ih pivots shift
                      (cancelKernelLeafLeadingTerm row pivot shift) hpivots
                      (hclosed _ _ _ hrow hpivotrow) p r hget

omit [BEq F] [LawfulBEq F] in
/-- Any predicate holding for all stored pivot rows holds for all extracted rows. -/
theorem pivotRows_invariant (Q : PolynomialRow F → Prop)
    {pivots : Array (Option (PolynomialRow F))}
    (hpivots : ∀ p r, pivots.getD p none = some r → Q r)
    {row : PolynomialRow F} (hrow : row ∈ MatrixRows (pivotRows pivots)) :
    Q row := by
  rw [MatrixRows, pivotRows, List.toList_toArray] at hrow
  rcases List.mem_filterMap.mp hrow with ⟨entry, hentry, hid⟩
  rcases List.getElem_of_mem hentry with ⟨p, hp, hget⟩
  refine hpivots p row ?_
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hp),
    Option.getD_some]
  rw [show pivots[p] = pivots.toList[p] from by rw [Array.getElem_toList], hget]
  exact hid

/-- Any predicate closed under leading-term cancellation is preserved by the
pivot-table reduction. -/
theorem reduceKernelLeafRowsByPivots_invariant (Q : PolynomialRow F → Prop)
    (hclosed : ∀ (target reducer : PolynomialRow F) (shift : Array Nat),
      Q target → Q reducer → Q (cancelKernelLeafLeadingTerm target reducer shift))
    {rows : PolynomialMatrix F} (shift : Array Nat)
    (hrows : ∀ row ∈ MatrixRows rows, Q row)
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (reduceKernelLeafRowsByPivots rows shift)) :
    Q row := by
  rw [reduceKernelLeafRowsByPivots] at hrow
  refine pivotRows_invariant Q ?_ hrow
  have hfold : ∀ (l : List (PolynomialRow F))
      (pivots : Array (Option (PolynomialRow F))),
      (∀ r ∈ l, Q r) →
      (∀ p r, pivots.getD p none = some r → Q r) →
      ∀ p r,
        (l.foldl (fun pivots row ↦
            insertKernelLeafPivotRowWithFuel (reduceKernelLeafFuel rows shift)
              pivots shift row) pivots).getD p none = some r → Q r := by
    intro l
    induction l with
    | nil =>
        intro pivots _hl hpivots p r hget
        exact hpivots p r hget
    | cons head tail ih =>
        intro pivots hl hpivots p r hget
        rw [List.foldl_cons] at hget
        refine ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem head hr)) ?_ p r hget
        intro p' r' hget'
        exact insertKernelLeafPivotRowWithFuel_invariant Q hclosed
          (reduceKernelLeafFuel rows shift) pivots shift head hpivots
          (hl head List.mem_cons_self) p' r' hget'
  rw [← Array.foldl_toList]
  refine hfold rows.toList _ (fun r hr ↦ hrows r hr) ?_
  intro p r hget
  rw [Array.getD_eq_getD_getElem?] at hget
  rcases Nat.lt_or_ge p (Array.replicate (MatrixWidth rows)
      (none : Option (PolynomialRow F))).size with hp | hp
  · rw [Array.getElem?_eq_getElem hp, Option.getD_some] at hget
    rw [Array.getElem_replicate] at hget
    cases hget
  · rw [Array.getElem?_eq_none hp] at hget
    cases hget

omit [BEq F] [LawfulBEq F] in
/-- A row of `rows.push row` is either a row of `rows` or `row` itself. -/
theorem mem_matrixRows_push {rows : PolynomialMatrix F}
    {row r : PolynomialRow F} (hr : r ∈ MatrixRows (rows.push row)) :
    r ∈ MatrixRows rows ∨ r = row := by
  rw [MatrixRows, Array.toList_push, List.mem_append] at hr
  rcases hr with hr | hr
  · exact Or.inl hr
  · exact Or.inr (by simpa using hr)

/-- Any predicate closed under leading-term cancellation is preserved by the
incremental pivot reduction. -/
theorem reduceKernelLeafRowsIncremental_invariant
    (Q : PolynomialRow F → Prop)
    (hclosed : ∀ (target reducer : PolynomialRow F) (shift : Array Nat),
      Q target → Q reducer → Q (cancelKernelLeafLeadingTerm target reducer shift))
    {rows : PolynomialMatrix F} (shift : Array Nat)
    (hrows : ∀ row ∈ MatrixRows rows, Q row)
    {row : PolynomialRow F}
    (hrow : row ∈ MatrixRows (reduceKernelLeafRowsIncremental rows shift)) :
    Q row := by
  rw [reduceKernelLeafRowsIncremental, ← Array.foldl_toList] at hrow
  have hfold : ∀ (l : List (PolynomialRow F)) (basis : PolynomialMatrix F),
      (∀ r ∈ l, Q r) →
      (∀ r ∈ MatrixRows basis, Q r) →
      ∀ r ∈ MatrixRows (l.foldl
        (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis),
        Q r := by
    intro l
    induction l with
    | nil =>
        intro basis _hl hbasis r hr
        exact hbasis r hr
    | cons head tail ih =>
        intro basis hl hbasis r hr
        rw [List.foldl_cons] at hr
        refine ih _ (fun x hx ↦ hl x (List.mem_cons_of_mem head hx)) ?_ r hr
        intro x hx
        rw [insertKernelLeafRowIncremental] at hx
        have hx' : x ∈ MatrixRows (reduceKernelLeafRows (basis.push head) shift) := by
          rw [MatrixRows] at hx ⊢
          have hmem : x ∈ reduceKernelLeafRows (basis.push head) shift ∧
              rowIsZero x = false := by
            simpa using hx
          simpa using hmem.1
        rw [reduceKernelLeafRows] at hx'
        refine reduceKernelLeafRowsByPivots_invariant Q hclosed shift ?_ hx'
        intro y hy
        rcases mem_matrixRows_push hy with hy | rfl
        · exact hbasis y hy
        · exact hl _ List.mem_cons_self
  exact hfold rows.toList #[] (fun r hr ↦ hrows r hr)
    (by intro r hr; simp [MatrixRows] at hr) row hrow

private theorem pm_foldl_push_toList {α β : Type*} (g : α → β) :
    ∀ (l : List α) (acc : Array β),
      (l.foldl (fun out x ↦ out.push (g x)) acc).toList = acc.toList ++ l.map g := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons head tail ih =>
      intro acc
      rw [List.foldl_cons, ih, Array.toList_push, List.map_cons,
        List.append_assoc, List.singleton_append]

private theorem pm_doubleFoldl_toList (orders : Array Nat) :
    ∀ (l : List Nat) (acc : Array (Nat × Nat)),
      (l.foldl (fun out j ↦ (List.range (orders.getD j 0)).foldl
          (fun out t ↦ out.push (j, t)) out) acc).toList =
        acc.toList ++ l.flatMap
          (fun j ↦ (List.range (orders.getD j 0)).map (fun t ↦ (j, t))) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons head tail ih =>
      intro acc
      rw [List.foldl_cons, ih, pm_foldl_push_toList, List.flatMap_cons,
        List.append_assoc]

/-- Every in-range equation index appears in `coefficientEquationIndices`. -/
private theorem mem_coefficientEquationIndices {orders : Array Nat} {j t : Nat}
    (hj : j < orders.size) (ht : t < orders.getD j 0) :
    (j, t) ∈ (coefficientEquationIndices orders).toList := by
  rw [coefficientEquationIndices]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, bind_pure,
    Id.run_pure]
  have hrange : ∀ n : Nat, List.range' 0 n = List.range n := fun n ↦
    (List.range_eq_range' (n := n)).symm
  simp only [hrange]
  rw [pm_doubleFoldl_toList]
  simp only [List.nil_append]
  exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
    List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩⟩

private theorem pm_sum_range_mul {M : Type*} [AddCommMonoid M] (cap : Nat)
    (f : Nat → M) :
    ∀ n : Nat,
      ∑ col ∈ Finset.range (n * cap), f col =
        ∑ k ∈ Finset.range n, ∑ a ∈ Finset.range cap, f (k * cap + a) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

omit [BEq F] [LawfulBEq F] in
/-- In-range entries of a scalar coefficient row. -/
private theorem coefficientMatrixRow_getD (problem : XAdicProblem F)
    (degreeCap : Nat) (equation : Nat × Nat) {col : Nat}
    (hcol : col < problem.matrix.size * degreeCap) :
    (coefficientMatrixRow problem degreeCap equation).getD col 0 =
      if col % degreeCap ≤ equation.2 then
        CPolynomial.coeff
          (rowGet (problem.matrix.getD (col / degreeCap) #[]) equation.1)
          (equation.2 - col % degreeCap)
      else 0 := by
  rw [coefficientMatrixRow, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range hcol, Option.map_some, Option.getD_some]

/-- Coefficients of polynomial rows reconstructed from scalar vectors. -/
theorem rowGet_vectorToPolynomialRow_coeff (cap width : Nat)
    (v : Array F) (k a : Nat) :
    CPolynomial.coeff (rowGet (vectorToPolynomialRow cap width v) k) a =
      if k < width ∧ a < cap then v.getD (k * cap + a) 0 else 0 := by
  rw [vectorToPolynomialRow, rowGet]
  rcases Nat.lt_or_ge k width with hk | hk
  · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some,
      CPolynomial.coeff_ofArray]
    rcases Nat.lt_or_ge a cap with ha | ha
    · rw [if_pos ⟨hk, ha⟩, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_map, List.getElem?_range ha, Option.map_some,
        Option.getD_some]
    · rw [if_neg (by omega), Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_eq_none (by simpa using ha), Option.getD_none]
  · rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_none (by simpa using hk), Option.getD_none,
      if_neg (by omega)]
    exact CPolynomial.coeff_zero a

/-- Polynomial rows reconstructed from scalar kernel vectors satisfy the
X-adic conditions of the bounded leaf problem. -/
theorem vectorToPolynomialRow_approximates (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) {v : Array F}
    (hv : v ∈ (homogeneousKernelBasisRows (coefficientMatrixRows problem)
      (problem.matrix.size * leafDegreeCap problem)).toList) :
    RowApproximates mulCtx problem
      (vectorToPolynomialRow (leafDegreeCap problem) problem.matrix.size v) := by
  rw [rowApproximates_iff]
  intro j hj _hjw
  rw [Polynomial.X_pow_dvd_iff]
  intro t ht
  have hcap_pos : 0 < leafDegreeCap problem := le_max_left 1 _
  have htcap : t < leafDegreeCap problem :=
    lt_of_lt_of_le ht (le_trans (getD_le_maxOrder problem hj) (Nat.le_max_right 1 _))
  have hr : coefficientMatrixRow problem (leafDegreeCap problem) (j, t) ∈
      (coefficientMatrixRows problem).toList := by
    rw [coefficientMatrixRows, Array.toList_map]
    exact List.mem_map.mpr ⟨(j, t), mem_coefficientEquationIndices hj ht, rfl⟩
  have hdot := homogeneousKernelBasisRows_dot_eq_zero hv hr
  rw [Polynomial.finsetSum_coeff]
  refine Eq.trans ?_ hdot
  rw [pm_sum_range_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k < problem.matrix.size := Finset.mem_range.mp hk
  have hentry : ∀ a, a < leafDegreeCap problem →
      (coefficientMatrixRow problem (leafDegreeCap problem) (j, t)).getD
        (k * leafDegreeCap problem + a) 0 =
        if a ≤ t then
          CPolynomial.coeff (rowGet (problem.matrix.getD k #[]) j) (t - a)
        else 0 := by
    intro a ha
    have hcol : k * leafDegreeCap problem + a <
        problem.matrix.size * leafDegreeCap problem := by
      have h1 : k * leafDegreeCap problem + a <
          (k + 1) * leafDegreeCap problem := by
        rw [Nat.succ_mul]
        omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ (by omega))
    have hdiv : (k * leafDegreeCap problem + a) / leafDegreeCap problem = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hcap_pos,
        Nat.div_eq_of_lt ha, Nat.zero_add]
    have hmod : (k * leafDegreeCap problem + a) % leafDegreeCap problem = a := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    rw [coefficientMatrixRow_getD problem _ _ hcol, hdiv, hmod]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Eq.trans (Finset.sum_congr rfl fun a ha ↦ ?_)
    (Finset.sum_subset (fun x hx ↦ Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) htcap)) fun a ha hnot ↦ ?_)
  · have ha' : a < t + 1 := Finset.mem_range.mp ha
    rw [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
      rowGet_vectorToPolynomialRow_coeff, if_pos ⟨hk', by omega⟩,
      hentry a (by omega), if_pos (by omega)]
    exact mul_comm _ _
  · have ha1 : a < leafDegreeCap problem := Finset.mem_range.mp ha
    have ha2 : t + 1 ≤ a := by
      by_contra hcon
      exact hnot (Finset.mem_range.mpr (by omega))
    rw [hentry a ha1, if_neg (by omega), zero_mul]

/-- Arithmetic of the packed index `k * cap + a`. -/
theorem pm_pack_index {cap : Nat} (hcap : 0 < cap) {size k a : Nat}
    (hk : k < size) (ha : a < cap) :
    k * cap + a < size * cap ∧ (k * cap + a) / cap = k ∧
      (k * cap + a) % cap = a := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : k * cap + a < (k + 1) * cap := by
      rw [Nat.succ_mul]
      omega
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ (by omega))
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hcap, Nat.div_eq_of_lt ha,
      Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

/-- Pack the coefficients below the leaf degree cap of a polynomial row into
one flat scalar vector: coefficient `a` of coordinate `k` is stored at index
`k * leafDegreeCap problem + a`.  This is the coefficient-side inverse of
`vectorToPolynomialRow`. -/
def rowToCoefficientVector (problem : XAdicProblem F) (row : PolynomialRow F) :
    Array F :=
  (List.range (problem.matrix.size * leafDegreeCap problem)).map
    (fun c ↦ CPolynomial.coeff (rowGet row (c / leafDegreeCap problem))
      (c % leafDegreeCap problem)) |>.toArray

omit [BEq F] [LawfulBEq F] in
/-- In-range entries of the packed coefficient vector. -/
private theorem rowToCoefficientVector_getD (problem : XAdicProblem F)
    (row : PolynomialRow F) {c : Nat}
    (hc : c < problem.matrix.size * leafDegreeCap problem) :
    (rowToCoefficientVector problem row).getD c 0 =
      CPolynomial.coeff (rowGet row (c / leafDegreeCap problem))
        (c % leafDegreeCap problem) := by
  rw [rowToCoefficientVector, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some]

/-- Reconstructing a polynomial row from its packed coefficient vector is the
identity on rows of the principal width whose coefficients respect the leaf
degree cap. -/
theorem vectorToPolynomialRow_rowToCoefficientVector
    (problem : XAdicProblem F) {row : PolynomialRow F}
    (hsize : row.size = problem.matrix.size)
    (hdeg : ∀ k, k < row.size → ∀ a, leafDegreeCap problem ≤ a →
      CPolynomial.coeff (rowGet row k) a = 0) :
    vectorToPolynomialRow (leafDegreeCap problem) problem.matrix.size
      (rowToCoefficientVector problem row) = row := by
  have hcap_pos : 0 < leafDegreeCap problem := le_max_left 1 _
  have hcoord : ∀ k,
      rowGet (vectorToPolynomialRow (leafDegreeCap problem)
        problem.matrix.size (rowToCoefficientVector problem row)) k =
        rowGet row k := by
    intro k
    apply CPolynomial.eq_iff_coeff.2
    intro a
    rw [rowGet_vectorToPolynomialRow_coeff]
    rcases Nat.lt_or_ge k problem.matrix.size with hk | hk
    · rcases Nat.lt_or_ge a (leafDegreeCap problem) with ha | ha
      · obtain ⟨hc, hdiv, hmod⟩ := pm_pack_index hcap_pos hk ha
        rw [if_pos ⟨hk, ha⟩, rowToCoefficientVector_getD problem row hc,
          hdiv, hmod]
      · rw [if_neg (by omega), hdeg k (by omega) a ha]
    · rw [if_neg (by omega)]
      have hzero : rowGet row k = 0 := by
        rw [rowGet, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (by omega)]
        rfl
      rw [hzero]
      exact (CPolynomial.coeff_zero a).symm
  refine Array.ext ?_ fun i hi hi' ↦ ?_
  · rw [vectorToPolynomialRow]
    simp only [List.size_toArray, List.length_map, List.length_range, hsize]
  · have h := hcoord i
    rw [rowGet, rowGet, array_getD_of_lt' _ 0 hi, array_getD_of_lt' _ 0 hi']
      at h
    exact h

/-- Conversely to `mem_coefficientEquationIndices`, every member of
`coefficientEquationIndices` is an in-range equation index. -/
private theorem mem_coefficientEquationIndices_bounds {orders : Array Nat}
    {j t : Nat}
    (h : (j, t) ∈ (coefficientEquationIndices orders).toList) :
    j < orders.size ∧ t < orders.getD j 0 := by
  rw [coefficientEquationIndices] at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, bind_pure,
    Id.run_pure] at h
  have hrange : ∀ n : Nat, List.range' 0 n = List.range n := fun n ↦
    (List.range_eq_range' (n := n)).symm
  simp only [hrange] at h
  rw [pm_doubleFoldl_toList] at h
  simp only [List.nil_append] at h
  obtain ⟨j', hj', hmem⟩ := List.mem_flatMap.mp h
  obtain ⟨t', ht', heq⟩ := List.mem_map.mp hmem
  have h1 : j' = j := congrArg Prod.fst heq
  have h2 : t' = t := congrArg Prod.snd heq
  subst h1
  subst h2
  exact ⟨List.mem_range.mp hj', List.mem_range.mp ht'⟩

/-- **Converse coefficient bridge.**  A polynomial row of a well-formed
bounded leaf problem that satisfies the X-adic conditions yields a packed
coefficient vector orthogonal to every scalar coefficient row. -/
theorem coefficientMatrixRows_dot_eq_zero_of_approximates
    (mulCtx : CPolynomial.MulContext F) (problem : XAdicProblem F)
    {row : PolynomialRow F}
    (happrox : RowApproximates mulCtx problem row)
    (hwf : WellFormed problem.matrix) :
    ∀ r ∈ (coefficientMatrixRows problem).toList,
      ∑ c ∈ Finset.range (problem.matrix.size * leafDegreeCap problem),
        r.getD c 0 * (rowToCoefficientVector problem row).getD c 0 = 0 := by
  intro r hr
  simp only [coefficientMatrixRows] at hr
  rw [Array.toList_map] at hr
  obtain ⟨eqn, heqmem, rfl⟩ := List.mem_map.mp hr
  obtain ⟨j, t⟩ := eqn
  obtain ⟨hj, ht⟩ := mem_coefficientEquationIndices_bounds heqmem
  have hcap_pos : 0 < leafDegreeCap problem := le_max_left 1 _
  have htcap : t < leafDegreeCap problem :=
    lt_of_lt_of_le ht (le_trans (getD_le_maxOrder problem hj)
      (Nat.le_max_right 1 _))
  have hdvd : (Polynomial.X : Polynomial F) ^ (problem.orders.getD j 0) ∣
      ∑ k ∈ Finset.range problem.matrix.size,
        (rowGet row k).toPoly *
          (rowGet (problem.matrix.getD k #[]) j).toPoly := by
    rcases Nat.lt_or_ge j (MatrixWidth problem.matrix) with hjw | hjw
    · exact (rowApproximates_iff mulCtx problem row).mp happrox j hj hjw
    · have hzero : ∀ k ∈ Finset.range problem.matrix.size,
          (rowGet row k).toPoly *
            (rowGet (problem.matrix.getD k #[]) j).toPoly = 0 := by
        intro k hk
        have hk' : k < problem.matrix.size := Finset.mem_range.mp hk
        have hmemrow : problem.matrix.getD k #[] ∈
            MatrixRows problem.matrix := by
          rw [MatrixRows, array_getD_of_lt' _ #[] hk',
            ← Array.getElem_toList (by simpa using hk')]
          exact List.getElem_mem _
        have hsz := hwf _ hmemrow
        have h0 : rowGet (problem.matrix.getD k #[]) j = 0 := by
          rw [rowGet, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none (by omega)]
          rfl
        rw [h0, CPolynomial.toPoly_zero, mul_zero]
      rw [Finset.sum_eq_zero hzero]
      exact dvd_zero _
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdvd t ht
  have hentry : ∀ k, k < problem.matrix.size →
      ∀ a, a < leafDegreeCap problem →
      (coefficientMatrixRow problem (leafDegreeCap problem) (j, t)).getD
        (k * leafDegreeCap problem + a) 0 =
        if a ≤ t then
          CPolynomial.coeff (rowGet (problem.matrix.getD k #[]) j) (t - a)
        else 0 := by
    intro k hk a ha
    obtain ⟨hc, hdiv, hmod⟩ := pm_pack_index hcap_pos hk ha
    rw [coefficientMatrixRow_getD problem _ _ hc, hdiv, hmod]
  have hw : ∀ k, k < problem.matrix.size →
      ∀ a, a < leafDegreeCap problem →
      (rowToCoefficientVector problem row).getD
        (k * leafDegreeCap problem + a) 0 =
        CPolynomial.coeff (rowGet row k) a := by
    intro k hk a ha
    obtain ⟨hc, hdiv, hmod⟩ := pm_pack_index hcap_pos hk ha
    rw [rowToCoefficientVector_getD problem row hc, hdiv, hmod]
  have hinner : ∀ k, k < problem.matrix.size →
      ∑ a ∈ Finset.range (leafDegreeCap problem),
        (coefficientMatrixRow problem (leafDegreeCap problem) (j, t)).getD
          (k * leafDegreeCap problem + a) 0 *
        (rowToCoefficientVector problem row).getD
          (k * leafDegreeCap problem + a) 0 =
      Polynomial.coeff ((rowGet row k).toPoly *
        (rowGet (problem.matrix.getD k #[]) j).toPoly) t := by
    intro k hk
    symm
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Eq.trans (Finset.sum_congr rfl fun a ha ↦ ?_)
      (Finset.sum_subset (fun x hx ↦ Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) htcap))
        fun a ha hnot ↦ ?_)
    · have ha' : a < t + 1 := Finset.mem_range.mp ha
      rw [← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly,
        hentry k hk a (by omega), if_pos (by omega), hw k hk a (by omega)]
      exact mul_comm _ _
    · have ha1 : a < leafDegreeCap problem := Finset.mem_range.mp ha
      have ha2 : t + 1 ≤ a := by
        by_contra hcon
        exact hnot (Finset.mem_range.mpr (by omega))
      rw [hentry k hk a ha1, if_neg (by omega), zero_mul]
  rw [pm_sum_range_mul,
    Finset.sum_congr rfl fun k hk ↦ hinner k (Finset.mem_range.mp hk),
    ← Polynomial.finsetSum_coeff]
  exact hcoeff

/-- Every kernel-leaf basis row approximates the problem and has the principal
row width. -/
theorem kernelLeafBasis_rows (mulCtx : CPolynomial.MulContext F)
    (problem : XAdicProblem F) (shift : Array Nat) :
    ∀ row ∈ MatrixRows (kernelLeafBasis problem shift),
      RowApproximates mulCtx problem row ∧ row.size = problem.matrix.size := by
  set Q : PolynomialRow F → Prop := fun row ↦
    RowApproximates mulCtx problem row ∧ row.size = problem.matrix.size with hQ
  have hclosed : ∀ (target reducer : PolynomialRow F) (shift' : Array Nat),
      Q target → Q reducer →
      Q (cancelKernelLeafLeadingTerm target reducer shift') := by
    intro target reducer shift' ht hr
    refine ⟨rowApproximates_cancelKernelLeafLeadingTerm mulCtx problem shift'
      ht.1 hr.1, ?_⟩
    rw [cancelKernelLeafLeadingTerm]
    split
    · split
      · split
        · exact ht.2
        · rw [rowSub_size, rowScaleCoeffX_size]
          have h1 := ht.2
          have h2 := hr.2
          omega
      · exact ht.2
    · exact ht.2
  intro row hrow
  simp only [kernelLeafBasis] at hrow
  rw [MatrixRows, completeMissingPivotRows, Array.toList_append] at hrow
  rcases List.mem_append.mp hrow with hmem | hmem
  · refine reduceKernelLeafRowsIncremental_invariant Q hclosed shift ?_ hmem
    intro r hr
    rw [MatrixRows, Array.toList_append] at hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [Array.toList_map] at hr
      rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
      refine ⟨vectorToPolynomialRow_approximates mulCtx problem hw, ?_⟩
      simp [vectorToPolynomialRow]
    · simp only [kernelLeafCompletionRows] at hr
      rcases List.mem_map.mp hr with ⟨i, _hi, rfl⟩
      refine ⟨rowApproximates_monomialUnitRow mulCtx problem
        (fun j hj ↦ le_trans (getD_le_maxOrder problem hj)
          (Nat.le_max_right 1 _)), ?_⟩
      simp [monomialUnitRow]
  · have happrox := missingCompletionRows_approximates mulCtx problem shift _ hmem
    refine ⟨happrox, ?_⟩
    rw [missingCompletionRows, List.toList_toArray] at hmem
    rcases List.mem_filterMap.mp hmem with ⟨i, _hi, hsome⟩
    split at hsome
    · cases hsome
    · cases hsome
      simp [monomialUnitRow]

end Approximant

end PolynomialMatrix

end CompPoly
