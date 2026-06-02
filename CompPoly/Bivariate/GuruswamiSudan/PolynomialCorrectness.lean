/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Polynomial
import CompPoly.Data.List.Lemmas
import CompPoly.LinearAlgebra.Dense
import Mathlib.Tactic.Ring

/-!
# Guruswami-Sudan Polynomial Correctness Lemmas

Correctness lemmas for dense bivariate coefficient assembly, weighted-degree
enumeration, and executable Hasse derivatives.
-/

namespace CompPoly

namespace CPolynomial

/-- Coefficients past the stored canonical array are zero. -/
theorem coeff_eq_zero_of_size_le {R : Type*} [Zero R] (p : CPolynomial R)
    {i : Nat} (hi : p.val.size ≤ i) : p.coeff i = 0 := by
  unfold CPolynomial.coeff CPolynomial.Raw.coeff
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi]
  rfl

/-- The natural degree of a nonzero computable polynomial lies in its support. -/
theorem natDegree_mem_support_of_nonzero {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} (hp : p ≠ 0) : p.natDegree ∈ p.support := by
  rcases CPolynomial.degree_eq_support_max p hp with ⟨n, hnmem, hdegree⟩
  have hnat := CPolynomial.degree_eq_natDegree p hp
  rw [hnat] at hdegree
  have hn : n = p.natDegree := WithBot.coe_eq_coe.mp hdegree.symm
  simpa [hn] using hnmem

end CPolynomial

namespace DenseMatrix

/-- Reading an in-bounds entry from a matrix constructed by `ofFn` returns that entry. -/
theorem get_ofFn [Zero F] (rows cols : Nat) (f : Nat → Nat → F)
    {row col : Nat} (hrow : row < rows) (hcol : col < cols) :
    (ofFn rows cols f).get row col = f row col := by
  unfold get index
  have hidx : row * cols + col < rows * cols := by
    calc
      row * cols + col < row * cols + cols := Nat.add_lt_add_left hcol _
      _ = (row + 1) * cols := by rw [Nat.succ_mul]
      _ ≤ rows * cols := Nat.mul_le_mul_right cols hrow
  have hidx' : row * (ofFn rows cols f).cols + col < (ofFn rows cols f).data.size := by
    simpa [ofFn] using hidx
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hidx']
  simp [ofFn]
  have hcols : 0 < cols := Nat.lt_of_le_of_lt (Nat.zero_le col) hcol
  congr
  · rw [Nat.mul_comm row cols, Nat.add_comm (cols * row) col,
      Nat.add_mul_div_left col row hcols, Nat.div_eq_of_lt hcol, Nat.zero_add]
  · rw [Nat.mod_eq_of_lt hcol]

/-- Fold over a range with one distinguished nonzero entry. -/
theorem foldl_range_one_special {F : Type*} [AddCommMonoid F] {pivot : Nat} (x : F) :
    ∀ start len (init : F),
    (List.range' start len).foldl (fun acc j ↦ acc + if j = pivot then x else 0) init =
      init + if start ≤ pivot ∧ pivot < start + len then x else 0 := by
  intro start len init
  revert start init
  induction len with
  | zero =>
      intro start init
      have hpivotFalse : ¬(start ≤ pivot ∧ pivot < start) := by omega
      simp [hpivotFalse]
  | succ len ih =>
      intro start init
      rw [List.range']
      simp only [List.foldl_cons]
      rw [ih (start + 1) (init + if start = pivot then x else 0)]
      by_cases hsp : start = pivot
      · subst pivot
        simp
      · simp [hsp]
        by_cases hpivotIn : start + 1 ≤ pivot ∧ pivot < start + 1 + len
        · have hstartPivot : start ≤ pivot ∧ pivot < start + (len + 1) := by omega
          have hstart_lt : start < pivot := by omega
          simp [hpivotIn, hstartPivot, hstart_lt]
        · have hstartPivotFalse : ¬(start ≤ pivot ∧ pivot < start + (len + 1)) := by
            omega
          have hnot : ¬(start < pivot ∧ pivot < start + 1 + len) := by omega
          simp [hstartPivotFalse, hnot]

/-- A range fold with a single distinguished index. -/
theorem foldl_range_single_index {F : Type*} [AddCommMonoid F] {n k : Nat}
    (hk : k < n) (x : F) :
    (List.range' 0 n).foldl (fun acc j ↦ acc + if j = k then x else 0) 0 = x := by
  rw [foldl_range_one_special (F := F) (pivot := k) x 0 n 0]
  have hin : 0 ≤ k ∧ k < 0 + n := by omega
  simp [hin, hk]

/-- A range fold with identically zero contributions is zero. -/
theorem foldl_range_eq_zero_of_zero {F : Type*} [AddMonoid F] {n : Nat} {f : Nat → F}
    (hzero : ∀ c, c < n → f c = 0) :
    (List.range' 0 n).foldl (fun acc c ↦ acc + f c) 0 = 0 := by
  have hfold : ∀ (xs : List Nat) (acc : F),
      acc = 0 → (∀ c, c ∈ xs → f c = 0) →
        xs.foldl (fun acc c ↦ acc + f c) acc = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc _
        exact hacc
    | cons c xs ih =>
        intro acc hacc hxs
        simp only [List.foldl_cons]
        apply ih
        · simp [hacc, hxs c (by simp)]
        · intro d hd
          exact hxs d (by simp [hd])
  apply hfold (List.range' 0 n)
  · rfl
  · intro c hc
    exact hzero c (by simpa using (List.mem_range'_1.mp hc).2)

end DenseMatrix

namespace CBivariate

/-- Bivariate coefficients are additive. -/
theorem coeff_add {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (P Q : CBivariate R) (i j : Nat) :
    coeff (P + Q) i j = coeff P i j + coeff Q i j := by
  change CPolynomial.coeff (CPolynomial.coeff (P + Q : CBivariate R) j) i =
    CPolynomial.coeff (CPolynomial.coeff P j) i +
      CPolynomial.coeff (CPolynomial.coeff Q j) i
  have houter : CPolynomial.coeff (P + Q : CBivariate R) j =
      CPolynomial.coeff P j + CPolynomial.coeff Q j := by
    exact CPolynomial.coeff_add (p := P) (q := Q) (i := j)
  rw [houter]
  rw [CPolynomial.coeff_add]

/-- All bivariate coefficients of zero are zero. -/
theorem coeff_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (i j : Nat) :
    coeff (0 : CBivariate R) i j = 0 := by
  change CPolynomial.coeff (CPolynomial.coeff (0 : CBivariate R) j) i = 0
  have houter : CPolynomial.coeff (0 : CBivariate R) j = 0 := CPolynomial.coeff_zero j
  rw [houter]
  rw [CPolynomial.coeff_zero]

/-- Bivariate coefficients past the stored outer array are zero. -/
theorem coeff_eq_zero_of_y_size_le {R : Type*} [Zero R] (Q : CBivariate R)
    {i j : Nat} (hj : Q.val.size ≤ j) : coeff Q i j = 0 := by
  change (CPolynomial.coeff Q j).coeff i = 0
  rw [CPolynomial.coeff_eq_zero_of_size_le Q hj]
  exact CPolynomial.coeff_zero i

/-- Bivariate extensionality through all scalar coefficients. -/
theorem eq_iff_coeff {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    {P Q : CBivariate R} : P = Q ↔ ∀ i j, coeff P i j = coeff Q i j := by
  constructor
  · intro h i j
    rw [h]
  · intro h
    apply (CPolynomial.eq_iff_coeff (p := P) (q := Q)).2
    intro j
    apply (CPolynomial.eq_iff_coeff (p := CPolynomial.coeff P j)
      (q := CPolynomial.coeff Q j)).2
    intro i
    exact h i j

/-- Coefficients of one bivariate monomial. -/
theorem coeff_monomialXY {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (n m i j : Nat) (c : R) :
    coeff (monomialXY n m c) i j = if i = n ∧ j = m then c else 0 := by
  change CPolynomial.coeff
      (CPolynomial.coeff (CPolynomial.monomial m (CPolynomial.monomial n c) :
        CBivariate R) j) i = if i = n ∧ j = m then c else 0
  have houter :
      CPolynomial.coeff
        (CPolynomial.monomial m (CPolynomial.monomial n c) : CBivariate R) j =
      if j = m then CPolynomial.monomial n c else 0 := by
    exact CPolynomial.coeff_monomial m j (CPolynomial.monomial n c)
  rw [houter]
  by_cases hj : j = m
  · subst j
    simpa [CPolynomial.coeff] using CPolynomial.coeff_monomial (R := R) n i c
  · simp [hj]
    simpa [CPolynomial.coeff] using CPolynomial.coeff_zero (R := R) i

/-- Coefficients of a polynomial assembled from a monomial array are the folded
sum of matching monomial coefficients. -/
theorem ofMonomialCoeffs_coeff {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (monomials : Array Monomial) (coeffs : Array R) (i j : Nat) :
    coeff (ofMonomialCoeffs monomials coeffs) i j =
      (List.range' 0 monomials.size).foldl
        (fun acc col ↦
          let monomial := monomials.getD col ⟨0, 0⟩
          acc + if i = monomial.xDegree ∧ j = monomial.yDegree then coeffs.getD col 0
            else 0)
        0 := by
  unfold ofMonomialCoeffs
  have hfold : ∀ (xs : List Nat) (out : CBivariate R) (acc : R),
      coeff out i j = acc →
      coeff
        (xs.foldl
          (fun out col ↦
            let monomial := monomials.getD col ⟨0, 0⟩
            out + monomialXY monomial.xDegree monomial.yDegree (coeffs.getD col 0))
          out) i j =
        xs.foldl
          (fun acc col ↦
            let monomial := monomials.getD col ⟨0, 0⟩
            acc + if i = monomial.xDegree ∧ j = monomial.yDegree then coeffs.getD col 0
              else 0)
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro out acc hout
        exact hout
    | cons col xs ih =>
        intro out acc hout
        simp only [List.foldl_cons]
        apply ih
        rw [coeff_add, coeff_monomialXY, hout]
  exact hfold (List.range' 0 monomials.size) 0 0 (coeff_zero i j)

/-- The executable monomial grid has no duplicate exponent pairs. -/
theorem monomialGrid_nodup (bound : Nat) : (monomialGrid bound).Nodup := by
  unfold monomialGrid
  rw [List.nodup_flatMap]
  constructor
  · intro y _
    exact List.nodup_range.map (by
      intro x₁ x₂ h
      cases h
      rfl)
  · exact List.nodup_range.pairwise_of_forall_ne (by
      intro y hy y' hy' hyne
      simp only [Function.onFun, List.disjoint_left]
      intro m hm hm'
      rcases List.mem_map.mp hm with ⟨x, _, rfl⟩
      rcases List.mem_map.mp hm' with ⟨x', _, hmEq⟩
      exact hyne (by cases hmEq; rfl))

/-- Weighted-degree monomial enumeration has no duplicate exponent pairs. -/
theorem monomialsWeightedDegreeLE_nodup (xWeight yWeight bound : Nat) :
    (monomialsWeightedDegreeLE xWeight yWeight bound).toList.Nodup := by
  simpa [monomialsWeightedDegreeLE] using
    (monomialGrid_nodup bound).filter
      (fun m ↦ xWeight * m.xDegree + yWeight * m.yDegree ≤ bound)

/-- All returned weighted-degree monomials satisfy the requested bound. -/
theorem monomialsWeightedDegreeLE_sound
    {xWeight yWeight bound : Nat} {m : Monomial}
    (hm : m ∈ (monomialsWeightedDegreeLE xWeight yWeight bound).toList) :
    xWeight * m.xDegree + yWeight * m.yDegree ≤ bound := by
  simp [monomialsWeightedDegreeLE] at hm
  exact hm.2

/-- In a nodup array, equal in-bounds `getD` entries have equal indices. -/
theorem array_getD_inj_of_nodup {α : Type*} [DecidableEq α] {xs : Array α}
    {default : α} (hnodup : xs.toList.Nodup) {i j : Nat}
    (hi : i < xs.size) (hj : j < xs.size)
    (h : xs.getD i default = xs.getD j default) : i = j := by
  exact (List.getElem_inj hnodup).mp (by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj] at h
    simpa using h)

/-- For a nodup monomial array, the assembled polynomial recovers the matching
coefficient at each listed monomial. -/
theorem ofMonomialCoeffs_coeff_getD {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    {monomials : Array Monomial} {coeffs : Array R}
    (hnodup : monomials.toList.Nodup) {k : Nat} (hk : k < monomials.size) :
    coeff (ofMonomialCoeffs monomials coeffs)
        (monomials.getD k ⟨0, 0⟩).xDegree (monomials.getD k ⟨0, 0⟩).yDegree =
      coeffs.getD k 0 := by
  rw [ofMonomialCoeffs_coeff]
  have hfold : ∀ (xs : List Nat) (acc : R),
      (∀ col, col ∈ xs → col < monomials.size) →
      xs.foldl
          (fun acc col ↦
            let monomial := monomials.getD col ⟨0, 0⟩
            acc +
              if (monomials.getD k ⟨0, 0⟩).xDegree = monomial.xDegree ∧
                  (monomials.getD k ⟨0, 0⟩).yDegree = monomial.yDegree then
                coeffs.getD col 0
              else 0)
          acc =
        xs.foldl (fun acc col ↦ acc + if col = k then coeffs.getD k 0 else 0)
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc _
        rfl
    | cons col xs ih =>
        intro acc hxs
        simp only [List.foldl_cons]
        have hcol : col < monomials.size := hxs col (by simp)
        have hterm :
            (if (monomials.getD k ⟨0, 0⟩).xDegree =
                    (monomials.getD col ⟨0, 0⟩).xDegree ∧
                  (monomials.getD k ⟨0, 0⟩).yDegree =
                    (monomials.getD col ⟨0, 0⟩).yDegree then
                coeffs.getD col 0
              else 0) =
              if col = k then coeffs.getD k 0 else 0 := by
          by_cases hcolk : col = k
          · subst col
            simp
          · have hmono_ne : monomials.getD k ⟨0, 0⟩ ≠
                monomials.getD col ⟨0, 0⟩ := by
              intro hmono
              have hidx := array_getD_inj_of_nodup (xs := monomials)
                (default := ⟨0, 0⟩) hnodup hk hcol hmono
              exact hcolk hidx.symm
            have hpair_ne :
                ¬((monomials.getD k ⟨0, 0⟩).xDegree =
                    (monomials.getD col ⟨0, 0⟩).xDegree ∧
                  (monomials.getD k ⟨0, 0⟩).yDegree =
                    (monomials.getD col ⟨0, 0⟩).yDegree) := by
              rintro ⟨hx, hy⟩
              apply hmono_ne
              cases hkmono : monomials.getD k ⟨0, 0⟩
              cases hcmono : monomials.getD col ⟨0, 0⟩
              simp [hkmono, hcmono] at hx hy ⊢
              exact ⟨hx, hy⟩
            rw [if_neg hpair_ne, if_neg hcolk]
        rw [hterm]
        apply ih
        intro c hc
        exact hxs c (by simp [hc])
  rw [hfold]
  · exact DenseMatrix.foldl_range_single_index hk (coeffs.getD k 0)
  · intro col hcol
    simpa using (List.mem_range'_1.mp hcol).2

/-- A nonzero coefficient at a listed monomial makes the assembled bivariate
polynomial nonzero. -/
theorem ofMonomialCoeffs_ne_zero_of_coeff_getD_ne_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    {monomials : Array Monomial} {coeffs : Array R}
    (hnodup : monomials.toList.Nodup) {k : Nat} (hk : k < monomials.size)
    (hcoeff : coeffs.getD k 0 ≠ 0) :
    ofMonomialCoeffs monomials coeffs ≠ 0 := by
  intro hzero
  let monomial := monomials.getD k ⟨0, 0⟩
  have hcoeffEq := congrArg
    (fun Q : CBivariate R ↦ coeff Q monomial.xDegree monomial.yDegree) hzero
  have hget := ofMonomialCoeffs_coeff_getD (R := R) (monomials := monomials)
    (coeffs := coeffs) hnodup hk
  dsimp [monomial] at hget hcoeffEq
  rw [hget] at hcoeffEq
  rw [coeff_zero] at hcoeffEq
  exact hcoeff hcoeffEq

/-- If all coefficients above a weighted-degree bound are zero, the executable
weighted degree is below that bound. -/
theorem natWeightedDegree_le_of_coeff_zero {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (f : CBivariate R) (u v bound : Nat)
    (hzero : ∀ i j, bound < u * i + v * j → coeff f i j = 0) :
    natWeightedDegree f u v ≤ bound := by
  unfold natWeightedDegree
  apply Finset.sup_le
  intro j hj
  by_cases hcoeffY : f.val.coeff j = 0
  · have hne : f.val.coeff j ≠ 0 := (CPolynomial.mem_support_iff f j).mp hj
    exact False.elim (hne hcoeffY)
  · have hmem : (f.val.coeff j).natDegree ∈ CPolynomial.support (f.val.coeff j) :=
      CPolynomial.natDegree_mem_support_of_nonzero hcoeffY
    have hcoeff_ne : CPolynomial.coeff (f.val.coeff j) (f.val.coeff j).natDegree ≠ 0 :=
      (CPolynomial.mem_support_iff (f.val.coeff j) _).mp hmem
    by_contra hnot
    have hgt : bound < u * (f.val.coeff j).natDegree + v * j := by omega
    have hz := hzero (f.val.coeff j).natDegree j hgt
    unfold coeff at hz
    exact hcoeff_ne hz

/-- Coefficients above a bound are zero for a polynomial assembled from monomials
all below that bound. -/
theorem ofMonomialCoeffs_coeff_eq_zero_of_weight_gt {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    {monomials : Array Monomial} {coeffs : Array R} {u v bound i j : Nat}
    (hall : ∀ monomial, monomial ∈ monomials.toList →
      u * monomial.xDegree + v * monomial.yDegree ≤ bound)
    (hgt : bound < u * i + v * j) :
    coeff (ofMonomialCoeffs monomials coeffs) i j = 0 := by
  rw [ofMonomialCoeffs_coeff]
  apply DenseMatrix.foldl_range_eq_zero_of_zero
  intro col hcol
  let monomial := monomials.getD col ⟨0, 0⟩
  have hmem : monomial ∈ monomials.toList := by
    unfold monomial
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hcol]
    exact Array.mem_def.mp (Array.getElem_mem (xs := monomials) hcol)
  have hle := hall monomial hmem
  by_cases hmatch : i = monomial.xDegree ∧ j = monomial.yDegree
  · exfalso
    rcases hmatch with ⟨hi, hj⟩
    rw [hi, hj] at hgt
    exact Nat.not_lt_of_ge hle hgt
  · change (if i = monomial.xDegree ∧ j = monomial.yDegree then coeffs.getD col 0
        else 0) = 0
    rw [if_neg hmatch]

/-- A polynomial assembled from bounded monomials has weighted degree below the
same bound. -/
theorem ofMonomialCoeffs_natWeightedDegree_le {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    {monomials : Array Monomial} {coeffs : Array R} {u v bound : Nat}
    (hall : ∀ monomial, monomial ∈ monomials.toList →
      u * monomial.xDegree + v * monomial.yDegree ≤ bound) :
    natWeightedDegree (ofMonomialCoeffs monomials coeffs) u v ≤ bound :=
  natWeightedDegree_le_of_coeff_zero _ u v bound fun _ _ hgt ↦
    ofMonomialCoeffs_coeff_eq_zero_of_weight_gt (monomials := monomials)
      (coeffs := coeffs) hall hgt

/-- Coefficients of a polynomial materialized from Hasse terms are the folded
sum of matching term coefficients. -/
theorem hasseDerivativeFromTerms_coeff {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (terms : List (HasseTerm R)) (i j : Nat) :
    coeff (hasseDerivativeFromTerms terms) i j =
      terms.foldl
        (fun acc term ↦ acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
        0 := by
  unfold hasseDerivativeFromTerms
  have hfold : ∀ (xs : List (HasseTerm R)) (out : CBivariate R) (acc : R),
      coeff out i j = acc →
      coeff (xs.foldl (fun out term ↦
          out + monomialXY term.xDegree term.yDegree term.coeff) out) i j =
        xs.foldl
          (fun acc term ↦ acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
          acc := by
    intro xs
    induction xs with
    | nil =>
        intro out acc hout
        exact hout
    | cons term xs ih =>
        intro out acc hout
        simp only [List.foldl_cons]
        apply ih
        rw [coeff_add, coeff_monomialXY, hout]
  exact hfold terms 0 0 (coeff_zero i j)

/-- Evaluating after appending one Hasse term adds that term's contribution. -/
theorem hasseDerivativeEvalFromTerms_append_single {R : Type*} [Semiring R]
    (terms : List (HasseTerm R)) (term : HasseTerm R) (x y : R) :
    hasseDerivativeEvalFromTerms (terms ++ [term]) x y =
      hasseDerivativeEvalFromTerms terms x y +
        term.coeff * x ^ term.xDegree * y ^ term.yDegree := by
  unfold hasseDerivativeEvalFromTerms
  simp [List.foldl_append]

/-- The fixed coefficient of the executable Hasse term list is the matching
coefficient fold over the same degree ranges. -/
theorem hasseDerivativeTermList_coeff_fold {R : Type*} [Semiring R]
    (a b i j : Nat) (Q : CBivariate R) :
    (hasseDerivativeTermList a b Q).foldl
        (fun acc term ↦ acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
        0 =
      (List.range' 0 Q.val.size).foldl
        (fun acc yDeg ↦
          let coeffY := Q.val.coeff yDeg
          if b ≤ yDeg then
            (List.range' 0 coeffY.val.size).foldl
              (fun acc xDeg ↦
                if a ≤ xDeg then
                  acc +
                    if i = xDeg - a ∧ j = yDeg - b then
                      (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
                    else 0
                else acc)
              acc
          else acc)
        0 := by
  unfold hasseDerivativeTermList
  have houter : ∀ (ys : List Nat) (terms : List (HasseTerm R)) (acc : R),
      terms.foldl
          (fun acc term ↦ acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
          0 = acc →
      (ys.foldl
          (fun out yDeg ↦
            let coeffY := Q.val.coeff yDeg
            if b ≤ yDeg then
              (List.range' 0 coeffY.val.size).foldl
                (fun out xDeg ↦
                  if a ≤ xDeg then
                    let coeff := (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) *
                      coeffY.coeff xDeg
                    out ++ [⟨xDeg - a, yDeg - b, coeff⟩]
                  else out)
                out
            else out)
          terms).foldl
          (fun acc term ↦ acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
          0 =
        ys.foldl
          (fun acc yDeg ↦
            let coeffY := Q.val.coeff yDeg
            if b ≤ yDeg then
              (List.range' 0 coeffY.val.size).foldl
                (fun acc xDeg ↦
                  if a ≤ xDeg then
                    acc +
                      if i = xDeg - a ∧ j = yDeg - b then
                        (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
                      else 0
                  else acc)
                acc
            else acc)
          acc := by
    intro ys
    induction ys with
    | nil =>
        intro terms acc hterms
        exact hterms
    | cons yDeg ys ih =>
        intro terms acc hterms
        simp only [List.foldl_cons]
        by_cases hy : b ≤ yDeg
        · simp only [hy, if_true]
          have hinner : ∀ (xs : List Nat) (terms : List (HasseTerm R)) (acc : R),
              terms.foldl
                  (fun acc term ↦
                    acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
                  0 = acc →
              (xs.foldl
                  (fun out xDeg ↦
                    if a ≤ xDeg then
                      let coeff := (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) *
                        (Q.val.coeff yDeg).coeff xDeg
                      out ++ [⟨xDeg - a, yDeg - b, coeff⟩]
                    else out)
                  terms).foldl
                  (fun acc term ↦
                    acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
                  0 =
                xs.foldl
                  (fun acc xDeg ↦
                    if a ≤ xDeg then
                      acc +
                        if i = xDeg - a ∧ j = yDeg - b then
                          (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) *
                            (Q.val.coeff yDeg).coeff xDeg
                        else 0
                    else acc)
                  acc := by
            intro xs
            induction xs with
            | nil =>
                intro terms acc hterms
                exact hterms
            | cons xDeg xs ihx =>
                intro terms acc hterms
                simp only [List.foldl_cons]
                by_cases hx : a ≤ xDeg
                · simp only [hx, if_true]
                  apply ihx
                  simp [List.foldl_append, hterms]
                · simp only [hx, if_false]
                  exact ihx terms acc hterms
          apply ih
          exact hinner (List.range' 0 (Q.val.coeff yDeg).val.size) terms acc hterms
        · simp only [hy, if_false]
          exact ih terms acc hterms
  simpa using houter (List.range' 0 Q.val.size) [] 0 rfl

/-- Collapse the inner `x`-fold in a fixed Hasse coefficient calculation. -/
theorem hasseDerivativeTermList_coeff_inner_fold {R : Type*} [Semiring R]
    (a b i j yDeg : Nat) (coeffY : CPolynomial R) (acc : R) (hy : b ≤ yDeg) :
    (List.range' 0 coeffY.val.size).foldl
        (fun acc xDeg ↦
          if a ≤ xDeg then
            acc +
              if i = xDeg - a ∧ j = yDeg - b then
                (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
              else 0
          else acc)
        acc =
      acc +
        if yDeg = j + b ∧ i + a < coeffY.val.size then
          (Nat.choose (i + a) a : R) * (Nat.choose yDeg b : R) * coeffY.coeff (i + a)
        else 0 := by
  have hstep :
      (List.range' 0 coeffY.val.size).foldl
          (fun acc xDeg ↦
            if a ≤ xDeg then
              acc +
                if i = xDeg - a ∧ j = yDeg - b then
                  (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
                else 0
            else acc)
          acc =
        (List.range' 0 coeffY.val.size).foldl
          (fun acc xDeg ↦
            acc +
              if a ≤ xDeg then
                if i = xDeg - a ∧ j = yDeg - b then
                  (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
                else 0
              else 0)
          acc := by
    apply List.foldl_congr_of_mem
    intro acc xDeg
    by_cases hx : a ≤ xDeg <;> simp [hx]
  rw [hstep]
  by_cases hyTarget : yDeg = j + b
  · subst yDeg
    have hcontrib : ∀ xDeg,
        (if a ≤ xDeg then
            if i = xDeg - a ∧ j = j + b - b then
              (Nat.choose xDeg a : R) * (Nat.choose (j + b) b : R) * coeffY.coeff xDeg
            else 0
          else 0) =
          if xDeg = i + a then
            (Nat.choose (i + a) a : R) * (Nat.choose (j + b) b : R) *
              coeffY.coeff (i + a)
          else 0 := by
      intro xDeg
      by_cases hxEq : xDeg = i + a
      · subst xDeg
        have ha : a ≤ i + a := by omega
        have hi : i = i + a - a := by omega
        have hjy : j = j + b - b := by omega
        rw [if_pos ha, if_pos ⟨hi, hjy⟩, if_pos rfl]
      · by_cases ha : a ≤ xDeg
        · have hi_ne : i ≠ xDeg - a := by
            intro hi
            have : xDeg = i + a := by omega
            exact hxEq this
          simp [ha, hxEq, hi_ne]
        · simp [ha, hxEq]
    rw [List.foldl_congr_of_mem
      (List.range' 0 coeffY.val.size) acc
      (fun _acc' xDeg _hxDeg ↦ by rw [hcontrib xDeg])]
    rw [DenseMatrix.foldl_range_one_special
      (F := R) (pivot := i + a)
      ((Nat.choose (i + a) a : R) * (Nat.choose (j + b) b : R) *
        coeffY.coeff (i + a)) 0 coeffY.val.size acc]
    simp
  · have hcontrib : ∀ xDeg,
        (if a ≤ xDeg then
            if i = xDeg - a ∧ j = yDeg - b then
              (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
            else 0
          else 0) = (0 : R) := by
      intro xDeg
      by_cases ha : a ≤ xDeg
      · have hnot : ¬(i = xDeg - a ∧ j = yDeg - b) := by
          rintro ⟨_hi, hj⟩
          have : yDeg = j + b := by omega
          exact hyTarget this
        simp [ha, hnot]
      · simp [ha]
    rw [List.foldl_congr_of_mem
      (List.range' 0 coeffY.val.size) acc
      (fun _acc' xDeg _hxDeg ↦ by rw [hcontrib xDeg])]
    simp [hyTarget]

/-- The fixed coefficient of the executable Hasse term list has the closed
coefficient-shift formula. -/
theorem hasseDerivativeTermList_coeff_value {R : Type*} [Semiring R]
    (a b i j : Nat) (Q : CBivariate R) :
    (hasseDerivativeTermList a b Q).foldl
        (fun acc term ↦ acc + if i = term.xDegree ∧ j = term.yDegree then term.coeff else 0)
        0 =
      (Nat.choose (i + a) a : R) * (Nat.choose (j + b) b : R) *
        coeff Q (i + a) (j + b) := by
  rw [hasseDerivativeTermList_coeff_fold]
  let source :=
    if i + a < (Q.val.coeff (j + b)).val.size then
      (Nat.choose (i + a) a : R) * (Nat.choose (j + b) b : R) *
        (Q.val.coeff (j + b)).coeff (i + a)
    else 0
  have houterStep :
      (List.range' 0 Q.val.size).foldl
          (fun acc yDeg ↦
            let coeffY := Q.val.coeff yDeg
            if b ≤ yDeg then
              (List.range' 0 coeffY.val.size).foldl
                (fun acc xDeg ↦
                  if a ≤ xDeg then
                    acc +
                      if i = xDeg - a ∧ j = yDeg - b then
                        (Nat.choose xDeg a : R) * (Nat.choose yDeg b : R) * coeffY.coeff xDeg
                      else 0
                  else acc)
                acc
            else acc)
          0 =
        (List.range' 0 Q.val.size).foldl
          (fun acc yDeg ↦ acc + if yDeg = j + b then source else 0)
          0 := by
    apply List.foldl_congr_of_mem
    intro acc yDeg
    by_cases hy : b ≤ yDeg
    · rw [if_pos hy]
      rw [hasseDerivativeTermList_coeff_inner_fold a b i j yDeg (Q.val.coeff yDeg) acc hy]
      by_cases hyTarget : yDeg = j + b
      · subst yDeg
        simp [source]
      · simp [hyTarget]
    · rw [if_neg hy]
      have hyTarget : yDeg ≠ j + b := by
        intro htarget
        subst yDeg
        exact hy (by omega)
      simp [hyTarget]
  rw [houterStep]
  rw [DenseMatrix.foldl_range_one_special (F := R) (pivot := j + b) source 0 Q.val.size 0]
  by_cases hyIn : j + b < Q.val.size
  · have hin : 0 ≤ j + b ∧ j + b < 0 + Q.val.size := by omega
    simp [hin, hyIn]
    change source =
      (Nat.choose (i + a) a : R) * (Nat.choose (j + b) b : R) *
        (Q.val.coeff (j + b)).coeff (i + a)
    by_cases hxIn : i + a < (Q.val.coeff (j + b)).val.size
    · dsimp only [source]
      rw [if_pos hxIn]
    · have hxLe : (Q.val.coeff (j + b)).val.size ≤ i + a := Nat.le_of_not_gt hxIn
      dsimp only [source]
      rw [if_neg hxIn]
      rw [CPolynomial.coeff_eq_zero_of_size_le (Q.val.coeff (j + b)) hxLe]
      simp
  · have hyLe : Q.val.size ≤ j + b := Nat.le_of_not_gt hyIn
    rw [coeff_eq_zero_of_y_size_le Q hyLe]
    simp [source, hyIn]

/-- Coefficients of the executable Hasse derivative are shifted source
coefficients scaled by the corresponding binomial factors. -/
theorem hasseDerivative_coeff {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b i j : Nat) (Q : CBivariate R) :
    coeff (hasseDerivative a b Q) i j =
      (Nat.choose (i + a) a : R) * (Nat.choose (j + b) b : R) *
        coeff Q (i + a) (j + b) := by
  unfold hasseDerivative
  rw [hasseDerivativeFromTerms_coeff]
  exact hasseDerivativeTermList_coeff_value a b i j Q

/-- Hasse derivatives are additive. -/
theorem hasseDerivative_add {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : Nat) (P Q : CBivariate R) :
    hasseDerivative a b (P + Q) = hasseDerivative a b P + hasseDerivative a b Q := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff]
  rw [coeff_add]
  rw [coeff_add]
  rw [hasseDerivative_coeff, hasseDerivative_coeff]
  rw [mul_add]

/-- The Hasse derivative of zero is zero. -/
theorem hasseDerivative_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : Nat) :
    hasseDerivative a b (0 : CBivariate R) = 0 := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff, coeff_zero, coeff_zero]
  simp

/-- Hasse derivative of a single bivariate monomial. -/
theorem hasseDerivative_monomialXY {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b n m : Nat) (c : R) :
    hasseDerivative a b (monomialXY n m c) =
      if a ≤ n ∧ b ≤ m then
        monomialXY (n - a) (m - b)
          ((Nat.choose n a : R) * (Nat.choose m b : R) * c)
      else 0 := by
  rw [eq_iff_coeff]
  intro i j
  rw [hasseDerivative_coeff]
  by_cases hle : a ≤ n ∧ b ≤ m
  · rw [if_pos hle, coeff_monomialXY, coeff_monomialXY]
    by_cases hmatch : i = n - a ∧ j = m - b
    · rcases hmatch with ⟨hi, hj⟩
      have hia : i + a = n := by omega
      have hjb : j + b = m := by omega
      have hsource : i + a = n ∧ j + b = m := ⟨hia, hjb⟩
      rw [if_pos hsource, if_pos ⟨hi, hj⟩]
      rw [hia, hjb]
    · rw [if_neg hmatch]
      have hsource : ¬(i + a = n ∧ j + b = m) := by
        rintro ⟨hia, hjb⟩
        apply hmatch
        constructor <;> omega
      rw [if_neg hsource]
      simp
  · rw [if_neg hle, coeff_monomialXY, coeff_zero]
    have hsource : ¬(i + a = n ∧ j + b = m) := by
      rintro ⟨hia, hjb⟩
      apply hle
      constructor <;> omega
    rw [if_neg hsource]
    simp

/-- Full evaluation is additive. -/
theorem evalEval_add {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x y : R) (P Q : CBivariate R) :
    evalEval x y (P + Q) = evalEval x y P + evalEval x y Q := by
  rw [evalEval_toPoly, evalEval_toPoly, evalEval_toPoly, toPoly_add]
  simp [Polynomial.evalEval, Polynomial.eval_add]

/-- Full evaluation of zero is zero. -/
theorem evalEval_zero {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x y : R) : evalEval x y (0 : CBivariate R) = 0 := by
  rw [evalEval_toPoly, toPoly_zero]
  simp [Polynomial.evalEval]

/-- Full evaluation of a bivariate monomial has the expected closed form. -/
theorem evalEval_monomialXY {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (x y c : R) (n m : Nat) :
    evalEval x y (monomialXY n m c) = c * x ^ n * y ^ m := by
  rw [evalEval_toPoly, monomialXY_toPoly]
  simp [Polynomial.evalEval, Polynomial.eval_monomial]

/-- Evaluating the materialized derivative-term fold matches the direct scalar fold. -/
theorem hasseDerivativeTerms_eval_aux {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (x y : R) (terms : List (HasseTerm R)) (acc : CBivariate R) :
    evalEval x y (terms.foldl
      (fun out term ↦ out + monomialXY term.xDegree term.yDegree term.coeff) acc) =
    terms.foldl
      (fun z term ↦ z + term.coeff * x ^ term.xDegree * y ^ term.yDegree)
      (evalEval x y acc) := by
  induction terms generalizing acc with
  | nil => rfl
  | cons term terms ih =>
      simp [List.foldl]
      rw [ih]
      congr 1
      rw [evalEval_add, evalEval_monomialXY]

/-- Evaluating a materialized derivative-term polynomial matches direct term evaluation. -/
theorem hasseDerivativeFromTerms_eval {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (x y : R) (terms : List (HasseTerm R)) :
    evalEval x y (hasseDerivativeFromTerms terms) =
      hasseDerivativeEvalFromTerms terms x y := by
  unfold hasseDerivativeFromTerms hasseDerivativeEvalFromTerms
  rw [hasseDerivativeTerms_eval_aux]
  rw [evalEval_zero]

/-- Correctness of executable Hasse derivative evaluation. -/
theorem hasseDerivative_eval_eq_eval {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : Nat) (x y : R) (Q : CBivariate R) :
    evalEval x y (hasseDerivative a b Q) = hasseDerivativeEval a b x y Q := by
  unfold hasseDerivative hasseDerivativeEval
  exact hasseDerivativeFromTerms_eval x y (hasseDerivativeTerms a b Q).toList

/-- Direct Hasse evaluation is additive in the input polynomial. -/
theorem hasseDerivativeEval_add {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : Nat) (x y : R) (P Q : CBivariate R) :
    hasseDerivativeEval a b x y (P + Q) =
      hasseDerivativeEval a b x y P + hasseDerivativeEval a b x y Q := by
  rw [← hasseDerivative_eval_eq_eval a b x y (P + Q)]
  rw [hasseDerivative_add]
  rw [evalEval_add]
  rw [hasseDerivative_eval_eq_eval, hasseDerivative_eval_eq_eval]

/-- Direct Hasse evaluation of zero is zero. -/
theorem hasseDerivativeEval_zero {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : Nat) (x y : R) :
    hasseDerivativeEval a b x y (0 : CBivariate R) = 0 := by
  rw [← hasseDerivative_eval_eq_eval a b x y (0 : CBivariate R)]
  rw [hasseDerivative_zero, evalEval_zero]

end CBivariate

end CompPoly
