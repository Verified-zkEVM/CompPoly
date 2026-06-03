/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.BatchEval.Context
import CompPoly.Univariate.Derivative
import CompPoly.Univariate.Vanishing

/-!
# Coefficient-Form Interpolation from a Vanishing Polynomial

Build the coefficient polynomial interpolating packed points from the node
vanishing polynomial `G = ∏ᵢ (X - xᵢ)` using the formula
`R = ∑ᵢ yᵢ / G'(xᵢ) * G / (X - xᵢ)`.
-/

namespace CompPoly

namespace CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem eval_zero (x : F) :
    CPolynomial.eval x (0 : CPolynomial F) = 0 := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_zero, Polynomial.eval_zero]

private theorem eval_add (x : F) (p q : CPolynomial F) :
    CPolynomial.eval x (p + q) =
      CPolynomial.eval x p + CPolynomial.eval x q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

private theorem linearFactor_toPoly (x : F) :
    (CPolynomial.linearFactor x).toPoly =
      (Polynomial.X - Polynomial.C x : Polynomial F) := by
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly]
  rw [show Polynomial.C (-x) + Polynomial.X =
      (Polynomial.X - Polynomial.C x : Polynomial F) by
    rw [Polynomial.C_neg]
    ring]

private theorem linearFactor_monic (x : F) :
    (CPolynomial.linearFactor x).monic := by
  rw [CPolynomial.monic_toPoly_iff]
  rw [linearFactor_toPoly]
  exact Polynomial.monic_X_sub_C x

/-- Synthetic quotient by the monic linear factor `X - x`.

This is the quotient part of division by `X - x`, computed in one high-to-low
coefficient pass. When `x` is a root of `p`, it is exactly `p / (X - x)`.
-/
def divByLinearFactor (p : CPolynomial F) (x : F) : CPolynomial F :=
  let quotientSize := p.val.size - 1
  let coeffs :=
    ((List.range quotientSize).reverse.foldl
      (fun state j ↦
        let nextCoeff := p.coeff (j + 1) + x * state.1
        (nextCoeff, nextCoeff :: state.2))
      (0, ([] : List F))).2
  CPolynomial.ofArray coeffs.toArray

omit [BEq F] [LawfulBEq F] in
private theorem divByLinearFactor_fold_tail_of_le
    (p : CPolynomial F) (x : F) (n i : Nat) (state : F × List F)
    (hstate : state.2.getD 0 0 = state.1) (hi : n ≤ i) :
    ((List.range n).reverse.foldl
      (fun state j ↦
        let nextCoeff := p.coeff (j + 1) + x * state.1
        (nextCoeff, nextCoeff :: state.2))
      state).2.getD i 0 = state.2.getD (i - n) 0 := by
  induction n generalizing i state with
  | zero =>
      simp
  | succ n ih =>
      let nextCoeff := p.coeff (n + 1) + x * state.1
      let state' : F × List F := (nextCoeff, nextCoeff :: state.2)
      have hstate' : state'.2.getD 0 0 = state'.1 := by simp [state']
      have hni : n ≤ i := by omega
      have ih' := ih i state' hstate' hni
      simp [List.range_succ, state', nextCoeff] at ih' ⊢
      by_cases hi_eq : i = n
      · subst i
        omega
      · have hsub : i - n = (i - (n + 1)) + 1 := by omega
        rw [ih', hsub]
        simp

omit [BEq F] [LawfulBEq F] in
private theorem divByLinearFactor_fold_coeff_rec_aux
    (p : CPolynomial F) (x : F) (n i : Nat) (state : F × List F)
    (hstate : state.2.getD 0 0 = state.1) (hi : i < n) :
    ((List.range n).reverse.foldl
      (fun state j ↦
        let nextCoeff := p.coeff (j + 1) + x * state.1
        (nextCoeff, nextCoeff :: state.2))
      state).2.getD i 0 =
      p.coeff (i + 1) + x *
        ((List.range n).reverse.foldl
          (fun state j ↦
            let nextCoeff := p.coeff (j + 1) + x * state.1
            (nextCoeff, nextCoeff :: state.2))
          state).2.getD (i + 1) 0 := by
  induction n generalizing i state with
  | zero =>
      omega
  | succ n ih =>
      let nextCoeff := p.coeff (n + 1) + x * state.1
      let state' : F × List F := (nextCoeff, nextCoeff :: state.2)
      have hstate' : state'.2.getD 0 0 = state'.1 := by simp [state']
      by_cases hin : i < n
      · have ih' := ih i state' hstate' hin
        simp [List.range_succ, state', nextCoeff] at ih' ⊢
        simpa using ih'
      · have hi_eq : i = n := by omega
        subst i
        have hleft := divByLinearFactor_fold_tail_of_le p x n n state' hstate' (Nat.le_refl n)
        have hright := divByLinearFactor_fold_tail_of_le p x n (n + 1) state' hstate' (by omega)
        simp [List.range_succ, state', nextCoeff] at hleft hright ⊢
        rw [hleft, hright]
        simpa using congrArg (fun t ↦ p.coeff (n + 1) + x * t) hstate.symm

omit [BEq F] [LawfulBEq F] in
private theorem divByLinearFactor_fold_coeff_rec
    (p : CPolynomial F) (x : F) (n i : Nat) (hi : i < n) :
    ((List.range n).reverse.foldl
      (fun state j ↦
        let nextCoeff := p.coeff (j + 1) + x * state.1
        (nextCoeff, nextCoeff :: state.2))
      (0, ([] : List F))).2.getD i 0 =
      p.coeff (i + 1) + x *
        ((List.range n).reverse.foldl
          (fun state j ↦
            let nextCoeff := p.coeff (j + 1) + x * state.1
            (nextCoeff, nextCoeff :: state.2))
          (0, ([] : List F))).2.getD (i + 1) 0 :=
  divByLinearFactor_fold_coeff_rec_aux p x n i (0, []) (by simp) hi

omit [BEq F] [LawfulBEq F] in
private theorem divByLinearFactor_fold_coeff_eq_zero_of_le
    (p : CPolynomial F) (x : F) (n i : Nat) (hi : n ≤ i) :
    ((List.range n).reverse.foldl
      (fun state j ↦
        let nextCoeff := p.coeff (j + 1) + x * state.1
        (nextCoeff, nextCoeff :: state.2))
      (0, ([] : List F))).2.getD i 0 = 0 := by
  rw [divByLinearFactor_fold_tail_of_le p x n i (0, []) (by simp) hi]
  simp

private theorem divByLinearFactor_coeff_rec
    (p : CPolynomial F) (x : F) {i : Nat} (hi : i < p.val.size - 1) :
    (divByLinearFactor p x).coeff i =
      p.coeff (i + 1) + x * (divByLinearFactor p x).coeff (i + 1) := by
  unfold divByLinearFactor
  rw [CPolynomial.coeff_ofArray]
  rw [CPolynomial.coeff_ofArray]
  simpa using divByLinearFactor_fold_coeff_rec p x (p.val.size - 1) i hi

private theorem divByLinearFactor_coeff_eq_zero_of_le
    (p : CPolynomial F) (x : F) {i : Nat} (hi : p.val.size - 1 ≤ i) :
    (divByLinearFactor p x).coeff i = 0 := by
  unfold divByLinearFactor
  rw [CPolynomial.coeff_ofArray]
  simpa using divByLinearFactor_fold_coeff_eq_zero_of_le p x (p.val.size - 1) i hi

private theorem toPoly_natDegree_lt_succ_of_size_pred_le
    (p : CPolynomial F) {i : Nat} (hi : p.val.size - 1 ≤ i) :
    p.toPoly.natDegree < i + 1 := by
  have hnat := CPolynomial.natDegree_toPoly p
  cases hs : p.val.size with
  | zero =>
      simp [CPolynomial.natDegree, hs] at hnat
      omega
  | succ n =>
      simp [CPolynomial.natDegree, hs] at hnat
      omega

/-- Synthetic division by `X - x` agrees with generic monic division. -/
theorem divByLinearFactor_eq_divByMonic (p : CPolynomial F) (x : F) :
    divByLinearFactor p x = p.divByMonic (linearFactor x) := by
  apply (CPolynomial.eq_iff_coeff).2
  intro i
  rw [CPolynomial.coeff_toPoly]
  rw [CPolynomial.coeff_toPoly (p.divByMonic (linearFactor x)) i]
  rw [CPolynomial.divByMonic_toPoly_eq_divByMonic
    p (linearFactor x) (linearFactor_monic x)]
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly]
  rw [show Polynomial.C (-x) + Polynomial.X =
      (Polynomial.X - Polynomial.C x : Polynomial F) by
    rw [Polynomial.C_neg]
    ring]
  let q := divByLinearFactor p x
  let d := p.toPoly /ₘ (Polynomial.X - Polynomial.C x)
  change q.toPoly.coeff i = d.coeff i
  have hcoeff : ∀ m i,
      m = p.val.size - 1 - i →
        q.coeff i = d.coeff i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro i hm
        by_cases hi : p.val.size - 1 ≤ i
        · have hq : q.coeff i = 0 := by
            simpa [q] using divByLinearFactor_coeff_eq_zero_of_le p x hi
          have hd : d.coeff i = 0 := by
            change (p.toPoly /ₘ (Polynomial.X - Polynomial.C x)).coeff i = 0
            rw [Polynomial.coeff_divByMonic_X_sub_C]
            apply Finset.sum_eq_zero
            intro k hk
            have hk_bounds := Finset.mem_Icc.mp hk
            have hdeg_lt := toPoly_natDegree_lt_succ_of_size_pred_le p hi
            omega
          rw [hq, hd]
        · have hi_lt : i < p.val.size - 1 := Nat.lt_of_not_ge hi
          have hqrec : q.coeff i = p.coeff (i + 1) + x * q.coeff (i + 1) := by
            simpa [q] using divByLinearFactor_coeff_rec p x hi_lt
          have hdrec : d.coeff i = p.coeff (i + 1) + x * d.coeff (i + 1) := by
            change (p.toPoly /ₘ (Polynomial.X - Polynomial.C x)).coeff i =
              p.coeff (i + 1) +
                x * (p.toPoly /ₘ (Polynomial.X - Polynomial.C x)).coeff (i + 1)
            rw [Polynomial.coeff_divByMonic_X_sub_C_rec]
            rw [← CPolynomial.coeff_toPoly p (i + 1)]
          rw [hqrec, hdrec]
          rw [ih (p.val.size - 1 - (i + 1)) (by omega) (i + 1) rfl]
  rw [← CPolynomial.coeff_toPoly]
  exact hcoeff (p.val.size - 1 - i) i rfl

private theorem divByLinearFactor_toPoly (p : CPolynomial F) (x : F) :
    (divByLinearFactor p x).toPoly =
      p.toPoly /ₘ (Polynomial.X - Polynomial.C x) := by
  rw [divByLinearFactor_eq_divByMonic]
  rw [CPolynomial.divByMonic_toPoly_eq_divByMonic p
    (linearFactor x) (linearFactor_monic x)]
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly]
  rw [show Polynomial.C (-x) + Polynomial.X =
      (Polynomial.X - Polynomial.C x : Polynomial F) by
    rw [Polynomial.C_neg]
    ring]

private theorem eval_divByLinearFactor_eq_zero_of_root_of_ne
    (p : CPolynomial F) {a x : F}
    (ha : CPolynomial.eval a p = 0) (hx : CPolynomial.eval x p = 0)
    (hxa : x ≠ a) :
    CPolynomial.eval x (divByLinearFactor p a) = 0 := by
  have haRoot : p.toPoly.IsRoot a := by
    rw [Polynomial.IsRoot, ← CPolynomial.eval_toPoly]
    exact ha
  have hmul :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot (a := a) (p := p.toPoly)).2 haRoot
  have heval := congrArg (fun q : Polynomial F ↦ Polynomial.eval x q) hmul
  change Polynomial.eval x
      ((Polynomial.X - Polynomial.C a) * (p.toPoly /ₘ (Polynomial.X - Polynomial.C a))) =
    Polynomial.eval x p.toPoly at heval
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
  have hxPoly : Polynomial.eval x p.toPoly = 0 := by
    rw [← CPolynomial.eval_toPoly]
    exact hx
  rw [hxPoly] at heval
  have hfactor : x - a ≠ 0 := sub_ne_zero.mpr hxa
  rw [CPolynomial.eval_toPoly, divByLinearFactor_toPoly]
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hfactor heval

private theorem eval_divByLinearFactor_self_eq_derivative
    (p : CPolynomial F) {x : F} (hx : CPolynomial.eval x p = 0) :
    CPolynomial.eval x (divByLinearFactor p x) =
      CPolynomial.eval x (CPolynomial.derivative p) := by
  have hxRoot : p.toPoly.IsRoot x := by
    rw [Polynomial.IsRoot, ← CPolynomial.eval_toPoly]
    exact hx
  have hmul :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot (a := x) (p := p.toPoly)).2 hxRoot
  have hderiv := congrArg Polynomial.derivative hmul
  have heval := congrArg (fun q : Polynomial F ↦ Polynomial.eval x q) hderiv
  change Polynomial.eval x
      (Polynomial.derivative
        ((Polynomial.X - Polynomial.C x) * (p.toPoly /ₘ (Polynomial.X - Polynomial.C x)))) =
    Polynomial.eval x (Polynomial.derivative p.toPoly) at heval
  rw [Polynomial.derivative_mul] at heval
  change Polynomial.eval x
      (Polynomial.derivative (Polynomial.X - Polynomial.C x) *
          (p.toPoly /ₘ (Polynomial.X - Polynomial.C x)) +
        (Polynomial.X - Polynomial.C x) *
          Polynomial.derivative (p.toPoly /ₘ (Polynomial.X - Polynomial.C x))) =
    Polynomial.eval x (Polynomial.derivative p.toPoly) at heval
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul] at heval
  rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C] at heval
  simp at heval
  rw [CPolynomial.eval_toPoly, divByLinearFactor_toPoly]
  rw [CPolynomial.eval_toPoly, CPolynomial.derivative_toPoly]
  exact heval

private theorem eval_foldl_add_eq_eval_add_sum (x : F) (xs : List Nat)
    (f : Nat → CPolynomial F) (acc : CPolynomial F) :
    CPolynomial.eval x (xs.foldl (fun acc i ↦ acc + f i) acc) =
      CPolynomial.eval x acc + (xs.map fun i ↦ CPolynomial.eval x (f i)).sum := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      rw [List.foldl_cons, ih, eval_add]
      rw [List.map_cons, List.sum_cons]
      ring

omit [BEq F] [LawfulBEq F] in
private theorem list_sum_range_eq_single_of
    (f : Nat → F) {n k : Nat} (hk : k < n)
    (hzero : ∀ i, i < n → i ≠ k → f i = 0) :
    ((List.range n).map f).sum = f k := by
  induction n with
  | zero =>
      omega
  | succ n ih =>
      rw [List.sum_range_succ]
      by_cases hk_last : k = n
      · subst k
        have hprev : ((List.range n).map f).sum = 0 := by
          apply List.sum_eq_zero
          intro y hy
          rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩
          have hi_lt : i < n := List.mem_range.mp hi
          exact hzero i (by omega) (by omega)
        rw [hprev]
        simp
      · have hk_lt : k < n := by omega
        rw [ih hk_lt (fun i hi hine ↦ hzero i (by omega) hine)]
        rw [hzero n (Nat.lt_succ_self n) (by omega)]
        simp

private theorem vanishingPolynomialArray_toPoly_list
    (xs : List F) (acc : CPolynomial F) :
    (xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc).toPoly =
      acc.toPoly * (xs.map fun x ↦ (Polynomial.X - Polynomial.C x : Polynomial F)).prod := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, CPolynomial.toPoly_mul, linearFactor_toPoly]
      simp only [List.map_cons, List.prod_cons]
      ring

private theorem vanishingPolynomialArray_toPoly (xs : Array F) :
    (CPolynomial.vanishingPolynomialArray xs).toPoly =
      (((xs.toList : Multiset F).map
        fun x ↦ (Polynomial.X - Polynomial.C x : Polynomial F))).prod := by
  rw [CPolynomial.vanishingPolynomialArray]
  have hlist := vanishingPolynomialArray_toPoly_list xs.toList (1 : CPolynomial F)
  simpa [CPolynomial.toPoly_one, Multiset.map_coe, Multiset.prod_coe] using hlist

private theorem derivative_vanishingPolynomialArray_eval_ne_zero_of_nodup
    [DecidableEq F] (xs : Array F) (hnodup : xs.toList.Nodup) {x : F}
    (hx : x ∈ xs.toList) :
    CPolynomial.eval x
        (CPolynomial.derivative (CPolynomial.vanishingPolynomialArray xs)) ≠ 0 := by
  have hxMultiset : x ∈ (xs.toList : Multiset F) := by
    simpa using hx
  have hderiv :=
    Polynomial.eval_multiset_prod_X_sub_C_derivative
      (S := (xs.toList : Multiset F)) (r := x) hxMultiset
  rw [← vanishingPolynomialArray_toPoly xs] at hderiv
  rw [← CPolynomial.derivative_toPoly] at hderiv
  rw [← CPolynomial.eval_toPoly] at hderiv
  rw [hderiv]
  apply Multiset.prod_ne_zero
  intro hzero
  rcases Multiset.mem_map.mp hzero with ⟨a, ha, hxa⟩
  have hnodupMultiset : (xs.toList : Multiset F).Nodup := by
    simpa using hnodup
  have hane : a ≠ x := ((hnodupMultiset.mem_erase_iff).mp ha).1
  exact hane (sub_eq_zero.mp hxa).symm

/-- One coefficient-form interpolation term from a packed point and `G'(xᵢ)`. -/
def interpolationTermWithVanishing
    (G : CPolynomial F) (point : F × F) (derivativeValue : F) : CPolynomial F :=
  CPolynomial.C (point.2 / derivativeValue) *
    divByLinearFactor G point.1

/-- Coefficient-form interpolation from packed points and an already-built node
vanishing polynomial. The supplied batch evaluator is used only for the
`G'` evaluations at the interpolation nodes. -/
def interpolateCoefficientFormWithVanishing
    (E : CPolynomial.BatchEvalContext F)
    (G : CPolynomial F) (points : Array (F × F)) : CPolynomial F :=
  let derivativeValues :=
    E.evalBatchWith (CPolynomial.derivative G) (points.map fun point ↦ point.1)
  (List.range points.size).foldl
    (fun acc i ↦
      acc + interpolationTermWithVanishing G
        (points.getD i (0, 0)) (derivativeValues.getD i 0))
    0

/-- Coefficient-form interpolation from packed points using a vanishing-polynomial
context and a batch-evaluation context. -/
def interpolateCoefficientForm
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (points : Array (F × F)) : CPolynomial F :=
  interpolateCoefficientFormWithVanishing E
    (V.vanishingPolynomial (points.map fun point ↦ point.1)) points

/-- Coefficient-form interpolation evaluates to the packed values at distinct nodes. -/
theorem interpolateCoefficientForm_eval_point [DecidableEq F]
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    {points : Array (F × F)}
    (hdistinct : (points.toList.map fun point ↦ point.1).Nodup)
    {point : F × F} (hpoint : point ∈ points.toList) :
    CPolynomial.eval point.1 (CPolynomial.interpolateCoefficientForm V E points) =
      point.2 := by
  rcases List.getElem_of_mem hpoint with ⟨k, hkList, hget⟩
  have hk : k < points.size := by
    simpa using hkList
  have hpoint_at : points[k] = point := by
    simpa [Array.getElem_toList] using hget
  let xs : Array F := points.map fun point ↦ point.1
  let G : CPolynomial F := V.vanishingPolynomial xs
  let derivativeValues : Array F :=
    E.evalBatchWith (CPolynomial.derivative G) xs
  let term : Nat → CPolynomial F := fun i ↦
    interpolationTermWithVanishing G
      (points.getD i (0, 0)) (derivativeValues.getD i 0)
  let termEval : Nat → F := fun i ↦ CPolynomial.eval point.1 (term i)
  have hG : G = CPolynomial.vanishingPolynomialArray xs := by
    simpa [G, xs] using V.correct xs
  have hnodes : xs.toList.Nodup := by
    simpa [xs, Array.toList_map] using hdistinct
  have hpoint_mem_xs : point.1 ∈ xs.toList := by
    have hmem : point.1 ∈ points.toList.map (fun point ↦ point.1) :=
      List.mem_map.mpr ⟨point, hpoint, rfl⟩
    simpa [xs, Array.toList_map] using hmem
  have hroot_point : CPolynomial.eval point.1 G = 0 := by
    rw [hG]
    exact CPolynomial.eval_vanishingPolynomialArray_eq_zero_of_mem xs hpoint_mem_xs
  have hroot_idx : ∀ (i : Nat) (hi : i < points.size),
      CPolynomial.eval points[i].1 G = 0 := by
    intro i hi
    rw [hG]
    apply CPolynomial.eval_vanishingPolynomialArray_eq_zero_of_mem xs
    have hmemPoint : points[i] ∈ points.toList :=
      Array.getElem_mem_toList hi
    have hmem : points[i].1 ∈ points.toList.map (fun point ↦ point.1) :=
      List.mem_map.mpr ⟨points[i], hmemPoint, rfl⟩
    simpa [xs, Array.toList_map] using hmem
  have hne_idx : ∀ (i : Nat) (hi : i < points.size),
      i ≠ k → point.1 ≠ points[i].1 := by
    intro i hi hik hEq
    have hiList : i < points.toList.length := by
      simpa using hi
    have hkList' : k < points.toList.length := by
      simpa using hk
    have hiMap : i < (points.toList.map fun point ↦ point.1).length := by
      simpa using hiList
    have hkMap : k < (points.toList.map fun point ↦ point.1).length := by
      simpa using hkList'
    have hmap_eq :
        (points.toList.map fun point ↦ point.1)[i]'hiMap =
          (points.toList.map fun point ↦ point.1)[k]'hkMap := by
      rw [List.getElem_map, List.getElem_map]
      simpa [Array.getElem_toList, hget] using hEq.symm
    have hik' : i = k :=
      (hdistinct.getElem_inj_iff (i := i) (hi := hiMap) (j := k) (hj := hkMap)).mp hmap_eq
    exact hik hik'
  have hderivative_get :
      derivativeValues.getD k 0 =
        CPolynomial.eval point.1 (CPolynomial.derivative G) := by
    dsimp [derivativeValues]
    rw [E.correct, CPolynomial.evalBatch]
    have hkxs : k < xs.size := by
      simp [xs, hk]
    rw [Array.getD_map_of_lt xs
      (fun x ↦ CPolynomial.eval x (CPolynomial.derivative G)) 0 hkxs]
    have hxs_at : xs[k] = point.1 := by
      simp [xs, hpoint_at]
    rw [hxs_at]
  have hderiv_ne :
      CPolynomial.eval point.1 (CPolynomial.derivative G) ≠ 0 := by
    rw [hG]
    exact derivative_vanishingPolynomialArray_eval_ne_zero_of_nodup
      xs hnodes hpoint_mem_xs
  have hterm_zero : ∀ i, i < points.size → i ≠ k → termEval i = 0 := by
    intro i hi hik
    have hgetD : points.getD i (0, 0) = points[i] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      simp
    have hquot :
        CPolynomial.eval point.1
          (CPolynomial.divByLinearFactor G points[i].1) = 0 :=
      eval_divByLinearFactor_eq_zero_of_root_of_ne
        (p := G) (a := points[i].1) (x := point.1)
        (hroot_idx i hi) hroot_point (hne_idx i hi hik)
    change CPolynomial.eval point.1
      (interpolationTermWithVanishing G
        (points.getD i (0, 0)) (derivativeValues.getD i 0)) = 0
    rw [hgetD]
    unfold interpolationTermWithVanishing
    rw [CPolynomial.eval_mul, CPolynomial.eval_C, hquot]
    simp
  have hterm_target : termEval k = point.2 := by
    have hgetD : points.getD k (0, 0) = points[k] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk]
      simp
    change CPolynomial.eval point.1
      (interpolationTermWithVanishing G
        (points.getD k (0, 0)) (derivativeValues.getD k 0)) = point.2
    rw [hgetD, hpoint_at]
    unfold interpolationTermWithVanishing
    rw [CPolynomial.eval_mul, CPolynomial.eval_C]
    rw [eval_divByLinearFactor_self_eq_derivative G hroot_point]
    rw [hderivative_get]
    exact div_mul_cancel₀ point.2 hderiv_ne
  unfold CPolynomial.interpolateCoefficientForm CPolynomial.interpolateCoefficientFormWithVanishing
  change CPolynomial.eval point.1
    ((List.range points.size).foldl (fun acc i ↦ acc + term i) 0) = point.2
  rw [eval_foldl_add_eq_eval_add_sum point.1 (List.range points.size) term
    (0 : CPolynomial F), eval_zero]
  rw [_root_.zero_add]
  change ((List.range points.size).map termEval).sum = point.2
  rw [list_sum_range_eq_single_of termEval hk hterm_zero]
  exact hterm_target

end CPolynomial

end CompPoly
