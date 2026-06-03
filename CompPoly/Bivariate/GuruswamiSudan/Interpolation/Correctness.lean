/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.FactorMonic
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Shared Guruswami-Sudan Interpolation Correctness

Backend-neutral correctness facts for executable interpolation helpers.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- The executable witness recognizer is equivalent to the semantic witness contract. -/
theorem interpolationWitnessIsValidBool_iff {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {points : Array (F × F)} {params : GSInterpParams} {Q : CBivariate F} :
    interpolationWitnessIsValidBool points params Q = true ↔
      ValidInterpolationWitness points params Q := by
  have horders_mem : ∀ m a b,
      a + b < m → (a, b) ∈ (CBivariate.derivativeOrders m).toList := by
    intro m a b hlt
    simp [CBivariate.derivativeOrders, CBivariate.derivativeOrderGrid]
    omega
  have horders_sound : ∀ m order,
      order ∈ (CBivariate.derivativeOrders m).toList → order.1 + order.2 < m := by
    intro m order h
    simp [CBivariate.derivativeOrders] at h
    exact h.2
  have hpoint : ∀ x y m,
      CBivariate.multiplicityAtLeastBool Q x y m = true ↔
        CBivariate.HasMultiplicityAtLeast Q x y m := by
    intro x y m
    simp [CBivariate.multiplicityAtLeastBool, CBivariate.HasMultiplicityAtLeast]
    constructor
    · intro h a b hab
      rcases List.getElem_of_mem (horders_mem m a b hab) with ⟨i, hi, hget⟩
      have horder : (CBivariate.derivativeOrders m)[i] = (a, b) := by
        simpa [Array.getElem_toList] using hget
      have hzero := h i (by simpa using hi)
      simpa [horder] using hzero
    · intro h i hi
      exact h _ _ (horders_sound m _ (Array.getElem_mem_toList hi))
  have hbatch :
      CBivariate.satisfiesMultiplicityConstraintsBool Q points params.multiplicity = true ↔
        CBivariate.SatisfiesMultiplicityConstraints Q points params.multiplicity := by
    simp [CBivariate.satisfiesMultiplicityConstraintsBool,
      CBivariate.SatisfiesMultiplicityConstraints]
    constructor
    · intro h x y hmem
      have hmemList : (x, y) ∈ points.toList := by
        simpa only [Array.mem_def] using hmem
      rcases List.getElem_of_mem hmemList with ⟨i, hi, hget⟩
      have hpt : points[i] = (x, y) := by
        simpa [Array.getElem_toList] using hget
      have hthis := h i (by simpa using hi)
      exact (hpoint x y params.multiplicity).1 (by simpa [hpt] using hthis)
    · intro h i hi
      apply (hpoint points[i].1 points[i].2 params.multiplicity).2
      apply h points[i].1 points[i].2
      simpa only [Array.mem_def] using (Array.getElem_mem_toList hi)
  simp [interpolationWitnessIsValidBool, ValidInterpolationWitness, hbatch]
  tauto

private noncomputable def lowMessageYPolynomial {F : Type*} [Field F]
    (points : Array (F × F)) (multiplicity : Nat) : Polynomial F :=
  points.toList.foldl
    (fun P point ↦ P * ((Polynomial.X - Polynomial.C point.2) ^ multiplicity)) 1

private theorem cbivariate_toPoly_pow {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (n : Nat) :
    CBivariate.toPoly (Q ^ n) = CBivariate.toPoly Q ^ n := by
  induction n with
  | zero =>
      simp [CBivariate.toPoly_one]
  | succ n ih =>
      rw [pow_succ, CBivariate.toPoly_mul, ih, pow_succ]

private theorem list_foldl_mul_eq_mul_prod {α R : Type*} [CommMonoid R]
    (f : α → R) :
    ∀ (xs : List α) (init : R),
      xs.foldl (fun acc x ↦ acc * f x) init = init * (xs.map f).prod
  | [], init => by simp
  | x :: xs, init => by
      rw [List.foldl_cons, list_foldl_mul_eq_mul_prod f xs (init * f x)]
      simp [mul_assoc]

private theorem linearYDivisor_C_toPoly {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] (y : F) :
    CBivariate.toPoly (CBivariate.linearYDivisor (CPolynomial.C y)) =
      (Polynomial.X - Polynomial.C y).map (Polynomial.C : F →+* Polynomial F) := by
  rw [CBivariate.toPoly_eq_map]
  rw [CBivariate.linearYDivisor_toPoly]
  simp [CPolynomial.C_toPoly, CPolynomial.ringEquiv]

private theorem lowMessageYPolynomial_toPoly {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (multiplicity : Nat) :
    CBivariate.toPoly (lowMessageDegreeInterpolation points multiplicity) =
      (lowMessageYPolynomial points multiplicity).map
        (Polynomial.C : F →+* Polynomial F) := by
  unfold lowMessageDegreeInterpolation lowMessageYPolynomial
  have hfold : ∀ (xs : List (F × F)) (Q : CBivariate F) (P : Polynomial F),
      CBivariate.toPoly Q = P.map (Polynomial.C : F →+* Polynomial F) →
        CBivariate.toPoly
            (xs.foldl
              (fun Q point ↦ Q *
                CBivariate.linearYDivisor (CPolynomial.C point.2) ^ multiplicity)
              Q) =
          (xs.foldl
              (fun P point ↦ P * (Polynomial.X - Polynomial.C point.2) ^ multiplicity)
              P).map (Polynomial.C : F →+* Polynomial F) := by
    intro xs
    induction xs with
    | nil =>
        intro Q P hQP
        exact hQP
    | cons point xs ih =>
        intro Q P hQP
        simp only [List.foldl_cons]
        apply ih
        rw [CBivariate.toPoly_mul]
        rw [hQP, Polynomial.map_mul]
        congr 1
        change CBivariate.toPoly
            (CBivariate.linearYDivisor (CPolynomial.C point.2) ^ multiplicity) =
          ((Polynomial.X - Polynomial.C point.2) ^ multiplicity).map
            (Polynomial.C : F →+* Polynomial F)
        rw [cbivariate_toPoly_pow, Polynomial.map_pow]
        rw [linearYDivisor_C_toPoly]
  exact hfold points.toList 1 1 (by simp [CBivariate.toPoly_one])

private theorem lowMessageYPolynomial_ne_zero {F : Type*} [Field F]
    (points : Array (F × F)) (multipity : Nat) :
    lowMessageYPolynomial points multipity ≠ 0 := by
  unfold lowMessageYPolynomial
  have hfold : ∀ (xs : List (F × F)) (acc : Polynomial F),
      acc ≠ 0 →
        xs.foldl
            (fun P point ↦ P * (Polynomial.X - Polynomial.C point.2) ^ multipity)
            acc ≠ 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        exact hacc
    | cons point xs ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact mul_ne_zero hacc
          (pow_ne_zero multipity (Polynomial.X_sub_C_ne_zero point.2))
  exact hfold points.toList 1 one_ne_zero

private theorem lowMessageYPolynomial_factor {F : Type*} [Field F]
    {points : Array (F × F)} {point : F × F} {multiplicity : Nat}
    (hpoint : point ∈ points.toList) :
    (Polynomial.X - Polynomial.C point.2) ^ multiplicity ∣
      lowMessageYPolynomial points multiplicity := by
  unfold lowMessageYPolynomial
  rcases List.mem_iff_append.mp hpoint with ⟨as, bs, hlist⟩
  rw [hlist, List.foldl_append]
  rw [list_foldl_mul_eq_mul_prod]
  simp only [List.map_cons, List.prod_cons]
  rw [list_foldl_mul_eq_mul_prod]
  simp only [one_mul]
  refine ⟨(as.map fun p : F × F ↦
        (Polynomial.X - Polynomial.C p.2) ^ multiplicity).prod *
      (bs.map fun p : F × F ↦
        (Polynomial.X - Polynomial.C p.2) ^ multiplicity).prod, ?_⟩
  ring

private theorem eval_hasseDeriv_X_sub_C_pow_eq_zero_of_lt {F : Type*} [Field F]
    (y : F) {b m : Nat} (hb : b < m) :
    (Polynomial.hasseDeriv b ((Polynomial.X - Polynomial.C y : Polynomial F) ^ m)).eval y =
      0 := by
  have htaylor :
      Polynomial.taylor y ((Polynomial.X - Polynomial.C y : Polynomial F) ^ m) =
        (Polynomial.X : Polynomial F) ^ m := by
    rw [Polynomial.taylor_apply]
    simp
  have hcoeff := congrArg (fun P : Polynomial F ↦ P.coeff b) htaylor
  change ((Polynomial.taylor y ((Polynomial.X - Polynomial.C y : Polynomial F) ^ m)).coeff b) =
      ((Polynomial.X : Polynomial F) ^ m).coeff b at hcoeff
  rw [Polynomial.taylor_coeff, Polynomial.coeff_X_pow] at hcoeff
  simp [Nat.ne_of_lt hb] at hcoeff
  exact hcoeff

private theorem eval_hasseDeriv_eq_zero_of_X_sub_C_pow_dvd {F : Type*} [Field F]
    {P : Polynomial F} {y : F} {b m : Nat}
    (hdiv : (Polynomial.X - Polynomial.C y : Polynomial F) ^ m ∣ P)
    (hb : b < m) :
    (Polynomial.hasseDeriv b P).eval y = 0 := by
  rcases hdiv with ⟨R, rfl⟩
  rw [Polynomial.hasseDeriv_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Polynomial.eval_mul]
  have hijsum : ij.1 + ij.2 = b := by
    simpa [Finset.mem_antidiagonal] using hij
  have hijlt : ij.1 < m := by omega
  rw [eval_hasseDeriv_X_sub_C_pow_eq_zero_of_lt y hijlt]
  simp

private theorem cbivariate_coeff_of_toPoly_map_C {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {P : Polynomial F}
    (hQ : CBivariate.toPoly Q = P.map (Polynomial.C : F →+* Polynomial F))
    (i j : Nat) :
    CBivariate.coeff Q i j = if i = 0 then P.coeff j else 0 := by
  have hcoeff := congrArg
    (fun R : Polynomial (Polynomial F) ↦ (R.coeff j).coeff i) hQ
  change ((CBivariate.toPoly Q).coeff j).coeff i =
      ((P.map (Polynomial.C : F →+* Polynomial F)).coeff j).coeff i at hcoeff
  rw [CBivariate.coeff_toPoly] at hcoeff
  by_cases hi : i = 0
  · subst i
    simpa [Polynomial.coeff_map] using hcoeff
  · simpa [hi, Polynomial.coeff_map, Polynomial.coeff_C] using hcoeff

private theorem hasseDerivative_pos_xOrder_eq_zero_of_toPoly_map_C {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {P : Polynomial F}
    (hQ : CBivariate.toPoly Q = P.map (Polynomial.C : F →+* Polynomial F))
    {a : Nat} (ha : 0 < a) (b : Nat) :
    CBivariate.hasseDerivative a b Q = 0 := by
  apply (CBivariate.eq_iff_coeff).mpr
  intro i j
  rw [CBivariate.hasseDerivative_coeff, CBivariate.coeff_zero]
  rw [cbivariate_coeff_of_toPoly_map_C hQ]
  have hne : ¬ i + a = 0 := by omega
  rw [if_neg hne]
  simp

private theorem hasseDerivativeEval_pos_xOrder_of_toPoly_map_C {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {P : Polynomial F}
    (hQ : CBivariate.toPoly Q = P.map (Polynomial.C : F →+* Polynomial F))
    {a : Nat} (ha : 0 < a) (b : Nat) (x y : F) :
    CBivariate.hasseDerivativeEval a b x y Q = 0 := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [hasseDerivative_pos_xOrder_eq_zero_of_toPoly_map_C hQ ha b]
  rw [CBivariate.evalEval_zero]

private theorem hasseDerivative_zero_xOrder_toPoly_of_map_C {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {P : Polynomial F}
    (hQ : CBivariate.toPoly Q = P.map (Polynomial.C : F →+* Polynomial F))
    (b : Nat) :
    CBivariate.toPoly (CBivariate.hasseDerivative 0 b Q) =
      (Polynomial.hasseDeriv b P).map (Polynomial.C : F →+* Polynomial F) := by
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  rw [CBivariate.coeff_toPoly, CBivariate.hasseDerivative_coeff]
  rw [Polynomial.coeff_map, Polynomial.hasseDeriv_coeff]
  rw [cbivariate_coeff_of_toPoly_map_C hQ]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi]

private theorem hasseDerivativeEval_zero_xOrder_of_toPoly_map_C {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {P : Polynomial F}
    (hQ : CBivariate.toPoly Q = P.map (Polynomial.C : F →+* Polynomial F))
    (b : Nat) (x y : F) :
    CBivariate.hasseDerivativeEval 0 b x y Q =
      (Polynomial.hasseDeriv b P).eval y := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [CBivariate.evalEval_toPoly]
  rw [hasseDerivative_zero_xOrder_toPoly_of_map_C hQ]
  simp [Polynomial.evalEval]

private theorem lowMessageDegreeInterpolation_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (multiplicity : Nat) :
    lowMessageDegreeInterpolation points multiplicity ≠ 0 := by
  intro hzero
  have hmap :
      (lowMessageYPolynomial points multiplicity).map
          (Polynomial.C : F →+* Polynomial F) = 0 := by
    rw [← lowMessageYPolynomial_toPoly points multiplicity]
    rw [hzero, CBivariate.toPoly_zero]
  exact ((Polynomial.map_ne_zero_iff (Polynomial.C_injective (R := F))).mpr
    (lowMessageYPolynomial_ne_zero points multiplicity)) hmap

private theorem lowMessageDegreeInterpolation_weightedDegree_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (multiplicity : Nat) :
    CBivariate.natWeightedDegree (lowMessageDegreeInterpolation points multiplicity) 1 0 ≤ 0 := by
  apply CBivariate.natWeightedDegree_le_of_coeff_zero
  intro i j hgt
  have hto := lowMessageYPolynomial_toPoly points multiplicity
  rw [cbivariate_coeff_of_toPoly_map_C hto]
  have hi : i ≠ 0 := by omega
  simp [hi]

private theorem lowMessageDegreeInterpolation_satisfies {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (F × F)) (multiplicity : Nat) :
    CBivariate.SatisfiesMultiplicityConstraints
      (lowMessageDegreeInterpolation points multiplicity) points multiplicity := by
  intro point hpoint a b hab
  have hto := lowMessageYPolynomial_toPoly points multiplicity
  by_cases ha : a = 0
  · subst a
    rw [hasseDerivativeEval_zero_xOrder_of_toPoly_map_C hto]
    exact eval_hasseDeriv_eq_zero_of_X_sub_C_pow_dvd
      (lowMessageYPolynomial_factor (points := points)
        (point := point) (multiplicity := multiplicity) hpoint)
      (by omega)
  · exact hasseDerivativeEval_pos_xOrder_of_toPoly_map_C hto
      (Nat.pos_of_ne_zero ha) b point.1 point.2

/-- Constructive low-message interpolation returns a semantic GS interpolation witness. -/
theorem lowMessageDegreeInterpolation_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)} {params : GSInterpParams}
    (hLow : params.messageDegree ≤ 1) :
    let Q := lowMessageDegreeInterpolation points params.multiplicity
    ValidInterpolationWitness points params Q := by
  dsimp
  refine ⟨lowMessageDegreeInterpolation_ne_zero points params.multiplicity, ?_, ?_⟩
  · have hy : yWeight params = 0 := by
      unfold yWeight
      omega
    rw [hy]
    exact le_trans
      (lowMessageDegreeInterpolation_weightedDegree_zero points params.multiplicity)
      (Nat.zero_le params.weightedDegreeBound)
  · exact lowMessageDegreeInterpolation_satisfies points params.multiplicity

end GuruswamiSudan

end CompPoly
