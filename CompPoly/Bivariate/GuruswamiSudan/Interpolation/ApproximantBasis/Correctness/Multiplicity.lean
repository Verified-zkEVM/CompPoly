/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import CompPoly.Univariate.Vanishing
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Shear Equivalence for Guruswami-Sudan Multiplicity Constraints

The approximant-basis backend reduces GS interpolation to diagonal modular
congruences on the `Z^b`-coefficients of the sheared polynomial `Q(X, R + Z)`.
This file proves the underlying semantic equivalence: for distinct
interpolation nodes, the packed multiplicity constraints on `Q` hold iff every
sheared coefficient `C_b = (hasseDeriv b Q.toPoly).eval R` is divisible by
`G^(s-b)`, where `G` is the vanishing polynomial of the nodes and `R`
interpolates the values.

The proof works one node at a time.  Writing `M_b = (hasseDeriv b Q.toPoly)`
for the outer `Y`-Hasse derivatives, multiplicity at `(x, y)` says that the
family `M_b.eval (C y)` is `(X - x)^(s-b)`-divisible, while the modular
congruence constrains the family `M_b.eval R`.  Because `R` and `C y` agree at
`x`, an outer Taylor expansion transfers each divisibility family to the
other; distinctness of the nodes then glues the per-node factors into powers
of `G`.
-/

namespace CompPoly

namespace GuruswamiSudan

namespace ApproximantBasis

open Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- `(X - x)^k` divides `A` iff the first `k` Hasse derivatives of `A` vanish
at `x`. -/
theorem X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero
    (A : Polynomial F) (x : F) (k : Nat) :
    (X - C x) ^ k ∣ A ↔
      ∀ a, a < k → (Polynomial.hasseDeriv a A).eval x = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h a ha
    have hcoeff := h a ha
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_coeff] at hcoeff
  · intro h d hd
    rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]
    exact h d hd

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
/-- Shear-transfer core: the `(X - x)`-adic divisibility family of the outer
Hasse-derivative evaluations of `P` moves between outer evaluation points `u`
and `v` that agree modulo `X - x`. -/
theorem X_sub_C_pow_dvd_hasseDeriv_eval_of_dvd_sub
    {P : Polynomial (Polynomial F)} {u v : Polynomial F} {x : F} {s : Nat}
    (huv : (X - C x) ∣ (v - u))
    (h : ∀ b, b < s →
      (X - C x) ^ (s - b) ∣ (Polynomial.hasseDeriv b P).eval u)
    {b : Nat} (hb : b < s) :
    (X - C x) ^ (s - b) ∣ (Polynomial.hasseDeriv b P).eval v := by
  have heval : (Polynomial.hasseDeriv b P).eval v =
      (Polynomial.taylor u (Polynomial.hasseDeriv b P)).eval (v - u) := by
    rw [Polynomial.taylor_apply, Polynomial.eval_comp]
    simp
  rw [heval, Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine Finset.dvd_sum fun t _ht ↦ ?_
  rw [Polynomial.taylor_coeff]
  by_cases hts : t + b < s
  · have hsplit : (X - C x) ^ (s - b) =
        (X - C x) ^ (s - (t + b)) * (X - C x) ^ t := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    refine mul_dvd_mul ?_ (pow_dvd_pow_of_dvd huv t)
    have hcomp : Polynomial.hasseDeriv t (Polynomial.hasseDeriv b P) =
        (t + b).choose t • Polynomial.hasseDeriv (t + b) P := by
      have hmap := Polynomial.hasseDeriv_comp (R := Polynomial F) t b
      calc Polynomial.hasseDeriv t (Polynomial.hasseDeriv b P)
          = ((Polynomial.hasseDeriv t).comp (Polynomial.hasseDeriv b)) P := rfl
        _ = ((t + b).choose t • Polynomial.hasseDeriv (t + b)) P := by rw [hmap]
        _ = (t + b).choose t • Polynomial.hasseDeriv (t + b) P := rfl
    rw [hcomp]
    have heval_smul :
        (((t + b).choose t • Polynomial.hasseDeriv (t + b) P).eval u) =
          (t + b).choose t • ((Polynomial.hasseDeriv (t + b) P).eval u) := by
      simp
    rw [heval_smul, nsmul_eq_mul]
    exact Dvd.dvd.mul_left (h (t + b) hts) _
  · have hpow : (X - C x) ^ (s - b) ∣ (v - u) ^ t :=
      dvd_trans (pow_dvd_pow _ (by omega)) (pow_dvd_pow_of_dvd huv t)
    exact Dvd.dvd.mul_left hpow _

/-- At a single node `(x, y)` with `R(x) = y`, the `(X - x)`-adic divisibility
family of the sheared coefficients `(hasseDeriv b Q.toPoly).eval R` is
equivalent to GS multiplicity of `Q` at the node. -/
theorem X_sub_C_pow_dvd_hasseDeriv_eval_iff_hasMultiplicity
    {Q : CBivariate F} {R : Polynomial F} {x y : F} {s : Nat}
    (hRx : R.eval x = y) :
    (∀ b, b < s →
      (X - C x) ^ (s - b) ∣ (Polynomial.hasseDeriv b Q.toPoly).eval R) ↔
      CBivariate.hasMultiplicity Q s x y := by
  have hdvd_sub : (X - C x) ∣ (R - C y) := by
    rw [Polynomial.dvd_iff_isRoot]
    simp [Polynomial.IsRoot, hRx]
  have hdvd_sub' : (X - C x) ∣ (C y - R) := by
    have hneg := dvd_neg.mpr hdvd_sub
    rwa [neg_sub] at hneg
  have hfamilyCy : (∀ b, b < s → (X - C x) ^ (s - b) ∣
      (Polynomial.hasseDeriv b Q.toPoly).eval (C y)) ↔
      CBivariate.hasMultiplicity Q s x y := by
    rw [CBivariate.hasMultiplicity_iff_hasMultiplicityAtLeast]
    unfold CBivariate.HasMultiplicityAtLeast
    constructor
    · intro h a b hab
      have hb : b < s := by omega
      have hz := (X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero _ x (s - b)).1
        (h b hb) a (by omega)
      rwa [CBivariate.eval_hasseDeriv_eval_hasseDeriv_toPoly] at hz
    · intro h b hb
      rw [X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero]
      intro a ha
      rw [CBivariate.eval_hasseDeriv_eval_hasseDeriv_toPoly]
      exact h a b (by omega)
  constructor
  · intro h
    refine hfamilyCy.1 fun b hb ↦ ?_
    exact X_sub_C_pow_dvd_hasseDeriv_eval_of_dvd_sub hdvd_sub' h hb
  · intro h b hb
    exact X_sub_C_pow_dvd_hasseDeriv_eval_of_dvd_sub hdvd_sub
      (hfamilyCy.2 h) hb

omit [Nontrivial F] [DecidableEq F] in
/-- The linear factor of one node under `toPoly`. -/
theorem linearFactor_toPoly_eq (x : F) :
    (CPolynomial.linearFactor x).toPoly = (X - C x : Polynomial F) := by
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  simp [sub_eq_add_neg, add_comm]

omit [Nontrivial F] [DecidableEq F] in
private theorem vanishingPolynomialArray_toPoly_list
    (xs : List F) (acc : CPolynomial F) :
    (xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc).toPoly =
      acc.toPoly * (xs.map fun x ↦ (X - C x : Polynomial F)).prod := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, CPolynomial.toPoly_mul, linearFactor_toPoly_eq]
      simp only [List.map_cons, List.prod_cons]
      ring

omit [DecidableEq F] in
/-- The array vanishing polynomial is the product of the node linear factors
under `toPoly`. -/
theorem vanishingPolynomialArray_toPoly (xs : Array F) :
    (CPolynomial.vanishingPolynomialArray xs).toPoly =
      (((xs.toList : Multiset F).map fun x ↦
        (X - C x : Polynomial F))).prod := by
  rw [CPolynomial.vanishingPolynomialArray]
  have hlist := vanishingPolynomialArray_toPoly_list xs.toList (1 : CPolynomial F)
  simpa [CPolynomial.toPoly_one, Multiset.map_coe, Multiset.prod_coe] using hlist

omit [DecidableEq F] in
/-- The array vanishing polynomial is monic over the underlying `toPoly`
image. -/
theorem vanishingPolynomialArray_toPoly_monic (xs : Array F) :
    Polynomial.Monic (CPolynomial.vanishingPolynomialArray xs).toPoly := by
  rw [vanishingPolynomialArray_toPoly]
  exact Polynomial.monic_multiset_prod_of_monic _ _
    fun x _hx ↦ Polynomial.monic_X_sub_C x

omit [BEq F] [LawfulBEq F] [Nontrivial F] in
/-- Per-node `(X - x)^k` divisibility glues to divisibility by the `k`-th
power of the product of distinct linear factors. -/
theorem prod_X_sub_C_pow_dvd_of_nodup
    {A : Polynomial F} {xs : List F} {k : Nat}
    (hA : A ≠ 0) (hnodup : xs.Nodup)
    (hroot : ∀ x, x ∈ xs → (X - C x) ^ k ∣ A) :
    (((xs : Multiset F).map fun x ↦ (X - C x : Polynomial F)).prod) ^ k ∣ A := by
  let ms : Multiset F := xs
  have hmsNodup : ms.Nodup := by
    simpa [ms] using hnodup
  have hle : k • ms ≤ A.roots := by
    rw [Multiset.le_iff_count]
    intro x
    rw [Multiset.count_nsmul]
    by_cases hx : x ∈ ms
    · have hxCount : Multiset.count x ms = 1 :=
        Multiset.count_eq_one_of_mem hmsNodup hx
      rw [hxCount, mul_one]
      have hdiv : (X - C x) ^ k ∣ A := hroot x (by simpa [ms] using hx)
      rw [Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hA).2 hdiv
    · rw [Multiset.count_eq_zero_of_notMem hx, mul_zero]
      exact Nat.zero_le _
  have hprod :
      (((k • ms).map fun x ↦ (X - C x : Polynomial F)).prod) ∣ A :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hA (k • ms)).2 hle
  rw [Multiset.map_nsmul, Multiset.prod_nsmul] at hprod
  simpa [ms] using hprod

/-- Batch shear equivalence: over distinct nodes, divisibility of every
sheared coefficient `C_b` by `G^(s-b)` is equivalent to the packed GS
multiplicity constraints. -/
theorem vanishing_pow_dvd_hasseDeriv_eval_iff_satisfiesMultiplicityConstraints
    {points : Array (F × F)} {Q : CBivariate F} {R : CPolynomial F} {s : Nat}
    (hdistinct : DistinctXCoordinates points)
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2) :
    (∀ b, b < s →
      (CPolynomial.vanishingPolynomialArray (points.map fun p ↦ p.1)).toPoly ^ (s - b) ∣
        (Polynomial.hasseDeriv b Q.toPoly).eval R.toPoly) ↔
      CBivariate.SatisfiesMultiplicityConstraints Q points s := by
  have hnodup : (points.map fun p ↦ p.1).toList.Nodup := by
    simpa [DistinctXCoordinates, Array.toList_map] using hdistinct
  have hRp : ∀ point, point ∈ points.toList →
      Polynomial.eval point.1 R.toPoly = point.2 := by
    intro point hpoint
    rw [← CPolynomial.eval_toPoly]
    exact hR point hpoint
  rw [CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity]
  constructor
  · intro h point hpoint
    refine (X_sub_C_pow_dvd_hasseDeriv_eval_iff_hasMultiplicity
      (hRp point hpoint)).1 ?_
    intro b hb
    refine dvd_trans (pow_dvd_pow_of_dvd ?_ (s - b)) (h b hb)
    rw [vanishingPolynomialArray_toPoly]
    refine Multiset.dvd_prod ?_
    rw [Multiset.mem_map]
    refine ⟨point.1, ?_, rfl⟩
    rw [Multiset.mem_coe, Array.toList_map]
    exact List.mem_map.mpr ⟨point, hpoint, rfl⟩
  · intro h b hb
    by_cases hzero : (Polynomial.hasseDeriv b Q.toPoly).eval R.toPoly = 0
    · simp [hzero]
    · rw [vanishingPolynomialArray_toPoly]
      refine prod_X_sub_C_pow_dvd_of_nodup hzero hnodup ?_
      intro x hx
      rw [Array.toList_map] at hx
      rcases List.mem_map.mp hx with ⟨point, hpoint, rfl⟩
      exact (X_sub_C_pow_dvd_hasseDeriv_eval_iff_hasMultiplicity
        (hRp point hpoint)).2 (h point hpoint) b hb

end ApproximantBasis

end GuruswamiSudan

end CompPoly
