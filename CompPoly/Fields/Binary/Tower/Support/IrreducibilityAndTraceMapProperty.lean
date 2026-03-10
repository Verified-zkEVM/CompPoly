/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Support.DefiningPoly

open Polynomial
open AdjoinRoot
open Module

section IrreducibilityAndTraceMapProperty
/--
Generic irreducibility theorem for binary tower polynomials.
Proves that X² + s·X + 1 is irreducible when s satisfies the required properties.
This is the most general form that can be reused across different tower constructions.
-/
instance irreducible_quadratic_defining_poly_of_traceMap_eq_1
  {F : Type*} [Field F] [Fintype F] [CharP F 2] (s : F) [NeZero s] (k : ℕ)
  (trace_map_prop : TraceMapProperty F s k)
  (fintypeCard : Fintype.card F = 2 ^ (2 ^ k)) :
  Irreducible (definingPoly s) := by
  set p := definingPoly s
  have nat_deg_poly_is_2 : p.natDegree = 2 := natDegree_definingPoly s
  have coeffOfX_0 : p.coeff 0 = 1 := definingPoly_coeffOf0 s
  have coeffOfX_1 : p.coeff 1 = s := definingPoly_coeffOf1 s
  have fieldFintypeCard := fintypeCard
  have selfSumEqZero : ∀ (x : F), x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  have sumZeroIffEq : ∀ (x y : F), x + y = 0 ↔ x = y :=
    sum_zero_iff_eq_of_self_sum_zero (selfSumEqZero)

  by_contra h_not_irreducible
  -- Viet theorem : ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
  obtain ⟨c1, c2, h_mul, h_add⟩ :=
    (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
      (definingPoly_is_monic s) (nat_deg_poly_is_2)).mp h_not_irreducible
  rw [coeffOfX_0] at h_mul
  rw [coeffOfX_1] at h_add
  rw [←coeffOfX_1, coeffOfX_1] at h_add -- u = c1 + c2
  rw [←coeffOfX_0, coeffOfX_0] at h_mul -- (1 : F) = c1 * c2

  have c1_ne_zero : c1 ≠ 0 := by
    by_contra h_c1_zero
    rw [h_c1_zero, zero_mul] at h_mul
    have h : (1 : F) ≠ 0 := by exact Ne.symm (zero_ne_one' F)
    contradiction

  have c2_is_c1_inv : c2 = c1⁻¹ := by
    apply mul_left_cancel₀ (ha:=c1_ne_zero)
    rw [←h_mul, mul_inv_cancel₀ (a:=c1) (h:=c1_ne_zero)]

  have h_c1_square : c1^2 = c1 * s + 1 := by
    have eq : c1 + c1⁻¹ = s := by
      rw [c2_is_c1_inv] at h_add
      exact h_add.symm
    rw [←mul_right_inj' c1_ne_zero (b:=(c1 + c1⁻¹)) (c:=s)] at eq
    rw [left_distrib] at eq
    rw [←pow_two, mul_inv_cancel₀ (a:=c1) (c1_ne_zero)] at eq
    -- theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
    rw [← add_left_inj (a:=1)] at eq
    rw [add_assoc] at eq
    rw [selfSumEqZero (1 : F), add_zero] at eq
    exact eq

  have x_pow_card : ∀ (x : F), x^(2^2^k) = x := by
    intro x
    calc
      x^(2^2^k) = x^(Fintype.card F) := by rw [fieldFintypeCard]
      _ = x := by exact FiniteField.pow_card x

  have x_pow_exp_of_2_repr := pow_exp_of_2_repr_given_x_square_repr (sumZeroIffEq := sumZeroIffEq)

  have c1_pow_card_eq_c1:= x_pow_card c1 -- Fermat's little theorem
  have two_to_k_plus_1_ne_zero : 2^k ≠ 0 := by norm_num
  have c1_pow_card_eq := x_pow_exp_of_2_repr (x:=c1) (z:=s)
    (h_z_non_zero:=NeZero.ne s) (h_x_square:=h_c1_square) (i:=2^(k))
  rw [c1_pow_card_eq_c1] at c1_pow_card_eq
  -- c1_pow_card_eq : c1 = c1 * s ^ (2 ^ 2 ^ k - 1)
    -- + ∑ j ∈ Finset.Icc 1 (2 ^ k), s ^ (2 ^ 2 ^ k - 2 ^ j)

  have h_1_le_fin_card : 1 ≤ Fintype.card F := by
    rw [fieldFintypeCard] -- ⊢ 1 ≤ 2 ^ 2 ^ k
    apply Nat.one_le_pow
    apply Nat.zero_lt_two
  let instDivisionRing : DivisionRing F := inferInstance
  let instDivisionSemiring : DivisionSemiring F := instDivisionRing.toDivisionSemiring
  let instGroupWithZero : GroupWithZero F := instDivisionSemiring.toGroupWithZero

  have u_pow_card_sub_one : s ^ (2 ^ 2 ^ k - 1) = 1 := by
    rw [←FiniteField.pow_card_sub_one_eq_one (a:=s) (ha:=NeZero.ne s)]
    rw [fieldFintypeCard]

  rw [u_pow_card_sub_one, mul_one] at c1_pow_card_eq -- u_pow_card_eq : u = u * 1
  -- + ∑ j ∈ Finset.range (2 ^ k), (of prevPoly) t1 ^ (2 ^ 2 ^ k - 2 ^ (j + 1))
  set rsum := ∑ j ∈ Finset.Icc 1 (2 ^ k), s ^ (2 ^ 2 ^ k - 2 ^ j) with rsum_def
  have rsum_eq_zero : rsum = 0 := by
    have sum_eq_2 : -c1 + c1 = -c1 + (c1 + rsum) := (add_right_inj (a := -c1)).mpr c1_pow_card_eq
    have sum_eq_3 : 0 = -c1 + (c1 + rsum) := by
      rw [neg_add_cancel] at sum_eq_2
      exact sum_eq_2
    rw [←add_assoc, neg_add_cancel, zero_add] at sum_eq_3
    exact sum_eq_3.symm

  have rsum_eq_u : rsum = s := rsum_eq_t1_square_aux (u:=s) (k:=k) (x_pow_card:=x_pow_card)
    (u_ne_zero:=NeZero.ne s) trace_map_prop

  have rsum_ne_zero : rsum ≠ 0 := by
    rw [rsum_eq_u]
    exact NeZero.ne s

  rw [rsum_eq_zero] at rsum_ne_zero
  contradiction

/--
Instance : The trace map property for a quadratic extension defined by a root u of X^2 + t1 * X + 1,
assuming the trace property for t1 at the previous level.
-/
theorem traceMapProperty_of_quadratic_extension
    (F_prev : Type*) [Field F_prev] [Fintype F_prev] (k : ℕ)
    (fintypeCardPrev : Fintype.card F_prev = 2 ^ (2 ^ k))
    (t1 : F_prev) [instNeZero_t1 : NeZero t1]
    {F_cur : Type*} [Field F_cur] (u : F_cur) [instNeZero_u : NeZero u]
    [Algebra F_prev F_cur]
    (h_rel : SpecialElementRelation (t1 := t1) (u := u))
    (prev_trace_map : TraceMapProperty F_prev t1 (k))
    (sumZeroIffEq : ∀ (x y : F_cur), x + y = 0 ↔ x = y) :
    TraceMapProperty F_cur u (k + 1) := by
  have h_t1_ne_0 : t1 ≠ 0 := NeZero.ne t1
  set algMap := algebraMap F_prev F_cur
  have liftedPrevTraceMapEvalAtRootsIs1 : ∑ i ∈ Finset.range (2 ^ k), algMap t1 ^ 2 ^ i = 1
    ∧ ∑ i ∈ Finset.range (2 ^ k), (algMap t1)⁻¹ ^ 2 ^ i = 1 := by
    constructor
    · -- First part : sum of t1^(2^i)
      have h_coe : algMap (∑ i ∈ Finset.range (2 ^ k), t1 ^ 2 ^ i) = 1 := by
        rw [prev_trace_map.1, map_one]
      have h_map := map_sum algMap (fun i => t1 ^ 2 ^ i) (Finset.range (2 ^ k))
      rw [h_map] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [map_pow (f := algMap) (a := t1) (n := 2 ^ i)]
      )] at h_coe
      exact h_coe
    · -- Second part : sum of (t1⁻¹)^(2^i)
      have h_coe : algMap (∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ 2 ^ i) = 1 := by
        rw [prev_trace_map.2, map_one]
      have h_map := map_sum algMap (fun i => t1⁻¹ ^ 2 ^ i) (Finset.range (2 ^ k))
      rw [h_map] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [map_pow (f := algMap) (a := t1⁻¹) (n := 2 ^ i)]
      )] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by -- map_inv₀ here
        rw [map_inv₀ (f := algMap) (a := t1)]
      )] at h_coe
      exact h_coe

  have h_prev_pow_card_sub_one : ∀ (x : F_prev) (hx : x ≠ 0), x^(2^(2^k)-1) = 1 := by
    intro x hx
    calc
      x^(2^(2^k)-1) = x^(Fintype.card F_prev - 1) := by rw [fintypeCardPrev]
      _ = 1 := by exact FiniteField.pow_card_sub_one_eq_one (a:=x) (ha:=hx)
  have h_lifted_prev_pow_card_sub_one : ∀ (x : F_prev) (hx : x ≠ 0),
    algMap x^(2^(2^k)-1) = 1 := by
    intro x hx
    have h1 : x^(2^(2^k)-1) = 1 := h_prev_pow_card_sub_one x hx
    have h_coe : algMap (x^(2^(2^k)-1)) = 1 := by rw [h1]; exact algebraMap.coe_one
    rw [map_pow (f := algMap) (a := x) (n := 2^(2^k)-1)] at h_coe
    exact h_coe

  have h_t1_pow : algMap t1^(2^(2^k)-1) = 1 ∧ (algMap t1)⁻¹^(2^(2^k)-1) = 1 := by
    constructor
    · rw [h_lifted_prev_pow_card_sub_one t1 (h_t1_ne_0)]
    · have t1_inv_ne_zero : t1⁻¹ ≠ 0 := by
        intro h
        rw [inv_eq_zero] at h
        exact h_t1_ne_0 h -- contradiction
      rw [←h_lifted_prev_pow_card_sub_one t1⁻¹ t1_inv_ne_zero]
      rw [map_inv₀ (f := algMap) (a := t1)]

  have galoisAutomorphism : u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u := by
    exact galois_automorphism_power (u:=u) (t1:=algMap t1) (k:=k) (sumZeroIffEq)
      (NeZero.ne u) ((_root_.map_ne_zero algMap).mpr h_t1_ne_0) (h_rel.sum_inv_eq)
      (h_rel.h_u_square) (h_t1_pow) (liftedPrevTraceMapEvalAtRootsIs1)

  have u_is_inv_of_u1 : u = u⁻¹⁻¹ := (inv_inv u).symm

  exact {
    element_trace :=
      lifted_trace_map_eval_at_roots_prev_BTField (u:=u) (t1:=algMap t1) (k:=k)
        (sumZeroIffEq) (h_rel.sum_inv_eq)
        (galoisAutomorphism) (liftedPrevTraceMapEvalAtRootsIs1.1)
    inverse_trace := by
      have u1_plus_u11_eq_t1 : u⁻¹ + u⁻¹⁻¹ = algMap t1 := by
        rw [←h_rel.sum_inv_eq]
        rw [←u_is_inv_of_u1]
        rw [add_comm]
      have galoisAutomorphismRev : (u⁻¹)^(2^(2^k)) = u⁻¹⁻¹ ∧ (u⁻¹⁻¹)^(2^(2^k)) = u⁻¹ := by
        rw [←u_is_inv_of_u1]
        exact ⟨galoisAutomorphism.2, galoisAutomorphism.1⟩
      have res := lifted_trace_map_eval_at_roots_prev_BTField (u:=u⁻¹) (t1:=algMap t1) (k:=k)
        (sumZeroIffEq) (u1_plus_u11_eq_t1)
        (galoisAutomorphismRev) (liftedPrevTraceMapEvalAtRootsIs1.1)
      exact res
  }

variable {R : Type*} [CommRing R] [IsDomain R]
/--
A polynomial with a degree greater than 1 is not irreducible if it has a root in `R`.
-/
theorem not_irreducible_of_isRoot_of_degree_gt_one
    (p : R[X]) (h_root : ∃ r : R, IsRoot p r) (h_deg : p.degree > 1) :
    ¬ Irreducible p := by
  -- Assume p is irreducible for a contradiction.
  by_contra h_irreducible
  -- From the hypothesis, there exists a root `r`.
  obtain ⟨r, hr⟩ := h_root
  -- By the Factor Theorem, if `r` is a root of `p`, then `(X - C r)` divides `p`.
  have h_dvd : X - C r ∣ p := by
    apply Polynomial.dvd_iff_isRoot.mpr
    exact hr
  obtain ⟨q, hq⟩ := h_dvd
  have h_unit_or_unit := h_irreducible.isUnit_or_isUnit (a:=(X - C r)) (b:=q) (hq)
  rcases h_unit_or_unit with h_factor1_is_unit | h_factor2_is_unit
  · -- Case 1 : `(X - C r)` is a unit.
    have h := Polynomial.not_isUnit_X_sub_C (r:=r)
    contradiction
  · -- Case 2 : The other factor `q` is a unit.
    have h_deg_q : q.degree = 0 := by exact degree_eq_zero_of_isUnit h_factor2_is_unit
    have h_deg_p : p.degree = 1 := by
      rw [hq, degree_mul, degree_X_sub_C, h_deg_q, _root_.add_zero]
    have h_deg_p_ne_1 : p.degree ≠ 1 := by
      exact Ne.symm (ne_of_lt h_deg)
    exact h_deg_p_ne_1 h_deg_p -- contradiction
end IrreducibilityAndTraceMapProperty
