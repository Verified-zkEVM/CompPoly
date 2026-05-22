/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.Lagrange
import CompPoly.Univariate.NTT.Evaluation
import CompPoly.Univariate.NTT.Inverse
import Init.Data.Vector.OfFn
import Mathlib.Algebra.Field.GeomSum

/-!
# NTT and Interpolation

Bridge theorem declarations connecting the NTT specification layer to power-domain
interpolation.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

open scoped BigOperators

private theorem omegaInv_pow_mul_eq (D : Domain R) {i : Nat} (hi : i < D.n) (k : Nat) :
    D.omegaInv ^ (i * k) = D.omega ^ ((D.n - i) * k) := by
  rw [show D.omegaInv ^ (i * k) = (D.omegaInv ^ i) ^ k by rw [pow_mul]]
  rw [show D.omega ^ ((D.n - i) * k) = (D.omega ^ (D.n - i)) ^ k by rw [pow_mul]]
  congr 1
  rw [Domain.omegaInv, inv_pow]
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add]
  have hle : i ≤ D.n := Nat.le_of_lt hi
  rw [Nat.sub_add_cancel hle]
  simpa [Domain.n] using D.primitive.pow_eq_one

private theorem kernel_term_eq (D : Domain R) {i : Nat} (hi : i < D.n) (j k : Nat) :
    D.omega ^ (k * j) * D.omegaInv ^ (i * k) =
      D.omega ^ ((j + (D.n - i)) * k) := by
  rw [omegaInv_pow_mul_eq D hi k]
  rw [← pow_add]
  congr 1
  ring

private theorem omega_sum_pow_mul_eq_if_dvd (D : Domain R) (m : Nat) :
    (∑ k : D.Idx, D.omega ^ (m * (k : Nat))) = if D.n ∣ m then (D.n : R) else 0 := by
  by_cases hdiv : D.n ∣ m
  · rw [if_pos hdiv]
    rcases hdiv with ⟨t, rfl⟩
    trans ∑ _k : D.Idx, (1 : R)
    · apply Finset.sum_congr rfl
      intro k _hk
      rw [show D.n * t * (k : Nat) = D.n * (t * (k : Nat)) by ring]
      rw [pow_mul]
      simp [Domain.n, D.primitive.pow_eq_one]
    · simp
  · rw [if_neg hdiv]
    have hne : D.omega ^ m ≠ 1 := by
      intro h
      exact hdiv ((D.primitive.pow_eq_one_iff_dvd m).mp h)
    have hpow : (D.omega ^ m) ^ D.n = 1 := by
      rw [← pow_mul]
      rw [Nat.mul_comm]
      rw [pow_mul]
      simp [Domain.n, D.primitive.pow_eq_one]
    calc
      (∑ k : D.Idx, D.omega ^ (m * (k : Nat))) =
          ∑ k : D.Idx, (D.omega ^ m) ^ (k : Nat) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [pow_mul]
      _ = (∑ k ∈ Finset.range D.n, (D.omega ^ m) ^ k) := by
            rw [Fin.sum_univ_eq_sum_range]
      _ = 0 := by
            rw [geom_sum_eq hne]
            rw [hpow]
            simp

private theorem dvd_add_sub_iff_fin_eq (D : Domain R) (i j : D.Idx) :
    D.n ∣ (j.1 + (D.n - i.1)) ↔ j = i := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩
    have hlt : j.1 + (D.n - i.1) < 2 * D.n := by omega
    have hpos : 0 < j.1 + (D.n - i.1) := by
      have : 0 < D.n - i.1 := by omega
      omega
    have htlt : t < 2 := by
      rw [ht] at hlt
      nlinarith [D.n_pos]
    have htpos : 0 < t := by
      rw [ht] at hpos
      nlinarith [D.n_pos]
    interval_cases t
    apply Fin.ext
    omega
  · intro h
    subst h
    use 1
    omega

private theorem kernel_sum_eq_if (D : Domain R) (i j : D.Idx) :
    (∑ k : D.Idx, D.omega ^ ((k : Nat) * (j : Nat)) *
        D.omegaInv ^ ((i : Nat) * (k : Nat))) =
      if j = i then (D.n : R) else 0 := by
  calc
    (∑ k : D.Idx, D.omega ^ ((k : Nat) * (j : Nat)) *
        D.omegaInv ^ ((i : Nat) * (k : Nat))) =
        ∑ k : D.Idx, D.omega ^ (((j : Nat) + (D.n - (i : Nat))) * (k : Nat)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact kernel_term_eq D i.is_lt (j : Nat) (k : Nat)
    _ = if D.n ∣ ((j : Nat) + (D.n - (i : Nat))) then (D.n : R) else 0 := by
          exact omega_sum_pow_mul_eq_if_dvd D ((j : Nat) + (D.n - (i : Nat)))
    _ = if j = i then (D.n : R) else 0 := by
          by_cases h : j = i
          · rw [if_pos h, if_pos ((dvd_add_sub_iff_fin_eq D i j).mpr h)]
          · rw [if_neg h, if_neg (mt (dvd_add_sub_iff_fin_eq D i j).mp h)]

private theorem kernel_sum_forward_inverse_eq_if (D : Domain R) (i j : D.Idx) :
    (∑ k : D.Idx, D.omegaInv ^ ((k : Nat) * (j : Nat)) *
        D.omega ^ ((i : Nat) * (k : Nat))) =
      if j = i then (D.n : R) else 0 := by
  simpa [Domain.inverse, Domain.omegaInv, mul_comm]
    using kernel_sum_eq_if D.inverse i j

private theorem raw_toPoly_degree_lt_size (p : CPolynomial.Raw R) :
    p.toPoly.degree < p.size := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [CPolynomial.Raw.coeff_toPoly]
  simp [CPolynomial.Raw.coeff]
  simp [Nat.not_lt.mpr hi]

private theorem raw_toPoly_natDegree_lt_size_of_size_pos
    (p : CPolynomial.Raw R) (hp : 0 < p.size) :
    p.toPoly.natDegree < p.size := by
  by_cases hzero : p.toPoly = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hp
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (raw_toPoly_degree_lt_size p)

namespace Inverse

private theorem forwardSpec_inverseSpec_get_eq (D : Domain R) (values : Array R) (i : D.Idx) :
    (Forward.forwardSpec D (inverseSpec D values))[i.1] = values.getD i.1 0 := by
  simp [Forward.forwardSpec, Forward.nttAt, inverseSpec, inttAt]
  calc
    (∑ x : D.Idx,
      (D.nInv * ∑ x_1 : D.Idx,
        values[x_1.1]?.getD 0 * D.omegaInv ^ (x.1 * x_1.1)) * D.omega ^ (i.1 * x.1))
      = ∑ x : D.Idx, D.nInv * ((∑ x_1 : D.Idx,
          values[x_1.1]?.getD 0 * D.omegaInv ^ (x.1 * x_1.1)) *
            D.omega ^ (i.1 * x.1)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = D.nInv * (∑ x : D.Idx, ∑ x_1 : D.Idx,
          values[x_1.1]?.getD 0 *
            (D.omegaInv ^ (x.1 * x_1.1) * D.omega ^ (i.1 * x.1))) := by
          rw [← Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x_1 _
          ring
    _ = D.nInv * (∑ x_1 : D.Idx, ∑ x : D.Idx,
          values[x_1.1]?.getD 0 *
            (D.omegaInv ^ (x.1 * x_1.1) * D.omega ^ (i.1 * x.1))) := by
          rw [Finset.sum_comm]
    _ = D.nInv * (∑ x_1 : D.Idx,
          values[x_1.1]?.getD 0 * (∑ x : D.Idx,
            D.omegaInv ^ (x.1 * x_1.1) * D.omega ^ (i.1 * x.1))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x_1 _
          rw [Finset.mul_sum]
    _ = D.nInv * (∑ x_1 : D.Idx,
          values[x_1.1]?.getD 0 * (if x_1 = i then (D.n : R) else 0)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x_1 _
          rw [kernel_sum_forward_inverse_eq_if D i x_1]
    _ = values[i.1]?.getD 0 := by
          rw [Finset.sum_eq_single i]
          · have hn : ((D.n : Nat) : R) ≠ 0 := by
              simpa [Domain.n] using D.natCast_ne_zero
            simp only [if_true]
            rw [Domain.nInv]
            rw [_root_.mul_comm (values[i.1]?.getD 0) (((D.n : Nat) : R))]
            rw [← _root_.mul_assoc]
            rw [inv_mul_cancel₀ hn]
            simp
          · intro b _hb hb
            simp [hb]
          · intro hii
            exact (hii (Finset.mem_univ i)).elim

/-- Pointwise form of `inverseSpec_interpolatePow_eq`. -/
theorem inverseSpec_eval_node_eq (D : Domain R) (values : Array R) (k : D.Idx) :
    CPolynomial.Raw.eval (D.node k) (inverseSpec D values) = values.getD k.1 0 := by
  have hdeg : (CPolynomial.Raw.toPoly (inverseSpec D values)).natDegree < D.n := by
    simpa [inverseSpec] using
      raw_toPoly_natDegree_lt_size_of_size_pos (R := R) (inverseSpec D values) (by
        simp [inverseSpec])
  have hforward := Forward.forwardSpec_eval_node_eq D (inverseSpec D values) hdeg k
  have hvalues := forwardSpec_inverseSpec_get_eq D values k
  rw [hforward] at hvalues
  exact hvalues

/-- The inverse NTT specification evaluates back to the input values on the NTT domain. -/
theorem inverseSpec_evalOnDomain_eq (D : Domain R) (values : Array R) :
    evalOnDomain D (inverseSpec D values) = loadNaturalArray D values := by
  apply Array.ext
  · simp [evalOnDomain, loadNaturalArray]
  · intro i hi₁ hi₂
    let k : D.Idx := ⟨i, by simpa [evalOnDomain] using hi₁⟩
    simpa [evalOnDomain, loadNaturalArray, k] using inverseSpec_eval_node_eq D values k

/-- The inverse NTT specification interpolates the input values on the NTT domain. -/
theorem inverseSpec_interpolatePow_eq [BEq R] [LawfulBEq R]
    (D : Domain R) (values : Array R) :
    CPolynomial.Raw.trim (inverseSpec D values) =
      (CLagrange.interpolatePow D.omega (loadNaturalVector D values)).val := by
  let r : Vector R D.n := loadNaturalVector D values
  let q : CPolynomial R := CLagrange.interpolatePow D.omega r
  have hrawdeg : (CPolynomial.Raw.toPoly (inverseSpec D values)).degree < D.n := by
    simpa [inverseSpec] using raw_toPoly_degree_lt_size (R := R) (inverseSpec D values)
  have hunit : IsUnit D.omega := D.primitive.isUnit D.n_ne_zero
  let omegaUnit : Rˣ := hunit.unit
  have homegaUnit : (omegaUnit : R) = D.omega := hunit.unit_spec
  have hprimUnit : IsPrimitiveRoot omegaUnit D.n := by
    simpa [omegaUnit] using IsPrimitiveRoot.isUnit_unit D.n_ne_zero D.primitive
  have horder : D.n ≤ orderOf omegaUnit := by
    rw [← hprimUnit.eq_orderOf]
  have hnodes : Set.InjOn (fun k : D.Idx => D.node k) Set.univ := by
    intro a _ha b _hb hab
    apply CLagrange.eq_of_pow_eq_pow_of_lt_orderOf horder
    apply Units.ext
    simpa [Domain.node, omegaUnit, homegaUnit] using hab
  have hinterpdeg : q.toPoly.degree < D.n := by
    unfold q CLagrange.interpolatePow
    rw [CLagrange.cinterpolate_eq_interpolate]
    simpa [Domain.node] using
      Lagrange.degree_interpolate_lt
        (s := Finset.univ) (v := fun k : D.Idx => D.node k)
        (r := r.get) (by simpa using hnodes)
  have hinterpEval : ∀ k : D.Idx, q.eval (D.node k) = values.getD k.1 0 := by
    intro k
    have h := CLagrange.eval_interpolatePow_at_node
      (ω := omegaUnit) (r := r) horder k
    have hget : r.get k = values.getD k.1 0 := by
      dsimp [r]
      simp [loadNaturalVector, Vector.get]
    rw [← hget]
    simpa [q, Domain.node, omegaUnit, homegaUnit] using h
  have hpoly :
      CPolynomial.Raw.toPoly (inverseSpec D values) = q.toPoly := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (s := Finset.univ) (v := fun k : D.Idx => D.node k)
      (by simpa using hnodes) (by simpa using hrawdeg) (by simpa using hinterpdeg) ?_
    intro k _hk
    rw [CPolynomial.Raw.eval_toPoly_eq_eval (D.node k) (inverseSpec D values)]
    rw [← CPolynomial.eval_toPoly (D.node k) q]
    rw [inverseSpec_eval_node_eq D values k, hinterpEval k]
  calc
    CPolynomial.Raw.trim (inverseSpec D values)
        = (CPolynomial.Raw.toPoly (inverseSpec D values)).toImpl := by
            exact (CPolynomial.Raw.toImpl_toPoly (R := R) (inverseSpec D values)).symm
    _ = q.toPoly.toImpl := by
            rw [hpoly]
    _ = q.val.trim := by
            exact CPolynomial.Raw.toImpl_toPoly (R := R) q.val
    _ = q.val := by
            exact CPolynomial.Raw.Trim.trim_eq_of_isCanonical q.property

/-- The inverse NTT implementation interpolates the input values on the NTT domain. -/
theorem inverseImpl_interpolatePow_eq [BEq R] [LawfulBEq R]
    (D : Domain R) (values : Array R) :
    CPolynomial.Raw.trim (inverseImpl D values) =
      (CLagrange.interpolatePow D.omega (loadNaturalVector D values)).val := by
  rw [inverseImpl_correct]
  exact inverseSpec_interpolatePow_eq D values

/-- Pointwise form of `inverseImpl_interpolatePow_eq`. -/
theorem inverseImpl_eval_node_eq (D : Domain R) (values : Array R) (k : D.Idx) :
    CPolynomial.Raw.eval (D.node k) (inverseImpl D values) = values.getD k.1 0 := by
  rw [inverseImpl_correct]
  exact inverseSpec_eval_node_eq D values k

/-- The inverse NTT implementation evaluates back to the input values on the NTT domain. -/
theorem inverseImpl_evalOnDomain_eq (D : Domain R) (values : Array R) :
    evalOnDomain D (inverseImpl D values) = loadNaturalArray D values := by
  rw [inverseImpl_correct]
  exact inverseSpec_evalOnDomain_eq D values

end Inverse
end NTT
end CPolynomial
end CompPoly
