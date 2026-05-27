/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu, Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Domain
import Mathlib.Algebra.Field.GeomSum

/-!
# NTT Kernel Identities

Shared root-of-unity orthogonality lemmas used by NTT evaluation,
interpolation, and multiplication proofs.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

open scoped BigOperators

/-- Rewrite powers of the inverse root as powers of the forward root. -/
theorem omegaInv_pow_mul_eq (D : Domain R) {i : Nat} (hi : i < D.n) (k : Nat) :
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

/-- Combine a forward-kernel term with an inverse-kernel term. -/
theorem kernel_term_eq (D : Domain R) {i : Nat} (hi : i < D.n) (j k : Nat) :
    D.omega ^ (k * j) * D.omegaInv ^ (i * k) =
      D.omega ^ ((j + (D.n - i)) * k) := by
  rw [omegaInv_pow_mul_eq D hi k]
  rw [← pow_add]
  congr 1
  ring

/-- Sum of powers over the NTT domain, expressed by divisibility of the exponent. -/
theorem omega_sum_pow_mul_eq_if_dvd (D : Domain R) (m : Nat) :
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

/-- The kernel divisibility condition is equivalent to equality of domain indices. -/
theorem dvd_add_sub_iff_fin_eq (D : Domain R) (i j : D.Idx) :
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

/-- Orthogonality of the forward/inverse NTT kernels over the domain. -/
theorem kernel_sum_eq_if (D : Domain R) (i j : D.Idx) :
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

/-- Orthogonality of the inverse/forward NTT kernels over the domain. -/
theorem kernel_sum_forward_inverse_eq_if (D : Domain R) (i j : D.Idx) :
    (∑ k : D.Idx, D.omegaInv ^ ((k : Nat) * (j : Nat)) *
        D.omega ^ ((i : Nat) * (k : Nat))) =
      if j = i then (D.n : R) else 0 := by
  simpa [Domain.inverse, Domain.omegaInv, mul_comm]
    using kernel_sum_eq_if D.inverse i j

end NTT
end CPolynomial
end CompPoly
