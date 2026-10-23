/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Lagrange interpolation on a coset of the `n`-th roots of unity

For `ω` a primitive `n`-th root of unity and `s ≠ 0`, the points `s ω ^ i`, `i < n`, form the
coset `s μₙ`.

- Its nodal polynomial is `X ^ n - s ^ n` (`nodal_coset`).
- The barycentric weight of `xᵢ = s ω ^ i` is `xᵢ / (n s ^ n)` (`nodalWeight_coset`).
- Off the coset, `Lᵢ(x) = (x ^ n - s ^ n) xᵢ / (n s ^ n (x - xᵢ))` (`eval_basis_coset`).
- A function of period `p ∣ n` on the coset interpolates to `Q(X ^ (n / p))`, for `Q` its
  interpolant over the coset `s ^ (n / p) μₚ` (`interpolate_coset_periodic`).

The last identity is how a STARK verifier evaluates a periodic column at an out-of-domain point
in `O(p)` instead of `O(n)`.

See Berrut and Trefethen, *Barycentric Lagrange Interpolation*, SIAM Review 46(3), 2004, for the
weights, and the Plonky3 periodic-column evaluator for the folding.
-/

@[expose] public section

open Finset Lagrange

namespace Polynomial

variable {F : Type*} [Field F]

/-- The points `s ω ^ i` of the coset `s μₙ`. -/
def cosetPoints (s ω : F) (n : ℕ) : Fin n → F := fun i => s * ω ^ (i : ℕ)

theorem cosetPoints_injective {s ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hs : s ≠ 0) :
    Function.Injective (cosetPoints s ω n) := fun i j h =>
  Fin.ext (hω.pow_inj i.isLt j.isLt (mul_left_cancel₀ hs h))

/-- The nodal polynomial of `s μₙ` is `X ^ n - s ^ n`. -/
theorem nodal_coset {s ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n) :
    nodal univ (cosetPoints s ω n) = X ^ n - C (s ^ n) := by
  rw [X_pow_sub_C_eq_prod hω hn rfl, nodal_eq,
    ← Fin.prod_univ_eq_prod_range (fun i => X - C (ω ^ i * s))]
  simp [cosetPoints, mul_comm]

/-- The barycentric weight of `xᵢ = s ω ^ i` is `xᵢ / (n s ^ n)`. -/
theorem nodalWeight_coset {s ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : (n : F) ≠ 0)
    (hs : s ≠ 0) (i : Fin n) :
    nodalWeight univ (cosetPoints s ω n) i = cosetPoints s ω n i / (n * s ^ n) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp [h])
  rw [nodalWeight_eq_eval_derivative_nodal (mem_univ i), nodal_coset hω hn0]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow,
    eval_X]
  have hx : cosetPoints s ω n i ≠ 0 := mul_ne_zero hs (pow_ne_zero _ (hω.ne_zero hn0.ne'))
  have hpow : cosetPoints s ω n i ^ n = s ^ n := by
    rw [cosetPoints, mul_pow, ← pow_mul, mul_comm (i : ℕ), pow_mul, hω.pow_eq_one, one_pow,
      mul_one]
  have hsucc : cosetPoints s ω n i ^ (n - 1) * cosetPoints s ω n i = s ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn0, hpow]
  rw [eq_div_iff (mul_ne_zero hn (pow_ne_zero _ hs)), ← hsucc]
  field_simp

/-- Off the coset, `Lᵢ(x) = (x ^ n - s ^ n) xᵢ / (n s ^ n (x - xᵢ))`. -/
theorem eval_basis_coset {s ω x : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : (n : F) ≠ 0)
    (hs : s ≠ 0) (i : Fin n) (hx : x ≠ cosetPoints s ω n i) :
    (Lagrange.basis univ (cosetPoints s ω n) i).eval x =
      (x ^ n - s ^ n) * (cosetPoints s ω n i / (n * s ^ n) * (x - cosetPoints s ω n i)⁻¹) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp [h])
  rw [eval_basis_not_at_node (mem_univ i) hx, nodal_coset hω hn0, nodalWeight_coset hω hn hs]
  simp

/-- A function of period `p` on `s μₙ`, for `n = p m`, interpolates to `Q(X ^ m)`, for `Q` its
interpolant over `s ^ m μₚ`. -/
theorem interpolate_coset_periodic {s ω : F} {p m : ℕ} (hω : IsPrimitiveRoot ω (p * m))
    (hs : s ≠ 0) (hm : 0 < m) (g : Fin p → F) :
    interpolate univ (cosetPoints s ω (p * m)) (fun i => g ⟨i % p, Nat.mod_lt _ (by
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · exact absurd i.isLt (by simp)
        · exact hp)⟩) =
      (interpolate univ (cosetPoints (s ^ m) (ω ^ m) p) g).comp (X ^ m) := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hωm : IsPrimitiveRoot (ω ^ m) p := hω.pow (by positivity) (mul_comm p m)
  have hinj := cosetPoints_injective hωm (pow_ne_zero m hs)
  set Q := interpolate univ (cosetPoints (s ^ m) (ω ^ m) p) g with hQdef
  have hQ : Q.degree < p := by
    have := degree_interpolate_lt (s := univ) g hinj.injOn
    rwa [card_univ, Fintype.card_fin, ← hQdef] at this
  symm
  refine eq_interpolate_of_eval_eq _ (cosetPoints_injective hω hs).injOn ?_ fun i _ => ?_
  · rw [card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [natDegree_comp, natDegree_X_pow, Nat.cast_lt]
    have : Q.natDegree < p := by
      rcases eq_or_ne Q 0 with h | h
      · rw [h]; simpa using hp
      · exact (natDegree_lt_iff_degree_lt h).mpr hQ
    nlinarith
  · have hpt : cosetPoints s ω (p * m) i ^ m =
        cosetPoints (s ^ m) (ω ^ m) p ⟨i % p, Nat.mod_lt _ hp⟩ := by
      have hmod : (ω ^ m) ^ ((i : ℕ) % p) = (ω ^ m) ^ (i : ℕ) := by
        conv_rhs => rw [← pow_mod_orderOf (ω ^ m) (i : ℕ), ← hωm.eq_orderOf]
      simp only [cosetPoints]
      rw [hmod, mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
    rw [eval_comp, eval_pow, eval_X, hpt]
    exact eval_interpolate_at_node _ hinj.injOn (mem_univ _)

end Polynomial
