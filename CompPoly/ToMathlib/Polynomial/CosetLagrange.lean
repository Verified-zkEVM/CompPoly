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

Let `omega` be a primitive `n`-th root of unity, and let `s != 0`.

The points `x_i = s omega^i`, for `i < n`, form the coset `s mu_n`.

- nodal polynomial: it is `X^n - s^n`.
- barycentric weights: the weight of `x_i` is `x_i / (n s^n)`.
- Lagrange basis: off the coset, `L_i(x) = (x^n - s^n) x_i / (n s^n (x - x_i))`.
- periodic functions: with `n = p m`, a function of period `p` interpolates to `Q(X^m)`.

In the last result, `Q` is the interpolant of the same values over the coset `s^m mu_p`.

```text
    n = 8, p = 2, m = 4:   f = (a, b, a, b, a, b, a, b) on s mu_8
                           Q interpolates (a, b) on s^4 mu_2
                           interpolate(f) = Q(X^4)
```

A STARK verifier uses this to evaluate a periodic column out of the domain.

The cost drops from `O(n)` to `O(p)`.

The weights follow Berrut and Trefethen, *Barycentric Lagrange Interpolation*.

That paper appeared in SIAM Review 46(3), 2004.

The folding follows the Plonky3 periodic-column evaluator.
-/

@[expose] public section

open Finset Lagrange

namespace Polynomial

variable {F : Type*} [Field F]

/-- The points `s omega^i` of the coset `s mu_n`. -/
def rootsOfUnityCoset (s ω : F) (n : ℕ) : Fin n → F := fun i => s * ω ^ (i : ℕ)

theorem rootsOfUnityCoset_injective {s ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hs : s ≠ 0) :
    Function.Injective (rootsOfUnityCoset s ω n) := fun i j h =>
  Fin.ext (hω.pow_inj i.isLt j.isLt (mul_left_cancel₀ hs h))

/-- The nodal polynomial of `s mu_n` is `X^n - s^n`. -/
theorem nodal_rootsOfUnityCoset {s ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n) (hn : 0 < n) :
    nodal univ (rootsOfUnityCoset s ω n) = X ^ n - C (s ^ n) := by
  rw [X_pow_sub_C_eq_prod hω hn rfl, nodal_eq,
    ← Fin.prod_univ_eq_prod_range (fun i => X - C (ω ^ i * s))]
  simp only [rootsOfUnityCoset, map_mul, map_pow, mul_comm]

/-- The barycentric weight of `x_i = s omega^i` is `x_i / (n s^n)`. -/
theorem nodalWeight_rootsOfUnityCoset {s ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : (n : F) ≠ 0) (hs : s ≠ 0) (i : Fin n) :
    nodalWeight univ (rootsOfUnityCoset s ω n) i = rootsOfUnityCoset s ω n i / (n * s ^ n) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp only [h, Nat.cast_zero])
  rw [nodalWeight_eq_eval_derivative_nodal (mem_univ i), nodal_rootsOfUnityCoset hω hn0]
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow,
    eval_X]
  have hx : rootsOfUnityCoset s ω n i ≠ 0 := mul_ne_zero hs (pow_ne_zero _ (hω.ne_zero hn0.ne'))
  have hpow : rootsOfUnityCoset s ω n i ^ n = s ^ n := by
    rw [rootsOfUnityCoset, mul_pow, ← pow_mul, mul_comm (i : ℕ), pow_mul, hω.pow_eq_one, one_pow,
      mul_one]
  have hsucc : rootsOfUnityCoset s ω n i ^ (n - 1) * rootsOfUnityCoset s ω n i = s ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn0, hpow]
  rw [eq_div_iff (mul_ne_zero hn (pow_ne_zero _ hs)), ← hsucc]
  field_simp

/-- Off the coset, `L_i(x) = (x^n - s^n) x_i / (n s^n (x - x_i))`. -/
theorem eval_basis_rootsOfUnityCoset {s ω x : F} {n : ℕ} (hω : IsPrimitiveRoot ω n)
    (hn : (n : F) ≠ 0) (hs : s ≠ 0) (i : Fin n) (hx : x ≠ rootsOfUnityCoset s ω n i) :
    (Lagrange.basis univ (rootsOfUnityCoset s ω n) i).eval x =
      (x ^ n - s ^ n) *
        (rootsOfUnityCoset s ω n i / (n * s ^ n) * (x - rootsOfUnityCoset s ω n i)⁻¹) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp only [h, Nat.cast_zero])
  rw [eval_basis_not_at_node (mem_univ i) hx, nodal_rootsOfUnityCoset hω hn0,
    nodalWeight_rootsOfUnityCoset hω hn hs]
  simp only [map_pow, eval_sub, eval_pow, eval_X, eval_C]

/-- A function of period `p` on `s mu_n`, with `n = p m`, interpolates to `Q(X^m)`.

Here `Q` interpolates the same values over the coset `s^m mu_p`.
-/
theorem interpolate_rootsOfUnityCoset_periodic {s ω : F} {p m : ℕ} [NeZero p]
    (hω : IsPrimitiveRoot ω (p * m)) (hs : s ≠ 0) (hm : 0 < m) (g : Fin p → F) :
    interpolate univ (rootsOfUnityCoset s ω (p * m)) (fun i => g (Fin.ofNat p i)) =
      (interpolate univ (rootsOfUnityCoset (s ^ m) (ω ^ m) p) g).comp (X ^ m) := by
  classical
  have hp : 0 < p := NeZero.pos p
  have hωm : IsPrimitiveRoot (ω ^ m) p := hω.pow (Nat.mul_pos hp hm) (mul_comm p m)
  have hinj := rootsOfUnityCoset_injective hωm (pow_ne_zero m hs)
  set Q := interpolate univ (rootsOfUnityCoset (s ^ m) (ω ^ m) p) g with hQdef
  have hQ : Q.degree < p := by
    have := degree_interpolate_lt (s := univ) g hinj.injOn
    rwa [card_univ, Fintype.card_fin, ← hQdef] at this
  symm
  refine eq_interpolate_of_eval_eq _ (rootsOfUnityCoset_injective hω hs).injOn ?_ fun i _ => ?_
  · rw [card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt degree_le_natDegree ?_
    rw [natDegree_comp, natDegree_X_pow, Nat.cast_lt]
    have : Q.natDegree < p := by
      rcases eq_or_ne Q 0 with h | h
      · rwa [h, natDegree_zero]
      · exact (natDegree_lt_iff_degree_lt h).mpr hQ
    exact Nat.mul_lt_mul_of_pos_right this hm
  · have hpt : rootsOfUnityCoset s ω (p * m) i ^ m =
        rootsOfUnityCoset (s ^ m) (ω ^ m) p (Fin.ofNat p i) := by
      have hmod : (ω ^ m) ^ ((i : ℕ) % p) = (ω ^ m) ^ (i : ℕ) := by
        conv_rhs => rw [← pow_mod_orderOf (ω ^ m) (i : ℕ), ← hωm.eq_orderOf]
      simp only [rootsOfUnityCoset, Fin.val_ofNat]
      rw [hmod, mul_pow, ← pow_mul, ← pow_mul, mul_comm m]
    rw [eval_comp, eval_pow, eval_X, hpt]
    exact eval_interpolate_at_node _ hinj.injOn (mem_univ _)

end Polynomial
