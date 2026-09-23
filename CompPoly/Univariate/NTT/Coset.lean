/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.ToPoly.Core
public import CompPoly.Univariate.NTT.Interpolation
public import CompPoly.Univariate.ToPoly.RingHom

/-!
# Coset NTT

Evaluation and interpolation on a multiplicative coset `g·⟨ω⟩ = {g·ωᵏ}` of an NTT domain,
the shape of a STARK/FRI low-degree extension. Both reduce to the plain transform by
scaling coefficients: `p(g·x) = (∑ gʲ pⱼ xʲ)`, so evaluating `p` on the coset is the
forward NTT of `(gʲ pⱼ)ⱼ`, and interpolating on the coset is the inverse NTT followed by
scaling with `g⁻¹`.

## Main definitions

* `NTT.Coset.scale g m a`: the coefficient array `(gʲ · aⱼ)ⱼ<m`.
* `NTT.evalOnCoset D g p`: `p` evaluated at every coset node `g·ωᵏ`, in natural order.
* `NTT.Coset.forwardImpl`, `NTT.Coset.inverseImpl`: the coset transforms.
* `NTT.Coset.interpolate`: interpolation of natural-order values on the coset.

## Main results

* `NTT.Coset.eval_scale`: `(scale g m p).eval x = p.eval (g * x)` below the size bound.
* `NTT.Coset.forwardImpl_eq_evalOnCoset`: the coset forward transform evaluates on the coset.
* `NTT.Coset.inverseImpl_evalOnCoset_eq`: the coset inverse transform interpolates.
* `NTT.Coset.interpolate_eq_interpolate`: coset interpolation is Lagrange interpolation on
  the nodes `g·ωᵏ`.
-/

@[expose] public section

open scoped BigOperators

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

/-- Evaluate a raw polynomial at every coset node `g·ωᵏ`, in natural order. -/
def evalOnCoset (D : Domain R) (g : R) (p : CPolynomial.Raw R) : Array R :=
  Array.ofFn (fun k : D.Idx => p.eval (g * D.node k))

@[simp] theorem size_evalOnCoset (D : Domain R) (g : R) (p : CPolynomial.Raw R) :
    (evalOnCoset D g p).size = D.n := by
  simp [evalOnCoset]

namespace Coset

/-- Scale the first `m` coefficients by powers of `g`: `(gʲ · aⱼ)ⱼ<m`. -/
def scale (g : R) (m : Nat) (a : Array R) : CPolynomial.Raw R :=
  Array.ofFn (fun j : Fin m => g ^ (j : Nat) * a.getD j 0)

@[simp] theorem size_scale (g : R) (m : Nat) (a : Array R) : (scale g m a).size = m := by
  simp [scale]

theorem getD_scale (g : R) (m : Nat) (a : Array R) (j : Nat) (hj : j < m) :
    (scale g m a).getD j 0 = g ^ j * a.getD j 0 := by
  simp [scale, hj]

/-- A raw polynomial below degree `m` is the sum of its first `m` monomials. -/
theorem eval_eq_sum_fin (p : CPolynomial.Raw R) (m : Nat)
    (hdeg : p.toPoly.natDegree < m) (x : R) :
    p.eval x = ∑ j : Fin m, p.getD j 0 * x ^ (j : Nat) := by
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, Polynomial.eval_eq_sum_range' hdeg,
    ← Fin.sum_univ_eq_sum_range (fun j => p.toPoly.coeff j * x ^ j) m]
  apply Finset.sum_congr rfl
  intro j _
  rw [CPolynomial.Raw.coeff_toPoly]

/-- A raw polynomial of size at most `m > 0` has degree below `m`. -/
theorem natDegree_lt_of_size_le (p : CPolynomial.Raw R) {m : Nat} (hm : 0 < m)
    (hsize : p.size ≤ m) : p.toPoly.natDegree < m := by
  by_cases hzero : p.toPoly = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hm
  · rw [Polynomial.natDegree_lt_iff_degree_lt hzero, Polynomial.degree_lt_iff_coeff_zero]
    intro i hi
    rw [CPolynomial.Raw.coeff_toPoly]
    simp only [CPolynomial.Raw.coeff]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

/-- Scaling coefficients by powers of `g` composes the polynomial with `x ↦ g·x`. -/
theorem eval_scale (g : R) (m : Nat) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < m) (x : R) :
    CPolynomial.Raw.eval x (scale g m p) = p.eval (g * x) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hdeg
  rw [eval_eq_sum_fin (scale g m p) m (natDegree_lt_of_size_le _ hm (by simp)) x,
    eval_eq_sum_fin p m hdeg (g * x)]
  apply Finset.sum_congr rfl
  intro j _
  rw [getD_scale g m p j j.isLt, mul_pow]
  ring

/-- Scaling by `g` and then by `g⁻¹` restores the first `m` coefficients. -/
theorem eval_scale_inv (g : R) (hg : g ≠ 0) (m : Nat) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < m) (x : R) :
    CPolynomial.Raw.eval (g * x) (scale g⁻¹ m p) = p.eval x := by
  rw [eval_scale g⁻¹ m p hdeg, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]

/-- Forward transform on the coset `g·⟨ω⟩`: values `p(g·ωᵏ)` in natural order. -/
def forwardImpl (D : Domain R) (g : R) (p : CPolynomial.Raw R) : Array R :=
  Forward.forwardImpl D (scale g D.n p)

/-- Inverse transform on the coset `g·⟨ω⟩`, from natural-order values. -/
def inverseImpl (D : Domain R) (g : R) (v : Array R) : CPolynomial.Raw R :=
  scale g⁻¹ D.n (Inverse.inverseImpl D v)

/-- The coset forward transform evaluates the polynomial on the coset. -/
theorem forwardImpl_eq_evalOnCoset (D : Domain R) (g : R) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < D.n) :
    forwardImpl D g p = evalOnCoset D g p := by
  have hscale : (scale g D.n p).toPoly.natDegree < D.n :=
    natDegree_lt_of_size_le _ D.n_pos (by simp)
  rw [forwardImpl, Forward.forwardImpl_eq_evalOnDomain D _ hscale]
  apply Array.ext
  · simp [evalOnDomain, evalOnCoset]
  · intro i hi₁ _
    simp only [evalOnDomain, evalOnCoset, Array.getElem_ofFn]
    exact eval_scale g D.n p hdeg _

/-- The coset inverse transform has degree below the domain size. -/
theorem natDegree_inverseImpl_lt (D : Domain R) (g : R) (v : Array R) :
    (inverseImpl D g v).toPoly.natDegree < D.n :=
  natDegree_lt_of_size_le _ D.n_pos (by simp [inverseImpl])

/-- The coset inverse transform takes each value at its coset node. -/
theorem inverseImpl_eval_node_eq (D : Domain R) (g : R) (hg : g ≠ 0) (v : Array R)
    (k : D.Idx) :
    CPolynomial.Raw.eval (g * D.node k) (inverseImpl D g v) = v.getD k.1 0 := by
  have hdeg : (Inverse.inverseImpl D v).toPoly.natDegree < D.n :=
    natDegree_lt_of_size_le _ D.n_pos (by
      simp [Inverse.inverseImpl_correct])
  rw [inverseImpl, eval_scale_inv g hg D.n _ hdeg]
  exact Inverse.inverseImpl_eval_node_eq D v k

/-- The coset inverse transform evaluates back to its input on the coset. -/
theorem inverseImpl_evalOnCoset_eq (D : Domain R) (g : R) (hg : g ≠ 0) (v : Array R) :
    evalOnCoset D g (inverseImpl D g v) = loadNaturalArray D v := by
  apply Array.ext
  · simp
  · intro i hi₁ _
    simp only [evalOnCoset, Array.getElem_ofFn, getElem_loadNaturalArray]
    exact inverseImpl_eval_node_eq D g hg v ⟨i, by simpa using hi₁⟩

/-- The coset forward transform inverts the coset inverse transform. -/
theorem forwardImpl_inverseImpl (D : Domain R) (g : R) (hg : g ≠ 0) (v : Array R) :
    forwardImpl D g (inverseImpl D g v) = loadNaturalArray D v := by
  rw [forwardImpl_eq_evalOnCoset D g _ (natDegree_inverseImpl_lt D g v),
    inverseImpl_evalOnCoset_eq D g hg v]

/-- Interpolate natural-order values on the coset `g·⟨ω⟩`, in `O(n log n)`. -/
def interpolate [BEq R] [LawfulBEq R] (D : Domain R) (g : R) (values : Vector R D.n) :
    CPolynomial R :=
  let raw := inverseImpl D g values.toArray
  ⟨raw.trim, CPolynomial.Raw.Trim.isCanonical_trim raw⟩

/-- Coset interpolation takes each value at its coset node. -/
theorem eval_interpolate_node [BEq R] [LawfulBEq R] (D : Domain R) (g : R) (hg : g ≠ 0)
    (values : Vector R D.n) (k : D.Idx) :
    (interpolate D g values).eval (g * D.node k) = values.get k := by
  change CPolynomial.Raw.eval _ (CPolynomial.Raw.trim (inverseImpl D g values.toArray)) = _
  rw [← CPolynomial.Raw.eval_toPoly_eq_eval, CPolynomial.Raw.toPoly_trim,
    CPolynomial.Raw.eval_toPoly_eq_eval, inverseImpl_eval_node_eq D g hg]
  simp [Vector.get]

/-- Coset interpolation is Lagrange interpolation on the nodes `g·ωᵏ`. -/
theorem interpolate_eq_interpolate [BEq R] [LawfulBEq R] (D : Domain R) (g : R) (hg : g ≠ 0)
    (values : Vector R D.n) :
    interpolate D g values =
      CLagrange.interpolate Finset.univ (fun k : D.Idx => g * D.node k) values.get := by
  have hinj : Set.InjOn (fun k : D.Idx => g * D.node k) ↑(Finset.univ : Finset D.Idx) := by
    intro a _ b _ hab
    exact Fin.ext (D.primitive.pow_inj a.isLt b.isLt (mul_left_cancel₀ hg hab))
  apply CPolynomial.toPoly_injective
  rw [CLagrange.cinterpolate_eq_interpolate]
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := Finset.univ)
    (v := fun k : D.Idx => g * D.node k) hinj ?_ ?_ ?_
  · change (CPolynomial.Raw.trim (inverseImpl D g values.toArray)).toPoly.degree < _
    rw [CPolynomial.Raw.toPoly_trim, Finset.card_univ, Fintype.card_fin]
    exact Polynomial.degree_lt_iff_coeff_zero _ _ |>.mpr fun i hi => by
      have h := natDegree_inverseImpl_lt D g values.toArray
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le h (by exact_mod_cast hi))
  · exact Lagrange.degree_interpolate_lt _ hinj
  · intro k _
    rw [Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ k), ← CPolynomial.eval_toPoly,
      eval_interpolate_node D g hg values k]

end Coset
end NTT
end CPolynomial
end CompPoly
