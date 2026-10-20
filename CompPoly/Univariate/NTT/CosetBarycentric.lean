/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTT.Barycentric

/-!
# Barycentric evaluation from a coset into an extension field

A polynomial `p` over `F` of degree below `n` is determined by its values on the coset `s · H` of
the order-`n` subgroup `H = ⟨ω⟩`. At any point `z` of an extension field `E` outside the coset,

`p(z) = (zⁿ - sⁿ) / (n sⁿ) · ∑ᵢ (s ωⁱ) / (z - s ωⁱ) · p(s ωⁱ)`.

This is the formula of Plonky3's `interpolate_coset`. The nodal polynomial of the coset is
`Xⁿ - sⁿ`, so the barycentric weight of the node `x = s ωⁱ` is `x / (n sⁿ)`.

## Main results

* `NTT.Domain.cosetNodal_eq`: the nodal polynomial of the coset, over `E`, is `Xⁿ - sⁿ`.
* `NTT.Domain.cosetNodalWeight_eq`: the barycentric weight of `s ωⁱ` is `s ωⁱ / (n sⁿ)`.
* `NTT.Domain.aeval_eq_cosetBarycentric`: the evaluation formula.
-/

@[expose] public section

open Polynomial

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Domain

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The coset node `s ωⁱ`, mapped into `E`. -/
def cosetNode (D : Domain F) (s : F) (i : D.Idx) : E := algebraMap F E (s * D.node i)

theorem cosetNode_pow_n (D : Domain F) (s : F) (i : D.Idx) :
    (D.cosetNode s i : E) ^ D.n = algebraMap F E s ^ D.n := by
  rw [cosetNode, ← map_pow, mul_pow, node_pow_n, mul_one, map_pow]

theorem cosetNode_injective (D : Domain F) {s : F} (hs : s ≠ 0) :
    Function.Injective (D.cosetNode s : D.Idx → E) := fun _ _ h ↦
  D.node_injective (mul_left_cancel₀ hs ((algebraMap F E).injective h))

/-- The nodal polynomial of a coset of the order-`n` subgroup is `Xⁿ - sⁿ`. -/
theorem cosetNodal_eq (D : Domain F) {s : F} (hs : s ≠ 0) :
    Lagrange.nodal Finset.univ (D.cosetNode s : D.Idx → E) =
      Polynomial.X ^ D.n - Polynomial.C (algebraMap F E s ^ D.n) := by
  have h : (Polynomial.C (algebraMap F E s ^ D.n)).degree <
      ((Polynomial.X : E[X]) ^ D.n).degree := by
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_C_le.trans_lt (by exact_mod_cast D.n_pos)
  apply Polynomial.eq_of_degree_le_of_eval_index_eq (v := D.cosetNode s) Finset.univ
  · exact (D.cosetNode_injective hs).injOn
  · exact Lagrange.degree_nodal.le
  · rw [Lagrange.degree_nodal, Polynomial.degree_sub_eq_left_of_degree_lt h]
    simp
  · rw [Lagrange.nodal_monic, Polynomial.leadingCoeff_sub_of_degree_lt h,
      Polynomial.monic_X_pow]
  · intro i hi
    rw [Lagrange.eval_nodal_at_node hi, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, cosetNode_pow_n, sub_self]

/-- `n` is invertible in `E`. -/
theorem natCast_n_ne_zero (D : Domain F) : ((D.n : ℕ) : E) ≠ 0 := by
  rw [← map_natCast (algebraMap F E), ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]
  exact D.natCast_ne_zero

/-- The barycentric weight of the coset node `x = s ωⁱ` is `x / (n sⁿ)`. -/
theorem cosetNodalWeight_eq (D : Domain F) {s : F} (hs : s ≠ 0) (i : D.Idx) :
    Lagrange.nodalWeight Finset.univ (D.cosetNode s : D.Idx → E) i =
      D.cosetNode s i * ((D.n : E) * algebraMap F E s ^ D.n)⁻¹ := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i), cosetNodal_eq D hs]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hx : (D.cosetNode s i : E) ≠ 0 := by
    rw [cosetNode, ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]
    exact mul_ne_zero hs (pow_ne_zero _ (D.primitive.ne_zero D.n_ne_zero))
  have hpow : (D.cosetNode s i : E) * D.cosetNode s i ^ (D.n - 1) = algebraMap F E s ^ D.n := by
    rw [← pow_succ', Nat.sub_add_cancel D.n_pos, cosetNode_pow_n]
  have hn := D.natCast_n_ne_zero (E := E)
  rw [← hpow]
  field_simp

/-- **Barycentric evaluation on a coset.** A polynomial of degree below `n` evaluates at a point
`z` of the extension field outside the coset as `(zⁿ - sⁿ) / (n sⁿ) · ∑ᵢ xᵢ / (z - xᵢ) · p(xᵢ)`,
where `xᵢ = s ωⁱ`. -/
theorem aeval_eq_cosetBarycentric (D : Domain F) {s : F} (hs : s ≠ 0) (p : F[X])
    (hp : p.degree < D.n) (z : E) (hz : z ^ D.n ≠ algebraMap F E s ^ D.n) :
    Polynomial.aeval z p =
      (z ^ D.n - algebraMap F E s ^ D.n) * ((D.n : E) * algebraMap F E s ^ D.n)⁻¹ *
        ∑ i : D.Idx, D.cosetNode s i * (z - D.cosetNode s i)⁻¹ *
          algebraMap F E (p.eval (s * D.node i)) := by
  have hinj : Set.InjOn (D.cosetNode s : D.Idx → E) ((Finset.univ : Finset D.Idx) : Set D.Idx) :=
    (D.cosetNode_injective hs).injOn
  have hdeg : (p.map (algebraMap F E)).degree < (Finset.univ : Finset D.Idx).card := by
    rw [Polynomial.degree_map, Finset.card_univ, Fintype.card_fin]; exact hp
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, Lagrange.eq_interpolate hinj hdeg,
    Lagrange.eval_interpolate_not_at_node _ (fun i _ h ↦ hz (by rw [h, cosetNode_pow_n])),
    cosetNodal_eq D hs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    cosetNodalWeight_eq D hs, Polynomial.eval_map, ← Polynomial.aeval_def, cosetNode,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  ring

end Domain
end NTT
end CPolynomial
end CompPoly
