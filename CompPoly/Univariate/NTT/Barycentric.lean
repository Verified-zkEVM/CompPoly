/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Univariate.Barycentric
public import CompPoly.Univariate.NTT.Domain

/-!
# Barycentric Interpolation on an NTT Domain

On the full group of `n`-th roots of unity the nodal polynomial is `Xⁿ - 1`, so the
barycentric weight of the node `ωⁱ` has the closed form `ωⁱ / n`. This file builds the
`BarycentricDomain` of an NTT domain from that formula, in `O(n)` field operations and one
inversion, rather than through the generic `O(n²)` product of `BarycentricDomain.mk'`.

## Main definitions

* `NTT.Domain.barycentric`: the barycentric domain of `D`, with weights `ωⁱ · n⁻¹`.

## Main results

* `NTT.Domain.nodal_eq_X_pow_sub_one`: the nodal polynomial of the domain is `Xⁿ - 1`.
* `NTT.Domain.nodalWeight_eq`: the barycentric weight of `ωⁱ` is `ωⁱ · n⁻¹`.
* `NTT.Domain.barycentric_eval_eq_interpolatePow_eval`: evaluating through the domain is
  evaluating `CLagrange.interpolatePow D.omega`.
-/

@[expose] public section

open Polynomial

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Domain

variable {R : Type*} [Field R]

/-- The nodes of an NTT domain are pairwise distinct. -/
theorem node_injective (D : Domain R) : Function.Injective D.node :=
  fun i j hij => Fin.ext (D.primitive.pow_inj i.isLt j.isLt hij)

/-- Every node of an NTT domain is an `n`-th root of unity. -/
theorem node_pow_n (D : Domain R) (i : D.Idx) : D.node i ^ D.n = 1 := by
  rw [node, ← pow_mul, mul_comm, pow_mul]
  simp [D.primitive.pow_eq_one]

/-- The nodal polynomial of an NTT domain is `Xⁿ - 1`. -/
theorem nodal_eq_X_pow_sub_one (D : Domain R) :
    Lagrange.nodal Finset.univ D.node = Polynomial.X ^ D.n - 1 := by
  have h : Polynomial.degree (1 : R[X]) < Polynomial.degree ((Polynomial.X : R[X]) ^ D.n) := by
    simp
  apply Polynomial.eq_of_degree_le_of_eval_index_eq (v := D.node) Finset.univ
  · exact D.node_injective.injOn
  · exact Lagrange.degree_nodal.le
  · rw [Lagrange.degree_nodal, Polynomial.degree_sub_eq_left_of_degree_lt h]
    simp
  · rw [Lagrange.nodal_monic, Polynomial.leadingCoeff_sub_of_degree_lt h,
      Polynomial.monic_X_pow]
  · intro i hi
    rw [Lagrange.eval_nodal_at_node hi, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, node_pow_n, sub_self]

/-- The barycentric weight of the node `ωⁱ` of an NTT domain is `ωⁱ / n`. -/
theorem nodalWeight_eq (D : Domain R) (i : D.Idx) :
    Lagrange.nodalWeight Finset.univ D.node i = D.node i * D.nInv := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i),
    nodal_eq_X_pow_sub_one]
  have hpow : D.node i * D.node i ^ (D.n - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel D.n_pos, node_pow_n]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    nInv]
  rw [mul_inv, mul_comm]
  congr 1
  exact inv_eq_of_mul_eq_one_left hpow

/-- The barycentric domain of an NTT domain, with the closed-form weights `ωⁱ · n⁻¹`. -/
def barycentric [DecidableEq R] (D : Domain R) : CLagrange.BarycentricDomain R D.n :=
  let nodes := Vector.ofFn D.node
  let nInv := D.nInv
  let weights := Vector.ofFn fun i : D.Idx => nodes[i] * nInv
  { nodes := fun i => nodes[i]
    nodes_injective := by
      simpa [nodes] using D.node_injective
    weights := fun i => weights[i]
    weights_spec := fun i => by
      have h := nodalWeight_eq D i
      simp only [Lagrange.nodalWeight] at h
      simp [weights, nodes, nInv, h] }

@[simp] theorem barycentric_nodes [DecidableEq R] (D : Domain R) (i : D.Idx) :
    D.barycentric.nodes i = D.node i := by
  simp [barycentric]

/-- Barycentric evaluation on an NTT domain is evaluation of `CLagrange.interpolatePow`. -/
theorem barycentric_eval_eq_interpolatePow_eval [DecidableEq R] [BEq R] [LawfulBEq R]
    (D : Domain R) (values : Vector R D.n) (z : R) :
    D.barycentric.eval values.get z =
      (CLagrange.interpolatePow D.omega values).eval z := by
  have hnodes : D.barycentric.nodes = D.node := funext (barycentric_nodes D)
  rw [CLagrange.BarycentricDomain.eval_eq_cinterpolate_eval, CLagrange.interpolatePow, hnodes]
  rfl

end Domain
end NTT
end CPolynomial
end CompPoly
