/-
Copyright (c) 2025 CompPoly, Elias Judin, Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic)
-/
import Mathlib.LinearAlgebra.Lagrange
import CompPoly.Univariate.Lagrange

/-!
# Barycentric Interpolation

This file provides a **fixed-domain barycentric interpolation** structure and evaluator
for univariate computable polynomials.

## Main definitions

* `CLagrange.BarycentricDomain` – a structure bundling `n` distinct nodes in `R` together with
  precomputed barycentric weights `w_i = ∏_{j ≠ i} (x_i − x_j)⁻¹`.

* `CLagrange.BarycentricDomain.eval` – the standard second-form barycentric evaluator:
  - if `z` equals a node `x_i`, returns `y_i` (the explicit node-hit fast path);
  - otherwise returns
    `(∑ w_i y_i / (z − x_i)) / (∑ w_i / (z − x_i))`.

## Main results

* `weights_eq_nodalWeight` – stored weights agree with `Lagrange.nodalWeight`.
* `eval_at_node` – the evaluator returns `y i` at node `x_i`.
* `eval_eq_cinterpolate_eval` – the evaluator equals
  `(CLagrange.interpolate Finset.univ nodes y).eval z`.
* `eval_eq_interpolate_eval` – variant in terms of `Lagrange.interpolate`.
* `ofPow_eval_eq_interpolatePow_eval` – specialisation to `CLagrange.interpolatePow`.
-/

open Finset

namespace CompPoly.CPolynomial.CLagrange

variable {R : Type*} [Field R] [DecidableEq R]

/-- A fixed-domain barycentric interpolation structure.

Bundles `n` distinct evaluation nodes together with precomputed barycentric weights.
The evaluator `BarycentricDomain.eval` can then be called repeatedly for different
value vectors and query points with no redundant per-query work on the nodes. -/
structure BarycentricDomain (R : Type*) [Field R] [DecidableEq R] (n : ℕ) where
  /-- The evaluation nodes. -/
  nodes : Fin n → R
  /-- The nodes are pairwise distinct. -/
  nodes_injective : Function.Injective nodes
  /-- Precomputed barycentric weights. -/
  weights : Fin n → R
  /-- The stored weights satisfy the standard product-inverse formula:
  `w_i = ∏_{j ≠ i} (x_i − x_j)⁻¹`. -/
  weights_spec : ∀ i, weights i =
    ((Finset.univ : Finset (Fin n)).erase i).prod (fun j => (nodes i - nodes j)⁻¹)

variable {n : ℕ}

/-- Construct a `BarycentricDomain` from nodes and an injectivity proof,
computing the weights automatically. -/
def BarycentricDomain.mk' (nodes : Fin n → R) (hinj : Function.Injective nodes) :
    BarycentricDomain R n where
  nodes := nodes
  nodes_injective := hinj
  weights i := ((Finset.univ : Finset (Fin n)).erase i).prod (fun j => (nodes i - nodes j)⁻¹)
  weights_spec _ := rfl

/-! ### Weight correctness -/

/-- The stored weights are exactly `Lagrange.nodalWeight Finset.univ nodes`. -/
theorem BarycentricDomain.weights_eq_nodalWeight (dom : BarycentricDomain R n) (i : Fin n) :
    dom.weights i = Lagrange.nodalWeight Finset.univ dom.nodes i := by
  rw [dom.weights_spec]; rfl

/-! ### The barycentric evaluator -/

/-- The standard second-form barycentric evaluator.

* If `z` equals a node `x_i`, returns `y i` (the explicit node-hit fast path).
  The node-hit is found by a computable finite search over `Fin n` via `Fin.find`.
* Otherwise returns
  `(∑ i, w_i * y_i * (z − x_i)⁻¹) / (∑ i, w_i * (z − x_i)⁻¹)`,
  the classical barycentric ratio. -/
def BarycentricDomain.eval (dom : BarycentricDomain R n) (y : Fin n → R) (z : R) : R :=
  if h : ∃ i : Fin n, dom.nodes i = z then
    y (Fin.find (fun i => dom.nodes i = z) h)
  else
    (∑ i : Fin n, dom.weights i * y i * (z - dom.nodes i)⁻¹) /
    (∑ i : Fin n, dom.weights i * (z - dom.nodes i)⁻¹)

/-! ### Evaluation at a node -/

/-- At a node, the barycentric evaluator returns the corresponding value. -/
theorem BarycentricDomain.eval_at_node (dom : BarycentricDomain R n) (y : Fin n → R)
    (i : Fin n) : dom.eval y (dom.nodes i) = y i := by
  unfold BarycentricDomain.eval
  have hexists : ∃ j : Fin n, dom.nodes j = dom.nodes i := ⟨i, rfl⟩
  simp only [dif_pos hexists]
  congr 1
  exact dom.nodes_injective (Fin.find_spec hexists)

/-! ### Equivalence with `Lagrange.interpolate` -/

/-- Injectivity of the nodes as a `Set.InjOn` statement on `Finset.univ`. -/
private theorem BarycentricDomain.injOn_nodes (dom : BarycentricDomain R n) :
    Set.InjOn dom.nodes ↑(Finset.univ : Finset (Fin n)) :=
  fun _ _ _ _ h => dom.nodes_injective h

/-
The off-node branch agrees with the Mathlib second barycentric form.
-/
private theorem BarycentricDomain.eval_off_node_eq (dom : BarycentricDomain R n)
    (y : Fin n → R) (z : R) (hne : ∀ i : Fin n, z ≠ dom.nodes i) (hn : 0 < n) :
    (∑ i : Fin n, dom.weights i * y i * (z - dom.nodes i)⁻¹) /
    (∑ i : Fin n, dom.weights i * (z - dom.nodes i)⁻¹) =
    (Lagrange.interpolate Finset.univ dom.nodes y).eval z := by
  rw [ Lagrange.eval_interpolate_not_at_node' ] <;> norm_num [ hne ];
  · simp +decide only [weights_eq_nodalWeight];
    ac_rfl;
  · exact dom.nodes_injective;
  · exact ⟨ ⟨ 0, hn ⟩, Finset.mem_univ _ ⟩

/-
**Main correctness theorem.**
The barycentric evaluator equals `(Lagrange.interpolate univ dom.nodes y).eval z`.
-/
theorem BarycentricDomain.eval_eq_interpolate_eval (dom : BarycentricDomain R n)
    (y : Fin n → R) (z : R) :
    dom.eval y z = (Lagrange.interpolate Finset.univ dom.nodes y).eval z := by
  -- Unfold BarycentricDomain.eval and split on whether ∃ i, dom.nodes i = z.
  by_cases hz : ∃ i : Fin n, dom.nodes i = z;
  · obtain ⟨ i, rfl ⟩ := hz
    generalize_proofs at *;
    rw [ BarycentricDomain.eval_at_node, Lagrange.eval_interpolate_at_node ];
    · exact fun x _ y _ hxy => dom.nodes_injective hxy;
    · exact Finset.mem_univ i;
  · rcases n with ( _ | n ) <;> simp_all +decide [ BarycentricDomain.eval ];
    convert BarycentricDomain.eval_off_node_eq dom y z
      (fun i => Ne.symm (hz i)) (Nat.succ_pos n) using 1

/-- The barycentric evaluator equals
`(CLagrange.interpolate Finset.univ dom.nodes y).eval z`. -/
theorem BarycentricDomain.eval_eq_cinterpolate_eval [BEq R] [LawfulBEq R]
    (dom : BarycentricDomain R n) (y : Fin n → R) (z : R) :
    dom.eval y z = (CLagrange.interpolate Finset.univ dom.nodes y).eval z := by
  rw [dom.eval_eq_interpolate_eval, eval_toPoly, cinterpolate_eq_interpolate]

/-! ### Specialisation to `interpolatePow` -/

/-- Build a barycentric domain from a primitive root of unity `ω` with
`n < orderOf ω`, so nodes are `ω^0, ω^1, …, ω^{n-1}`. -/
def BarycentricDomain.ofPow (ω : Rˣ) (hord : n < orderOf ω) :
    BarycentricDomain R n :=
  BarycentricDomain.mk' (fun i => ω.1 ^ i.val) <| by
    intro a b h
    simp only at h
    exact eq_of_pow_eq_pow_of_lt_orderOf (le_of_lt hord) a b
      (by rw [← Units.val_inj]; simpa using h)

/-- The barycentric evaluator on power-of-ω nodes agrees with
`(CLagrange.interpolatePow ω r).eval z`. -/
theorem BarycentricDomain.ofPow_eval_eq_interpolatePow_eval [BEq R] [LawfulBEq R]
    (ω : Rˣ) (hord : n < orderOf ω) (r : Vector R n) (z : R) :
    (BarycentricDomain.ofPow ω hord).eval r.get z =
    (CLagrange.interpolatePow ω.1 r).eval z := by
  rw [BarycentricDomain.eval_eq_cinterpolate_eval]
  rfl

end CompPoly.CPolynomial.CLagrange
