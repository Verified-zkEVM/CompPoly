/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.BatchEval.Naive
import CompPoly.Univariate.NTT.Forward
import CompPoly.Univariate.ToPoly.Core

/-!
# NTT and Evaluation

Bridge definitions and theorems connecting the NTT specification layer to
evaluation on the root-of-unity domain.
-/

namespace CompPoly
namespace CPolynomial
namespace NTT

variable {R : Type*} [Field R]

/-- Evaluate a raw polynomial on all nodes of an NTT domain in natural order. -/
def evalOnDomain (D : Domain R) (p : CPolynomial.Raw R) : Array R :=
  Array.ofFn (fun k : D.Idx => p.eval (D.node k))

/-- `evalOnDomain` is `evalBatch` specialized to the NTT domain nodes. -/
theorem evalOnDomain_eq_evalBatch (D : Domain R) (p : CPolynomial R) :
    evalOnDomain D p.val =
      evalBatch p (Array.ofFn (fun k : D.Idx => D.node k)) := by
  apply Array.ext
  · simp [evalOnDomain, evalBatch]
  · intro i hi₁ hi₂
    let k : D.Idx := ⟨i, by simpa [evalOnDomain] using hi₁⟩
    simp [evalOnDomain, evalBatch, CPolynomial.eval, CPolynomial.Raw.eval,
      CPolynomial.Raw.eval₂]

namespace Forward

/-- Pointwise form: the forward NTT specification evaluates a raw polynomial at a domain node. -/
theorem forwardSpec_eval_node_eq (D : Domain R) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < D.n) (k : D.Idx) :
    (forwardSpec D p)[k.1] = p.eval (D.node k) := by
  calc
    (forwardSpec D p)[k.1]
        = ∑ j : D.Idx, p.coeff j.1 * (D.node k) ^ (j : Nat) := by
            simp [forwardSpec, nttAt, Domain.node, CPolynomial.Raw.coeff, pow_mul]
    _ = ∑ j ∈ Finset.range D.n, p.toPoly.coeff j * (D.node k) ^ j := by
            change (∑ j : Fin D.n,
                (fun j : Nat => p.coeff j * (D.node k) ^ j) j) =
              ∑ j ∈ Finset.range D.n, p.toPoly.coeff j * (D.node k) ^ j
            rw [Fin.sum_univ_eq_sum_range
              (f := fun j : Nat => p.coeff j * (D.node k) ^ j) (n := D.n)]
            apply Finset.sum_congr rfl
            intro j _
            rw [CPolynomial.Raw.coeff_toPoly]
    _ = p.toPoly.eval (D.node k) := by
            rw [Polynomial.eval_eq_sum_range' hdeg]
    _ = p.eval (D.node k) := by
            exact CPolynomial.Raw.eval_toPoly_eq_eval (D.node k) p

/-- The forward NTT specification evaluates a raw polynomial on all domain nodes. -/
theorem forwardSpec_eq_evalOnDomain (D : Domain R) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < D.n) :
    forwardSpec D p = evalOnDomain D p := by
  apply Array.ext
  · simp [forwardSpec, evalOnDomain]
  · intro i hi₁ hi₂
    let k : D.Idx := ⟨i, by simpa [forwardSpec] using hi₁⟩
    simpa [evalOnDomain, k] using forwardSpec_eval_node_eq D p hdeg k

/-- Pointwise form: the forward NTT implementation evaluates a raw polynomial at a domain node. -/
theorem forwardImpl_eval_node_eq (D : Domain R) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < D.n) (k : D.Idx) :
    (forwardImpl D p).getD k.1 0 = p.eval (D.node k) := by
  rw [forwardImpl_correct]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem]
  exact forwardSpec_eval_node_eq D p hdeg k

/-- The forward NTT implementation evaluates a raw polynomial on all domain nodes. -/
theorem forwardImpl_eq_evalOnDomain (D : Domain R) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < D.n) :
    forwardImpl D p = evalOnDomain D p := by
  rw [forwardImpl_correct]
  exact forwardSpec_eq_evalOnDomain D p hdeg

end Forward
end NTT
end CPolynomial
end CompPoly
