/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Fin

/-!
# First-variable degree helpers for `MvPolynomial (Fin (n + 1)) R`

This file defines the maximal total degree contributed by the first `n` variables
(i.e., all variables except the last coordinate).
-/

namespace MvPolynomial

open Finsupp

section FirstVarsDegree

variable {n : ℕ} {R : Type*} [CommSemiring R]

/-- Maximal degree contributed by the first `n` variables of a polynomial on `Fin (n + 1)`.

This is the support supremum of the sum of coordinates on `Fin.castSucc`. -/
noncomputable def firstVarsDegree (P : MvPolynomial (Fin (n + 1)) R) : ℕ :=
  P.support.sup (fun α => ∑ i : Fin n, α (Fin.castSucc i))

/-- A support element bounds `firstVarsDegree` from below. -/
lemma le_firstVarsDegree_of_mem_support {P : MvPolynomial (Fin (n + 1)) R}
    {α : Fin (n + 1) →₀ ℕ} (hα : α ∈ P.support) :
    (∑ i : Fin n, α (Fin.castSucc i)) ≤ firstVarsDegree (R := R) P := by
  classical
  simpa using Finset.le_sup (s := P.support)
    (f := fun β : Fin (n + 1) →₀ ℕ => ∑ i : Fin n, β (Fin.castSucc i)) hα

/-- `firstVarsDegree` of a monomial with nonzero coefficient. -/
lemma firstVarsDegree_monomial (α : Fin (n + 1) →₀ ℕ) (c : R) (hc : c ≠ 0) :
    firstVarsDegree (R := R) (MvPolynomial.monomial α c) =
      (∑ i : Fin n, α (Fin.castSucc i)) := by
  classical
  have hsupp : (MvPolynomial.monomial α c).support = {α} := by
    rw [MvPolynomial.support_monomial, if_neg hc]
  simp [firstVarsDegree, hsupp]

end FirstVarsDegree

end MvPolynomial
