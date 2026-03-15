/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Univariate.NTT.Forward

/-!
# Inverse NTT Scaffolding

This file provides placeholder inverse NTT APIs and correctness statement
targets for future implementation/proofs.
-/

open scoped BigOperators

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Inverse

variable {R : Type*} [Field R]

/-- Inverse NTT formula at one output index. -/
def inttAt (D : Domain R) (v : Array R) (k : D.Idx) : R :=
  D.nInv * ∑ j : D.Idx, v.getD j.1 0 * D.omegaInv ^ ((k : Nat) * (j : Nat))

/-- Full inverse transform on arrays, specified from `inttAt`. -/
def inverseArraySpec (D : Domain R) (v : Array R) : Array R :=
  Array.ofFn (fun k : D.Idx => inttAt D v k)

/-- Convert inverse-transform output array back to raw polynomial coefficients. -/
def inverseSpec (D : Domain R) (v : Array R) : CPolynomial.Raw R :=
  -- TODO: Revisit whether inverse output should be normalized/truncated here or at call sites.
  inverseArraySpec D v

@[simp] theorem size_inverseArraySpec (D : Domain R) (v : Array R) :
    (inverseArraySpec D v).size = D.n := by
  simp [inverseArraySpec]

@[simp] theorem size_inverseSpec (D : Domain R) (v : Array R) :
    (inverseSpec D v).size = D.n := by
  simp [inverseSpec]

/-- Placeholder inverse implementation returning coefficients. -/
def inverseImpl (D : Domain R) (v : Array R) : CPolynomial.Raw R :=
  -- TODO: Replace this spec call with the dedicated iterative inverse NTT.
  inverseSpec D v

theorem inverseImpl_correct (D : Domain R) (v : Array R) :
    inverseImpl D v = inverseSpec D v := by
  rfl

end Inverse
end NTT
end CPolynomial
end CompPoly
