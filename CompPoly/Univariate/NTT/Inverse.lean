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

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- Inverse NTT formula at one output index. -/
def inttAtVec (D : Domain R) (v : EvalVec R D) (k : D.Idx) : R := by
  -- TODO: Implement inverse formula using `D.omegaInv` and normalization.
  sorry

/-- Full inverse transform on vectors, specified from `inttAtVec`. -/
def inverseVecSpec (D : Domain R) (v : EvalVec R D) : EvalVec R D := by
  -- TODO: Build vector by evaluating `inttAtVec` at each index.
  sorry

/-- Convert inverse-transform output vector back to a raw polynomial. -/
def inverseSpec (D : Domain R) (v : EvalVec R D) : CPolynomial.Raw R := by
  -- TODO: Apply normalization by `D.nInv`, and finalize shape/truncation conventions.
  sorry

/-- Placeholder inverse implementation on vectors. -/
def inverseImplVec (D : Domain R) (v : EvalVec R D) : EvalVec R D := by
  -- TODO: Replace with iterative radix-2 inverse implementation.
  sorry

/-- Placeholder inverse implementation returning coefficients. -/
def inverseImpl (D : Domain R) (v : EvalVec R D) : CPolynomial.Raw R := by
  -- TODO: Connect `inverseImplVec` to coefficient extraction.
  sorry

theorem inverseImplVec_correct (D : Domain R) (v : EvalVec R D) :
    inverseImplVec D v = inverseVecSpec D v := by
  sorry

theorem inverseImpl_correct (D : Domain R) (v : EvalVec R D) :
    inverseImpl D v = inverseSpec D v := by
  sorry

end Inverse
end NTT
end CPolynomial
end CompPoly
