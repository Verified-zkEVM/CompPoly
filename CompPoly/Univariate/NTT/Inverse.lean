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
def inttAtVec (D : Domain R) (v : EvalVec R D) (k : D.Idx) : R :=
  D.nInv * ∑ j : D.Idx, v.get j * D.omegaInv ^ ((k : Nat) * (j : Nat))

/-- Full inverse transform on vectors, specified from `inttAtVec`. -/
def inverseVecSpec (D : Domain R) (v : EvalVec R D) : EvalVec R D :=
  Vector.ofFn (fun k : D.Idx => inttAtVec D v k)

/-- Convert inverse-transform output vector back to a raw polynomial. -/
def inverseSpec (D : Domain R) (v : EvalVec R D) : CPolynomial.Raw R :=
  -- TODO: Revisit whether inverse output should be normalized/truncated here or at call sites.
  (inverseVecSpec D v).toArray

/-- Placeholder inverse implementation on vectors. -/
def inverseImplVec (D : Domain R) (v : EvalVec R D) : EvalVec R D :=
  -- TODO: Replace this spec call with the dedicated iterative inverse NTT.
  inverseVecSpec D v

/-- Placeholder inverse implementation returning coefficients. -/
def inverseImpl (D : Domain R) (v : EvalVec R D) : CPolynomial.Raw R :=
  -- TODO: Replace this spec call once `inverseImplVec` has its own runtime implementation.
  inverseSpec D v

theorem inverseImplVec_correct (D : Domain R) (v : EvalVec R D) :
    inverseImplVec D v = inverseVecSpec D v := by
  rfl

theorem inverseImpl_correct (D : Domain R) (v : EvalVec R D) :
    inverseImpl D v = inverseSpec D v := by
  rfl

end Inverse
end NTT
end CPolynomial
end CompPoly
