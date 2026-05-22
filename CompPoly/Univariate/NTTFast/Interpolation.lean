/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Interpolation
import CompPoly.Univariate.NTTFast.Correctness.Pipeline

/-!
# NTTFast and Interpolation

Bridge theorem declarations deriving NTTFast interpolation facts from the shared
NTT specification layer.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

namespace Plan

/--
A well-formed planned inverse interpolates the natural-order values when called on
the corresponding bit-reversed value array.
-/
theorem inverseImpl_interpolatePow [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (values : Array R) :
    CPolynomial.Raw.trim (inverseImpl P (NTT.Transform.bitRevPermute P.domain values)) =
      (CLagrange.interpolatePow P.domain.omega
        (NTT.loadNaturalVector P.domain values)).val := by
  rw [inverseImpl_correct P hP values]
  exact NTT.Inverse.inverseSpec_interpolatePow P.domain values

/-- Pointwise form of `inverseImpl_interpolatePow` for a well-formed planned inverse. -/
theorem inverseImpl_eval_node
    (P : Plan R) (hP : WellFormed P) (values : Array R) (k : P.domain.Idx) :
    CPolynomial.Raw.eval (P.domain.node k)
      (inverseImpl P (NTT.Transform.bitRevPermute P.domain values)) = values.getD k.1 0 := by
  rw [inverseImpl_correct P hP values]
  exact NTT.Inverse.inverseSpec_eval_node P.domain values k

/-- A well-formed planned inverse evaluates back to the natural-order input values. -/
theorem inverseImpl_evalOnDomain
    (P : Plan R) (hP : WellFormed P) (values : Array R) :
    NTT.evalOnDomain P.domain (inverseImpl P (NTT.Transform.bitRevPermute P.domain values)) =
      NTT.loadNaturalArray P.domain values := by
  rw [inverseImpl_correct P hP values]
  exact NTT.Inverse.inverseSpec_evalOnDomain P.domain values

end Plan
end NTTFast
end CPolynomial
end CompPoly
