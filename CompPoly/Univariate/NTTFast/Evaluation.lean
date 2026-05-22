/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Evaluation
import CompPoly.Univariate.NTTFast.Correctness.Basic
import CompPoly.Univariate.NTTFast.Correctness.Pipeline

/-!
# NTTFast and Evaluation

Bridge theorem declarations deriving NTTFast evaluation facts from the shared NTT
specification layer.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

namespace Plan

/--
A well-formed planned forward transform evaluates the raw polynomial on the NTT
domain, returning the values in bit-reversed order.
-/
theorem forwardImpl_evalOnDomain
    (P : Plan R) (hP : WellFormed P) (p : CPolynomial.Raw R)
    (hdeg : p.toPoly.natDegree < P.domain.n) :
    forwardImpl P p =
      NTT.Transform.bitRevPermute P.domain (NTT.evalOnDomain P.domain p) := by
  rw [forwardImpl_correct P hP p]
  rw [NTT.Forward.forwardSpec_evalOnDomain P.domain p hdeg]

end Plan
end NTTFast
end CPolynomial
end CompPoly
