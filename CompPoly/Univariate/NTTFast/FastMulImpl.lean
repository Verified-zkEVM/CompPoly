/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Domain

/-!
# Shared NTTFast multiplication helpers

This file contains small helpers shared by direct and planned `NTTFast`
multiplication implementations.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

/-- Pointwise multiplication in evaluation form. -/
@[inline] def pointwiseMul (D : NTT.Domain R) (a b : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD i.1 0 * b.getD i.1 0)

end NTTFast
end CPolynomial
end CompPoly
