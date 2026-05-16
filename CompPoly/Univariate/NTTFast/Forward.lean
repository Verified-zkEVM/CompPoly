/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Transform

/-!
# Experimental forward NTT

This file mirrors the executable forward-transform entry point from
`CompPoly.Univariate.NTT.Forward`, but routes through the `NTTFast` transform
copy so the transform can be optimized independently.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast
namespace Forward

variable {R : Type*} [Field R]

/-- Experimental forward NTT implementation entry point. -/
@[inline] def forwardImpl (D : NTT.Domain R) (p : CPolynomial.Raw R) : Array R :=
  Transform.runStages D (Transform.bitRevPermute D p)

end Forward
end NTTFast
end CPolynomial
end CompPoly
