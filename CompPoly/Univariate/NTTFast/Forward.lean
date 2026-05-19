/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Transform

/-!
# NTTFast forward NTT

This file defines the forward NTT entry point implemented by bit-reversal followed
by `NTTFast.Transform` stages.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast
namespace Forward

variable {R : Type*} [Field R]

/-- NTTFast forward NTT implementation entry point. -/
@[inline] def forwardImpl (D : NTT.Domain R) (p : CPolynomial.Raw R) : Array R :=
  Transform.runStages D (Transform.bitRevPermute D p)

end Forward
end NTTFast
end CPolynomial
end CompPoly
