/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Inverse
import CompPoly.Univariate.NTTFast.Transform

/-!
# Experimental inverse NTT

This file mirrors the executable inverse-transform entry point from
`CompPoly.Univariate.NTT.Inverse`, reusing the existing normalization helper and
routing the stage computation through `NTTFast.Transform`.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast
namespace Inverse

variable {R : Type*} [Field R]

/-- Experimental inverse NTT implementation entry point. -/
def inverseImpl (D : NTT.Domain R) (v : Array R) : CPolynomial.Raw R :=
  NTT.Inverse.normalize D (Transform.runStages D.inverse (Transform.bitRevPermute D.inverse v))

end Inverse
end NTTFast
end CPolynomial
end CompPoly
