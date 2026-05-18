/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Inverse
import CompPoly.Univariate.NTTFast.Transform

/-!
# NTTFast inverse NTT

This file defines the inverse NTT entry point implemented by inverse-domain
`NTTFast.Transform` stages followed by normalization.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast
namespace Inverse

variable {R : Type*} [Field R]

/-- NTTFast inverse NTT implementation entry point. -/
def inverseImpl (D : NTT.Domain R) (v : Array R) : CPolynomial.Raw R :=
  NTT.Inverse.normalize D (Transform.runStages D.inverse (Transform.bitRevPermute D.inverse v))

end Inverse
end NTTFast
end CPolynomial
end CompPoly
