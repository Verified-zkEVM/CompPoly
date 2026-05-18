/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Plan

/-!
# Fast multiplication via NTT

This file exposes the one-shot `NTTFast` multiplication entry point. It builds an
`NTTFast.Plan` for the given domain and runs the planned multiplication pipeline.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

namespace Raw

/--
Raw pipeline for NTT-based multiplication.

Correctness as ordinary polynomial multiplication requires `NTT.Domain.fits D p q`.
This raw API deliberately does not trim.
-/
@[inline] def fastMulImpl [BEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let plan := Plan.ofDomain D
  Plan.Raw.fastMulImpl plan p q

end Raw

/-- Pipeline for NTT-based multiplication as a canonical polynomial. -/
@[inline] def fastMulImpl [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) : CPolynomial R :=
  let plan := Plan.ofDomain D
  Plan.fastMulImpl plan p q

/--
Safe NTT-based multiplication wrapper.

The domain-fit proof requires the caller to show that the domain covers the
convolution length.
-/
@[inline] def safeFastMul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) (_hfit : NTT.Domain.fits D p.val q.val) :
    CPolynomial R :=
  fastMulImpl D p q

end NTTFast
end CPolynomial
end CompPoly
