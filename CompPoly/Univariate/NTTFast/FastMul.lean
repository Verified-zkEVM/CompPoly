/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTTFast.Plan

/-!
# Experimental fast multiplication via NTT

This file exposes the direct experimental NTT multiplication entry point. It
builds a one-shot `NTTFast.Plan` and then routes through the planned
implementation. The existing `CompPoly.Univariate.NTT.FastMul` module remains
the proved baseline.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

namespace Raw

/--
Raw experimental pipeline for NTT-based multiplication.

Correctness as ordinary polynomial multiplication requires the same fit condition
as the baseline NTT implementation. This raw API deliberately does not trim.
-/
@[inline] def fastMulImpl [BEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let plan := Plan.ofDomain D
  Plan.Raw.fastMulImpl plan p q

end Raw

/-- Experimental pipeline for NTT-based multiplication as a canonical polynomial. -/
@[inline] def fastMulImpl [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) : CPolynomial R :=
  let plan := Plan.ofDomain D
  Plan.fastMulImpl plan p q

/--
Safe experimental NTT-based multiplication wrapper.

The proof argument records the same sufficient length condition used by the
baseline NTT API; this experimental wrapper is intended for benchmark routing.
-/
@[inline] def safeFastMul [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) (_hfit : NTT.Domain.fits D p.val q.val) :
    CPolynomial R :=
  fastMulImpl D p q

end NTTFast
end CPolynomial
end CompPoly
