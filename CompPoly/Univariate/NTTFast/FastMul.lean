/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.NTTFast.Forward
import CompPoly.Univariate.NTTFast.Inverse

/-!
# Experimental fast multiplication via NTT

This file mirrors the executable NTT multiplication pipeline while routing
through `NTTFast` transform entry points. It is a benchmark target for future
runtime optimizations; the existing `CompPoly.Univariate.NTT.FastMul` module
remains the proved baseline.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

/-- Pointwise multiplication in evaluation form. -/
@[inline] def pointwiseMul (D : NTT.Domain R) (a b : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD i.1 0 * b.getD i.1 0)

namespace Raw

/--
Raw experimental pipeline for NTT-based multiplication.

Correctness as ordinary polynomial multiplication requires the same fit condition
as the baseline NTT implementation. This raw API deliberately does not trim.
-/
@[inline] def fastMulImpl [BEq R]
    (D : NTT.Domain R) (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  let pHat := Forward.forwardImpl D p
  let qHat := Forward.forwardImpl D q
  let cHat := pointwiseMul D pHat qHat
  let c := Inverse.inverseImpl D cHat
  NTT.Domain.truncate (NTT.Domain.requiredLength p q) c

end Raw

/-- Experimental pipeline for NTT-based multiplication as a canonical polynomial. -/
@[inline] def fastMulImpl [BEq R] [LawfulBEq R]
    (D : NTT.Domain R) (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.fastMulImpl D p.val q.val).trim,
    CPolynomial.Raw.Trim.isCanonical_trim (Raw.fastMulImpl D p.val q.val)⟩

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
