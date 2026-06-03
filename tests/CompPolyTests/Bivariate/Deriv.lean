/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
import CompPoly.Bivariate.Deriv
import Mathlib.Data.ZMod.Basic

/-!
# Bivariate Multiplicity Tests

Regression coverage for `CompPoly.CBivariate.checkMultiplicity`, the executable
multiplicity check used by the Guruswami–Sudan interpolation step.

The checks pin down the behaviour over finite fields of small characteristic,
where the multiplicity must be read off the shifted polynomial `Q(X + a, Y + b)`
rather than from ordinary partial derivatives: the latter acquire factorial
factors that vanish mod `p` and therefore *overcount* multiplicity. The two
`false` cases below are precisely the configurations an ordinary-derivative
definition would mis-report, so they guard against such a regression.

These are `#guard` checks: they run under `lake test` (via the `CompPolyTests`
driver) and are not elaborated by `lake build`.
-/

open CompPoly CompPoly.CBivariate

namespace CompPolyTests.Bivariate.Deriv

-- `X²` over `𝔽₂` has multiplicity exactly `2` at the origin, so multiplicity `≥ 3` is false.
-- (An ordinary-derivative check reports `true` here, since `∂ₓ²(X²) = 2 = 0` in `𝔽₂`.)
#guard checkMultiplicity (monomialXY 2 0 1 : CBivariate (ZMod 2)) 3 0 0 == false

-- `X³` over `𝔽₃` has multiplicity exactly `3` at the origin, so multiplicity `≥ 5` is false.
-- (Every ordinary derivative of `X³` is a multiple of `3! = 0`.)
#guard checkMultiplicity (monomialXY 3 0 1 : CBivariate (ZMod 3)) 5 0 0 == false

-- `X²` over `𝔽₂` does have multiplicity `≥ 2` at the origin.
#guard checkMultiplicity (monomialXY 2 0 1 : CBivariate (ZMod 2)) 2 0 0 == true

-- The zero polynomial has multiplicity `≥ r` at every point.
#guard checkMultiplicity (0 : CBivariate (ZMod 2)) 4 0 0 == true

-- A nonzero evaluation point: `(X - 1)²` has multiplicity `≥ 2` at `X = 1`.
#guard checkMultiplicity
    (monomialXY 2 0 1 - monomialXY 1 0 2 + monomialXY 0 0 1 : CBivariate (ZMod 3)) 2 1 0 == true

-- ... and not `≥ 3` there: the multiplicity of `(X - 1)²` at `X = 1` is exactly `2`.
#guard checkMultiplicity
    (monomialXY 2 0 1 - monomialXY 1 0 2 + monomialXY 0 0 1 : CBivariate (ZMod 3)) 3 1 0 == false

end CompPolyTests.Bivariate.Deriv
