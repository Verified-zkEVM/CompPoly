# Bivariate Polynomials

Formally verified computable bivariate polynomials for [CompPoly](../../README.md), represented as `CPolynomial (CPolynomial R)` — polynomials in Y whose coefficients are univariate polynomials in X. Matches Mathlib's `R[X][Y]` and is compatible with [ArkLib](https://github.com/Verified-zkEVM/ArkLib)'s `Polynomial.Bivariate` interface.

## Type

| Type | Description |
|------|-------------|
| `CBivariate R` | `CPolynomial (CPolynomial R)` — canonical polynomials in Y with polynomial-in-X coefficients. Same structure as Mathlib's `Polynomial (Polynomial R)`. |

## Modules

- **Basic.lean** — Type definition, constructors (`CC`, `C_X`, `Y`, `monomialXY`), operations (`coeff`, `evalX`, `evalY`, `evalEval`, `natDegreeX`, `natDegreeY`, `totalDegree`, `natWeightedDegree`, `leadingCoeffY`, `leadingCoeffX`, `swap`, `support`).
- **ToPoly.lean** — Conversion to/from Mathlib's `R[X][Y]` via `toPoly` and `ofPoly`, with round-trip theorems, ring equivalence, and correctness lemmas for coefficients, evaluation, support, and degree APIs.
- **Kronecker.lean** — Kronecker substitution (`kroneckerPack`, `kroneckerUnpack`) reducing bivariate multiplication to one univariate multiplication, with multiplicativity of packing and round-trip correctness under an X-degree bound (`kroneckerUnpack_mul`). Linear-time `*Fast` variants are proved equal to these, and `kroneckerUnpack_withFallback` routes the inner multiply through an NTT when a domain fits.
- **CoeffRows.lean** — Conversions between finite `Y`-coefficient rows and `CBivariate`.
- **CMvEquiv.lean** — Ring equivalence `CBivariate R ≃+* CMvPolynomial 2 R`, composing `CBivariate.ringEquiv` with `finSuccEquiv` and `isEmptyRingEquiv`.
- **Deriv.lean** — Partial derivatives (`partialDerivX`, `partialDerivY`, iterated and mixed) and the multiplicity condition `hasMultiplicity`, defined through the Taylor shift `shiftC a b Q = Q(X + a, Y + b)`. This is the multiplicity used by the Guruswami-Sudan interpolation step.
- **Factor.lean** — `evalYPoly`, `isLinearYFactor`, and `divByLinearY`: the computable factor theorem for the nested representation, deflating by a linear factor `Y - f(X)` over an arbitrary commutative ring.
- **FactorMonic.lean** — `divByLinearY_eq_divByMonic`, showing the bespoke synthetic division agrees with general monic Euclidean division at the coefficient ring `CPolynomial R`, so `divByLinearY` is a verified fast path.

## Guruswami-Sudan list decoder

**GuruswamiSudan/** is a 40-file subtree implementing Reed-Solomon list decoding on
top of this representation: a backend-parametric `Core` with dense and
Lee-O'Sullivan interpolation, Roth-Ruckenstein and Alekhnovich root search, and
soundness and completeness for each. It has its own wiki page —
[`../../docs/wiki/coding-theory.md`](../../docs/wiki/coding-theory.md) — and is the
main consumer of `Deriv.lean` and `Factor.lean` above.

Mathlib-facing helper files for `R[X][Y]` live under `CompPoly/ToMathlib/Polynomial/`:
- [`../ToMathlib/Polynomial/BivariateDegree.lean`](../ToMathlib/Polynomial/BivariateDegree.lean)
- [`../ToMathlib/Polynomial/BivariateWeightedDegree.lean`](../ToMathlib/Polynomial/BivariateWeightedDegree.lean)
- [`../ToMathlib/Polynomial/BivariateMultiplicity.lean`](../ToMathlib/Polynomial/BivariateMultiplicity.lean)

## Indexing

- `coeff f i j` = coefficient of `X^i Y^j` (X is inner variable, Y is outer).
- Outer structure: indexed by powers of Y.
- Inner structure: each Y-coefficient is a `CPolynomial R` (polynomial in X).
