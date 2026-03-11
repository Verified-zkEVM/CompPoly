# Bivariate Polynomials

Formally verified computable bivariate polynomials for [CompPoly](../../README.md), represented as `CPolynomial (CPolynomial R)` — polynomials in Y whose coefficients are univariate polynomials in X. Matches Mathlib's `R[X][Y]` and is compatible with [ArkLib](https://github.com/Verified-zkEVM/ArkLib)'s `Polynomial.Bivariate` interface.

## Type

| Type | Description |
|------|-------------|
| `CBivariate R` | `CPolynomial (CPolynomial R)` — canonical polynomials in Y with polynomial-in-X coefficients. Same structure as Mathlib's `Polynomial (Polynomial R)`. |

## Modules

- **Basic.lean** — Type definition, constructors (`CC`, `C_X`, `Y`, `monomialXY`), operations (`coeff`, `evalX`, `evalY`, `evalEval`, `degreeX`, `natDegreeY`, `totalDegree`, `leadingCoeffY`, `leadingCoeffX`, `swap`, `support`).
- **ToPoly.lean** — Conversion to/from Mathlib's `R[X][Y]` via `toPoly` and `ofPoly`, with round-trip theorems, ring equivalence, and correctness lemmas for coefficients, evaluation, support, and degree APIs.

## Indexing

- `coeff f i j` = coefficient of `X^i Y^j` (X is inner variable, Y is outer).
- Outer structure: indexed by powers of Y.
- Inner structure: each Y-coefficient is a `CPolynomial R` (polynomial in X).
