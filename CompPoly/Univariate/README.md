# Univariate Polynomials

Formally verified computable univariate polynomials for [CompPoly](../../README.md), built on array-backed coefficient representation.

## Types

| Type | Description |
|------|-------------|
| `CPolynomial.Raw R` | Raw polynomials as coefficient arrays. Multiple arrays represent the same polynomial via zero-padding (e.g. `#[1,2,3]` = `#[1,2,3,0,0,...]`). |
| `CPolynomial R` | Canonical polynomials: `{ p : Raw R // p.trim = p }`. Unique representation, no trailing zeros. |
| `QuotientCPolynomial R` | Quotient of `Raw R` by coefficient-wise equivalence; intended equivalent of Mathlib's `Polynomial R`. |

## Modules

- **Raw.lean** — Core datatype, `coeff`, `C`, `X`, `monomial`, `trim`, `degree`, `eval`, addition, multiplication, and proofs.
- **Basic.lean** — Canonical `CPolynomial` with ring structure (Add, Mul, Zero, One, etc.).
- **Quotient.lean** — Quotient type and operations descending from `Raw`.
- **ToPoly.lean** — Isomorphism with Mathlib's `Polynomial R` via `toPoly` and `ofPoly`, including round-trip lemmas.
- **Lagrange.lean** — Lagrange interpolation: `nodal`, `interpolate` at roots of unity.

## Example

```lean
-- Array #[1, 2, 3] represents 1 + 2X + 3X²
#check CPolynomial.X      -- #[0, 1]
#check CPolynomial.C 5       -- #[5]
#check CPolynomial.monomial 2 3  -- 3·X²
```
