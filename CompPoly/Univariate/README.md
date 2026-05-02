# Univariate Polynomials

Formally verified computable univariate polynomials for [CompPoly](../../README.md), built on array-backed coefficient representation.

## Types

| Type | Description |
|------|-------------|
| `CPolynomial.Raw R` | Raw polynomials as coefficient arrays. Multiple arrays represent the same polynomial via zero-padding (e.g. `#[1,2,3]` = `#[1,2,3,0,0,...]`). |
| `CPolynomial R` | Canonical polynomials: `{ p : Raw R // p.trim = p }`. Unique representation, no trailing zeros. |
| `QuotientCPolynomial R` | Quotient of `Raw R` by coefficient-wise equivalence; intended equivalent of Mathlib's `Polynomial R`. |

## Modules

- **Raw.lean** — Umbrella import for the raw array-backed representation and its split implementation files.
- **Raw/Core.lean** — Raw datatype and core operations (`coeff`, `C`, `X`, `monomial`, `trim`, `degree`, `eval`).
- **Raw/Ops.lean** — Raw algebraic operations and related operational lemmas.
- **Raw/Division.lean** — Raw polynomial division APIs (`divByMonic`, `modByMonic`, `div`, `mod`).
- **Raw/Proofs.lean** — Proof layer for the raw API (algebraic laws and operation correctness).
- **Basic.lean** — Canonical `CPolynomial` with ring structure (Add, Mul, Zero, One, etc.).
- **Quotient.lean** — Quotient type and operations descending from `Raw`.
- **QuotientEquiv.lean** — Equivalence between the quotient representation and canonical `CPolynomial`.
- **ToPoly.lean** — Umbrella import for conversion/equivalence with Mathlib's `Polynomial R`.
- **ToPoly/Core.lean** — Core conversion maps and API lemmas.
- **ToPoly/Equiv.lean** — Round-trip theorems and ring equivalence with Mathlib polynomials.
- **ToPoly/Degree.lean** — Degree/support transport lemmas for conversions.
- **Lagrange.lean** — Lagrange interpolation: `nodal`, `interpolate` at roots of unity.
- **Barycentric.lean** — Fixed-domain barycentric interpolation with precomputed weights and
  correctness lemmas comparing repeated-query evaluation against `Lagrange.interpolate` and
  `CLagrange.interpolate`.
- **Linear.lean** — Linear-factor and affine helper lemmas for univariate workflows.

## Example

```lean
-- Array #[1, 2, 3] represents 1 + 2X + 3X²
#check CPolynomial.X      -- #[0, 1]
#check CPolynomial.C 5       -- #[5]
#check CPolynomial.monomial 2 3  -- 3·X²
```
