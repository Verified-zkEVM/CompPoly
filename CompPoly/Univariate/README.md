# Univariate Polynomials

Formally verified computable univariate polynomials for [CompPoly](../../README.md), built on array-backed coefficient representation.

This is the largest subtree in the library. It is grouped below by role rather
than listed flat: the representation and its Mathlib bridge come first, then
arithmetic, interpolation, the fast transforms, and finally the algorithms built
on top (root finding and Reed-Solomon coding).

## Types

| Type | Description |
|------|-------------|
| `CPolynomial.Raw R` | Raw polynomials as coefficient arrays. Multiple arrays represent the same polynomial via zero-padding (e.g. `#[1,2,3]` = `#[1,2,3,0,0,...]`). |
| `CPolynomial R` | Canonical polynomials: `{ p : Raw R // p.trim = p }`. Unique representation, no trailing zeros. |
| `QuotientCPolynomial R` | Quotient of `Raw R` by coefficient-wise equivalence; intended equivalent of Mathlib's `Polynomial R`. |

## Representation

- **Raw.lean** — Umbrella import for the raw array-backed representation and its split implementation files.
- **Raw/Core.lean** — Raw datatype and core operations (`coeff`, `C`, `X`, `monomial`, `trim`, `degree`, `eval`).
- **Raw/Ops.lean** — Raw algebraic operations and related operational lemmas.
- **Raw/Division.lean** — Raw polynomial division APIs (`divByMonic`, `modByMonic`, `div`, `mod`). Only `[BEq R]` is shared at section scope; the monic-division definitions need just `[CommRing R]`.
- **Raw/Modular.lean** — Raw modular arithmetic.
- **Raw/Context.lean** — Raw-level algorithm dictionaries backing the canonical contexts.
- **Raw/Proofs.lean** — Proof layer for the raw API (algebraic laws and operation correctness).
- **Basic.lean** — Canonical `CPolynomial` with ring structure (Add, Mul, Zero, One, etc.).
- **Quotient/Core.lean** — Quotient type and operations descending from `Raw`.
- **Quotient/Equiv.lean** — Equivalence between the quotient representation and canonical `CPolynomial`.

## Mathlib bridge

- **ToPoly.lean** — Umbrella import for conversion/equivalence with Mathlib's `Polynomial R`.
- **ToPoly/Core.lean** — Core conversion maps and API lemmas.
- **ToPoly/Equiv.lean** — Round-trip theorems and ring equivalence with Mathlib polynomials.
- **ToPoly/Degree.lean** — Degree/support transport lemmas for conversions, plus `degreeLT` / `degreeLTEquiv`.
- **ToPoly/Impl.lean** — Implementation-facing transport lemmas.
- **CMvEquiv.lean** — Ring equivalence `CPolynomial R ≃+* CMvPolynomial 1 R`, via `CPolynomial R ≃ R[X] ≃ (CMvPolynomial 0 R)[X] ≃ CMvPolynomial 1 R`.

## Arithmetic and structure

- **Linear.lean** — Linear-factor and affine helper lemmas for univariate workflows.
- **Deriv.lean** — Formal derivative `CPolynomial.derivative` and the Taylor shift `CPolynomial.taylor`.
- **Modular.lean** — Executable modular arithmetic over the `MulContext` / `ModContext` backends.
- **DivisionCorrectness.lean** — Correctness theorems for the division-style algorithms.
- **EuclideanAlgorithm.lean** — Extended Euclid: `xgcd p q` returns `(r, s, t)` with `r = s * p + t * q`, with an early stop once `r.natDegree < threshold` (characterized by `xgcd_stopSpec` / `BezoutStopSpec`). Threshold `0` gives the plain gcd; positive thresholds are what the Gao decoder needs.
- **Vanishing.lean** — Executable `∏ x in xs, (X - x)` for an array of nodes.
- **Context.lean** — Algorithm dictionaries (`MulContext`, `ModContext`, …) with canonical, NTT, and NTTFast-backed implementations. This is how a caller swaps a multiplication backend without changing proofs.

## Interpolation and evaluation

- **Lagrange.lean** — Lagrange interpolation: `nodal`, `interpolate`, `interpolatePow`.
- **LagrangeArray.lean** — Finite-index array adapters for `CLagrange.interpolate`.
- **CoefficientInterpolation.lean** — Coefficient-form interpolation from the node vanishing polynomial, via `R = ∑ᵢ yᵢ / G'(xᵢ) · G / (X - xᵢ)`.
- **Barycentric.lean** — Fixed-domain barycentric interpolation with precomputed weights, for repeated queries over one node set.
- **BatchEval/** — Batch evaluation at many points: `Naive`, `SubproductTree`, a `Context` for pluggable multiply/remainder backends, and `Correctness`.
- **ManyEval/** — The transposed workload: many dense polynomials at one shared point (`Basic`, `Correctness`).

## Fast transforms

- **NTT/** — Radix-2 root-of-unity transforms: `Domain`, `Forward`, `Inverse`, `Transform`, `Kernel`, the `Evaluation` and `Interpolation` bridge theorems, `FastMul` and `FastMulLow`, and the concrete `BabyBear` / `KoalaBear` domains.
- **NTTFast/** — The optimized path: `Plan` (cached twiddle plans, DIF and radix-4 stages), `Evaluation`, `Interpolation`, `FastMul`, `FastMulLow`, and `Correctness/` proving refinement against the `NTT` specifications.

Write proofs against `NTT`; call `NTTFast`.

## Root finding and coding

- **Roots/** — Backend-parametric univariate root finding over finite fields: the `Context` / `Backend` / `Splitter` interfaces, `Extraction`, `RootProduct`, `Correctness`, and `SmoothSubgroup/` for fields with a smooth multiplicative-subgroup schedule.
- **ReedSolomon.lean** — The code itself: `Domain`, `messagePoly`, `encode`.
- **ReedSolomon/NTTEncode.lean** — The forward NTT *is* the encoder (`forwardImpl_eq_encode`).
- **ReedSolomon/GaoDecoder.lean**, **ReedSolomon/GaoCorrectness.lean** — Gao's unique decoder, with soundness, completeness, and `decode_none_farness`.

Both are covered in depth by [`../../docs/wiki/coding-theory.md`](../../docs/wiki/coding-theory.md).

## Example

```lean
-- Array #[1, 2, 3] represents 1 + 2X + 3X²
#check CPolynomial.X      -- #[0, 1]
#check CPolynomial.C 5       -- #[5]
#check CPolynomial.monomial 2 3  -- 3·X²
```
