# Representations And Bridges

CompPoly has several distinct polynomial representations. Picking the right one is
usually the first architectural decision in a change.

## At A Glance

| Surface | Main type(s) | Best for | Main entrypoints |
|---|---|---|---|
| Univariate | `CPolynomial.Raw R`, `CPolynomial R`, `QuotientCPolynomial R` | Canonical coefficient-sequence arithmetic, quotient reasoning, interpolation | `CompPoly/Univariate/README.md`, `CompPoly/Univariate/Basic.lean`, `CompPoly/Univariate/ToPoly.lean` |
| Multivariate | `CMvPolynomial n R` | Sparse computable multivariate operations and `MvPolynomial` interop | `CompPoly/Multivariate/CMvPolynomial.lean`, `CompPoly/Multivariate/Operations.lean`, `CompPoly/Multivariate/MvPolyEquiv.lean` |
| Multilinear | `CMlPolynomial R n`, `CMlPolynomialEval R n` | Boolean-hypercube evaluation form, basis conversion, multilinear extensions | `CompPoly/Multilinear/Basic.lean`, `CompPoly/Multilinear/Equiv.lean` |
| Bivariate | `CBivariate R` | Specialized two-variable APIs and `R[X][Y]` transport | `CompPoly/Bivariate/README.md`, `CompPoly/Bivariate/Basic.lean`, `CompPoly/Bivariate/ToPoly.lean`, `CompPoly/ToMathlib/Polynomial/BivariateDegree.lean`, `CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean`, `CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean` |

## Univariate Family

The univariate stack distinguishes between three closely related views:

- `CPolynomial.Raw R` is the array-backed representation where trailing zeros are
  allowed.
- `CPolynomial R` is the canonical trimmed representation.
- `QuotientCPolynomial R` is the quotient model that packages coefficient-wise
  equivalence on raw arrays.

Use `Raw` when implementation detail matters, `CPolynomial` for normal user-facing
 work, and `QuotientCPolynomial` when quotient reasoning is the cleanest proof
 boundary.

The main bridge to Mathlib lives in:

- [`../../CompPoly/Univariate/ToPoly/Core.lean`](../../CompPoly/Univariate/ToPoly/Core.lean)
- [`../../CompPoly/Univariate/ToPoly/Equiv.lean`](../../CompPoly/Univariate/ToPoly/Equiv.lean)
- [`../../CompPoly/Univariate/ToPoly/Degree.lean`](../../CompPoly/Univariate/ToPoly/Degree.lean)

For interpolation work, also read:

- [`../../CompPoly/Univariate/Lagrange.lean`](../../CompPoly/Univariate/Lagrange.lean)
  for the baseline interpolation surface and correctness statements.
- [`../../CompPoly/Univariate/Barycentric.lean`](../../CompPoly/Univariate/Barycentric.lean)
  for repeated-query barycentric evaluation over a fixed node set with precomputed
  barycentric weights.

## Multivariate Family

`CMvPolynomial n R` is the sparse computable multivariate surface highlighted in the
root README. It is the right place for:

- computable monomial-based operations,
- evaluation and substitution APIs,
- variable renaming and restriction,
- support and degree queries,
- transport to Mathlib `MvPolynomial (Fin n) R`.

The main split is:

- [`../../CompPoly/Multivariate/CMvPolynomial.lean`](../../CompPoly/Multivariate/CMvPolynomial.lean)
  for core type-level definitions,
- [`../../CompPoly/Multivariate/Operations.lean`](../../CompPoly/Multivariate/Operations.lean)
  for the higher-level operation surface,
- [`../../CompPoly/Multivariate/MvPolyEquiv/`](../../CompPoly/Multivariate/MvPolyEquiv/)
  for ring instances and bridge lemmas.

## Multilinear Family

The multilinear stack is easy to miss if you only read the old top-level summary.
It already has two distinct computable forms:

- `CMlPolynomial R n` for monomial-basis coefficients,
- `CMlPolynomialEval R n` for evaluation values on `{0,1}^n`.

These are both represented as vectors of length `2 ^ n`, with little-endian indexing.
That design is described directly in
[`../../CompPoly/Multilinear/Basic.lean`](../../CompPoly/Multilinear/Basic.lean).

Use this area for:

- Boolean-hypercube evaluation form,
- zeta / Mobius style basis transforms,
- multilinear-extension equivalences,
- fast multilinear pathways that do not fit the sparse `CMvPolynomial` API.

## Bivariate Family

`CBivariate R` is the specialized `CPolynomial (CPolynomial R)` layer. Use it when
the problem is truly two-variable and a dedicated API is clearer than treating the
code as generic multivariate syntax.

The key files are:

- [`../../CompPoly/Bivariate/Basic.lean`](../../CompPoly/Bivariate/Basic.lean)
- [`../../CompPoly/Bivariate/ToPoly.lean`](../../CompPoly/Bivariate/ToPoly.lean)
- [`../../CompPoly/ToMathlib/Polynomial/BivariateDegree.lean`](../../CompPoly/ToMathlib/Polynomial/BivariateDegree.lean)
- [`../../CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean`](../../CompPoly/ToMathlib/Polynomial/BivariateWeightedDegree.lean)
- [`../../CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean`](../../CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean)
- [`../../CompPoly/Bivariate/README.md`](../../CompPoly/Bivariate/README.md)

## Bridge Layers

When the task is "prove the computable thing agrees with Mathlib", start in the
bridge layer rather than the implementation file:

- Univariate bridge: `Univariate/ToPoly/*`
- Multivariate bridge: `Multivariate/MvPolyEquiv/*`
- Bivariate bridge: `Bivariate/ToPoly.lean` plus `ToMathlib/Polynomial/BivariateDegree.lean`, `ToMathlib/Polynomial/BivariateWeightedDegree.lean`, and `ToMathlib/Polynomial/BivariateMultiplicity.lean`
- Multilinear bridge: `Multilinear/Equiv.lean`
- Supporting upstream-facing lemmas: `ToMathlib/*`

The local `ToMathlib` subtree is especially useful when a proof needs a helper lemma
that conceptually belongs between CompPoly and Mathlib rather than inside one
specific polynomial representation.

## Choosing A Surface

- If you need canonical coefficient arrays and interpolation, start with
  `CPolynomial`; for repeated interpolation queries over a fixed domain, also
  inspect `Univariate/Barycentric.lean`.
- If you need sparse multivariate monomials or `MvPolynomial` equivalence, start
  with `CMvPolynomial`.
- If you need Boolean-cube evaluation data or multilinear transforms, start with
  `CMlPolynomial` or `CMlPolynomialEval`.
- If the API is naturally two-variable and you want `X` / `Y`-specific operations,
  start with `CBivariate`.
