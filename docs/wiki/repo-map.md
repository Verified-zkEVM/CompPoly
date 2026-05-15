# Repo Map

CompPoly is easiest to navigate by subtree and representation family, not by
individual file name.

## Main Surfaces

```text
CompPoly/
  Data/               shared helper lemmas and small support definitions
  ToMathlib/          local bridge lemmas and upstream-facing support code
  Univariate/         canonical computable univariate polynomials
  Multivariate/       sparse computable multivariate polynomials
  Multilinear/        multilinear coefficient and evaluation representations
  Bivariate/          specialized `CPolynomial (CPolynomial R)` layer
  Fields/             concrete fields plus binary-field and additive-NTT stack
tests/                regression modules under `CompPolyTests`
bench/                benchmark executable, runner docs, and local reports
scripts/              repo utilities and validation helpers
.github/workflows/    CI entrypoints and automation
```

## Conceptual Layering

- `CompPoly/Data/` and `CompPoly/ToMathlib/` support the rest of the library with
  helper lemmas, notation, and bridge infrastructure.
- `CompPoly/Univariate/`, `CompPoly/Multivariate/`, `CompPoly/Multilinear/`, and
  `CompPoly/Bivariate/` are the main user-facing polynomial surfaces.
- `CompPoly/Fields/` contains both the general field catalog and the more specialized
  binary-field, GHASH, tower, and additive-NTT developments.
- `tests/` mirrors the source tree when possible, but also contains cross-cutting
  regression modules for specialized subsystems.
- `bench/` contains the compiled benchmark entrypoint and benchmark-specific docs.

## Where To Start By Task

- Extending `CPolynomial`, quotient polynomials, or interpolation:
  start in `CompPoly/Univariate/`.
- Extending sparse monomial-based polynomial operations or `MvPolynomial`
  interoperability: start in `CompPoly/Multivariate/`.
- Working on Boolean-hypercube evaluation form, basis conversion, or multilinear
  equivalences: start in `CompPoly/Multilinear/`.
- Working on the specialized two-variable API or the `R[X][Y]` bridge:
  start in `CompPoly/Bivariate/`.
- Adding concrete fields, GHASH lemmas, tower-field infrastructure, or additive NTT:
  start in `CompPoly/Fields/`.
- Moving a reusable support lemma that should not live next to one specific feature:
  start in `CompPoly/Data/` or `CompPoly/ToMathlib/`.
- Adding regression coverage: start in `tests/` and mirror the source namespace when
  possible.
- Updating benchmark coverage or reports: start in `bench/`.

## Navigation Notes

- `CompPoly.lean` is a generated umbrella import file, not a hand-maintained module
  index.
- The root [`../../README.md`](../../README.md) is a good public overview, but it is
  intentionally higher level than the source tree.
- The existing subtree READMEs are a good first stop for the surfaces that already
  have them:
  - [`../../CompPoly/Univariate/README.md`](../../CompPoly/Univariate/README.md)
  - [`../../CompPoly/Bivariate/README.md`](../../CompPoly/Bivariate/README.md)
  - [`../../CompPoly/Fields/README.md`](../../CompPoly/Fields/README.md)
- Large feature edits usually require reading one layer outward from the current
  file: for example, a multivariate API change often touches `MvPolyEquiv/`,
  while an additive-NTT change often spans `Domain`, `Intermediate`, `Algorithm`,
  `Impl`, and `Correctness`.
