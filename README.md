# CompPoly

A formally verified library for computable polynomial operations over finite fields and
general rings, supporting univariate, multivariate, multilinear, and bivariate
polynomials. It aims to serve as the mathematical foundation for zero-knowledge
circuit verification.

## Representation

- **Multivariate (`CMvPolynomial n R`)**: computable polynomials in `n` variables over coefficients `R`, represented internally as sparse monomial-to-coefficient maps (`CMvMonomial n → R`) with zero coefficients filtered out. The library provides a `RingEquiv` to Mathlib `MvPolynomial (Fin n) R`.
- **Multilinear (`CMlPolynomial R n`, `CMlPolynomialEval R n`)**: computable multilinear polynomials represented either by monomial-basis coefficients or by evaluations over `{0,1}^n`, both as vectors of length `2^n`, with equivalence to Mathlib's multilinear polynomial surface.
- **Univariate (`CPolynomial R`)**: canonical computable coefficient-sequence representation, with a `RingEquiv` to Mathlib `Polynomial R`.
- **Bivariate (`CBivariate R`)**: represented as `CPolynomial (CPolynomial R)` with dedicated bivariate operations, plus equivalence to `Polynomial (Polynomial R)`.

## Importing the library

If your project is using a `lakefile.lean`, you can add
```
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly"
```
or you can specify a version, for example:
```
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly"@"init"
```
If your project is using a `lakefile.toml`, you can add
```
[[require]]
name = "CompPoly"
git = "https://github.com/Verified-zkEVM/CompPoly"
```
or you can specify a version, for example:
```
[[require]]
name = "CompPoly"
git = "https://github.com/Verified-zkEVM/CompPoly"
rev = "init"
```

Then you can import the desired modules, for example:
```lean
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv
import CompPoly.Multilinear.Basic
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Lagrange
import CompPoly.Bivariate.Basic
import CompPoly.Fields.BabyBear
```
Or depend on the root package to get the full library:
```lean
import CompPoly
```

## Documentation

- [`AGENTS.md`](AGENTS.md) is the canonical root handbook for AI agents and
  agent-oriented tooling.
- [`docs/wiki/README.md`](docs/wiki/README.md) is the deeper repo wiki for
  quickstart commands, repo structure, generated files, representation choice, and
  the binary-field / additive-NTT stack.
- Human contributors should usually start with [`CONTRIBUTING.md`](CONTRIBUTING.md)
  and this wiki, then consult `AGENTS.md` when working with agent tooling or when
  the AI-specific guardrails are relevant.
- Existing subtree READMEs also provide focused entrypoints:
  [`CompPoly/Univariate/README.md`](CompPoly/Univariate/README.md),
  [`CompPoly/Bivariate/README.md`](CompPoly/Bivariate/README.md), and
  [`CompPoly/Fields/README.md`](CompPoly/Fields/README.md).

## Current status and plans

**Phase 1 status (Theoretical Foundation):** **essentially complete**.

### Implemented highlights

- **Multivariate (`CMvPolynomial`)**: full core API (`eval`, `eval₂`, `eval₂Hom`, `aeval`, `bind₁`, `rename`, `restrict*`, `finSuccEquiv`/`optionEquivLeft`, leading-term operations, `sumToIter`), plus `CommSemiring`/`CommRing`, algebra/scalar-action instances, and equivalence to Mathlib `MvPolynomial`.
- **Multilinear (`CMlPolynomial`, `CMlPolynomialEval`)**: coefficient and Boolean-hypercube evaluation representations, basis conversions, and equivalence to Mathlib's multilinear polynomial surface.
- **Univariate (`CPolynomial`)**: full ring structure, core operations (`C`, `X`, `monomial`, `coeff`, `eval`, `eval₂`, degree/leading/support), `ringEquiv` to Mathlib `Polynomial`, Lagrange interpolation (`basis`, `interpolate`, `interpolatePow`), and fixed-domain barycentric interpolation for repeated-query evaluation.
- **Bivariate (`CBivariate`)**: specialized `CPolynomial (CPolynomial R)` API with `X`, `Y`, `monomialXY`, evaluation, leading coefficients, `swap`, and equivalence to `Polynomial (Polynomial R)`.
- **Fields**: broad set of finite-field instances and extensions (including BabyBear/Goldilocks/BN254/BLS12 family), binary tower support, and additive NTT infrastructure.

### Current focus: Phase 2

Primary roadmap focus is now shifting to **Performance & Efficiency**: optimized field arithmetic, FFT/NTT-based multiplication, faster exponentiation, and improved evaluation/interpolation pathways, with proof-first correctness maintained throughout.

*Last updated: March 2026*
