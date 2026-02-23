# CompPoly

A formally verified library for computable polynomial operations over finite fields and general rings, supporting univariate, multivariate, and bivariate polynomials. It aims to serve as the mathematical foundation for zero-knowledge circuit verification.

## Representation

**Multivariate:** A polynomial in `n` variables is represented by `CMvPolynomial (n : ℕ) (R : Type) [Zero R] : Type`, where `n` is the number of variables (indexed from 0) and `R` is the type of coefficients. 

`CMvPolynomial` is implemented internally as a map from monomials in `n` variables (`CMvMonomial n`) to coefficients, with the constraint that no monomial maps to the `0` coefficient. We instantiate a `RingEquiv` between `CMvPolynomial n R` and Mathlib's `MvPolynomial (Fin n) R` (`Mathlib.Algebra.MvPolynomial.Basic`).

**Univariate** polynomials use `CPolynomial R` (canonical coefficient sequences) and are in `RingEquiv` with Mathlib's `Polynomial R`. **Bivariate** polynomials are represented as `CPolynomial (CPolynomial R)` (`CBivariate R`) with specialized operations and an equivalence to `Polynomial (Polynomial R)`.

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

## Current status and plans

**Phase 1 progress (Theoretical Foundation):** approximately **50%** complete. See [ROADMAP.md](ROADMAP.md) for details and checkmarks.

### Implemented

- **Multivariate (`CMvPolynomial`):** `C`, `X`, `coeff`, `monomial`, `support`, `totalDegree`, `degreeOf`, `degrees`, `vars`, `eval`, `eval₂`, `restrictBy` / `restrictTotalDegree` / `restrictDegree`, `rename`, `renameEquiv`; `CommSemiring` instance and `polyRingEquiv` to Mathlib's `MvPolynomial (Fin n) R`. Stubs exist for `aeval`, `bind₁`, `MonomialOrder.degree`, `leadingCoeff` (proofs pending).

- **Univariate (`CPolynomial`):** Full ring structure (`Semiring`, `CommSemiring`, `Ring`, `CommRing`), `C`, `X`, `monomial`, `coeff`, `eval`, `eval₂`, `degree`, `natDegree`, `leadingCoeff`, `support`; `ringEquiv` with Mathlib's `Polynomial R`. Lagrange interpolation: `nodal` and `interpolate` (in `CompPoly.Univariate.Lagrange`). Quotient polynomials: `QuotientCPolynomial` with matching ring instances.

- **Bivariate:** Type `CBivariate R` as `CPolynomial (CPolynomial R)` with `X`, `Y`, `monomialXY`, `eval`, `leadingCoeffY`, `leadingCoeffX`, `swap`, and `toPoly` equivalence with `Polynomial (Polynomial R)`.

- **Fields:** Basic field and extension definitions (e.g. BabyBear, Goldilocks, BN254, BLS12_381, BLS12_377, KoalaBear, Mersenne, Secp256k1), binary tower, and additive NTT support.

### Still planned (Phase 1)

Counterparts or proofs for: `degreeLT` / `degreeLE` and related membership/equivalence for univariate; `MonomialOrder.degree` / `leadingCoeff` (without `sorry`); `aeval`, `bind₁`, `algebra`, `module`, `eval₂Hom`, `finSuccEquiv`, `optionEquivLeft`, `isEmptyAlgEquiv`, `smulZeroClass`, `sumToIter`; removing remaining `sorry`s and completing `CommRing` / `Algebra` / `Module` for `CMvPolynomial`.
