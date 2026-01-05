# CompPoly

A library for computational multivariate polynomial rings over a base commutative ring (or semiring), with variables indexed by natural numbers.

## Representation

A polynomial is represented by the type `CMvPolynomial (n : ℕ) (R : Type) [Zero R] : Type`, where `n` is the number of variables (indexed from 0) and `R` is the type of coefficients. 

This polynomial representation is implemented internally as a map from monomials in `n` variables (`CMvMonomial (n : ℕ) : Type`) to coefficients, with the constraint that no monomial maps to the `0` coefficient.
This implementation is then shown to be equivalent with a Mathlib polynomial ring with `Fin n` variables. More specifically, we instantiate a `RingEquiv` structure (modulo some typeclass constraints) between our type and `MvPolynomial (Fin n) R` which is defined in `Mathlib.Algebra.MvPolynomial.Basic`.

## Importing the library

If your project is using a `lakefile.lean`, you can add
```
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly"
```
or you can specify the exact commit, for example:
```
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly"@"ede2290"
```
If your project is using a `lakefile.toml`, you can add
```
[[require]]
name = "CompPoly"
git = "https://github.com/Verified-zkEVM/CompPoly"
```
or you can specify the exact commit, for example:
```
[[require]]
name = "CompPoly"
git = "https://github.com/Verified-zkEVM/CompPoly"
rev = "ede2290"
```

Then you can import the desired modules, for example:
```lean
import CompPoly.CMvPolynomial
```
```lean
import CompPoly.MvPolyEquiv
```

## Current status and plans

So far we have defined counterparts for the following `MvPolynomial` definitions:
`C`, `X`, `coeff`, `commSemiring`, `decidableEqMvPolynomial`, `degreeOf`, `eval`, `eval₂`, `support` and `totalDegree`. Many have the same name and are located in the namespace `CPoly.CMvPolynomial`; some are defined on `Lawful`, which `CMvPolynomial` is an abbrev of.

For the future, we plan to add counterparts to `MonomialOrder.degree`, `MonomialOrder.leadingCoeff` and the following `MvPolynomial` definitions (but we're first assessing the implementation complexity for some of them): `aeval`, `algebra`, `bind₁`, `degrees`, `eval₂Hom`, `finSuccEquiv`, `instCommRingMvPolynomial`, `isEmptyAlgEquiv`, `module`, `monomial`, `optionEquivLeft`, `rename`, `renameEquiv`, `restrictDegree`, `smulZeroClass`, `sumToIter`, `vars`.
