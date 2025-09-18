# CompPoly

A library for computaional multivariate polynomial rings over a base commutative ring (or semiring), with variables indexed by natural numbers.

## Representation

A polynomial is represented by the type `CMvPolynomial (n : ℕ) (R : Type) [Zero R] : Type`, where `n` is the number of variables (indexed from 0) and R is the type of coefficients. 

This polynomial representation is implemented internally as a map from monomials in `n` variables (`CMvMonomial (n : ℕ) : Type`) to coefficients, with the constraint that no monomial maps to the `0` coefficient. This implementation is then shown to be equivalent with a Mathlib polynomial ring with `Fin n` variables (modulo some typeclass constraints).

## Building the project

We recommend fetching Mathlib build cached files before building `CompPoly`.

```
$ lake exec cache get
$ lake build
```