# ArkLib Sumcheck Bridge

ArkLib's interaction-native Sumcheck formalization needs a small reusable
CompPoly API surface around `CMvPolynomial` substitution, finite-domain
summation, and univariate conversion. The initial ArkLib branch carries local
bridge proofs so the protocol can be reviewed end to end; this CompPoly PR is
the upstream home for the pieces that should not remain protocol-local.

## Candidate API

The ArkLib downstream use case needs the following reusable facts:

- `fromCMvPolynomial_bind₁`: computable substitution through `bind₁` agrees with
  Mathlib-side `MvPolynomial.eval₂`.
- Partial evaluation of the first variable preserves per-variable degree bounds.
- Partial evaluation of the last variable preserves degree bounds for variables
  that remain.
- Summing out the last variable over a finite domain preserves the degree bound
  of variable `0`.
- Iterated summation of all variables except the first preserves the degree bound
  needed to construct a bounded univariate round polynomial.
- A bundled constant-polynomial ring homomorphism for `CPolynomial.C`, so
  downstream code does not need to repackage it.

## Intended Downstream Shape

Once this API is available in CompPoly, ArkLib's
`ProofSystem/Sumcheck/Interaction/CompPoly.lean` should shrink to protocol
definitions and thin invocations of upstream lemmas. The Sumcheck interaction PR
should then depend on this CompPoly branch or on the merged CompPoly commit.

This page is a draft landing note for the dependency PR. The code should live in
the existing representation/bridge modules where possible, rather than in an
ArkLib-specific namespace.
