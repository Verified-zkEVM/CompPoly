# Binary Fields And NTT

The `CompPoly/Fields/` subtree mixes a broad concrete-field catalog with a more
specialized characteristic-2 stack used for GHASH and additive-NTT work.

## Top-Level Layout

```text
CompPoly/Fields/
  Basic.lean
  BabyBear.lean, Goldilocks.lean, BN254.lean, ...
  Binary/
    Common.lean
    BF128Ghash/
      Prelude.lean
      Basic.lean
      Impl.lean
      XPowTwoPowGcdCertificate.lean
      XPowTwoPowModCertificate.lean
    Tower/
      Abstract/*
      Concrete/*
      Support/*
      Basic.lean
      Equiv.lean
      Impl.lean
      Prelude.lean
      TensorAlgebra.lean
    AdditiveNTT/
      AdditiveNTT.lean
      Domain.lean
      NovelPolynomialBasis.lean
      Intermediate.lean
      Algorithm.lean
      Impl.lean
      Correctness.lean
```

Use [`../../CompPoly/Fields/README.md`](../../CompPoly/Fields/README.md) as the
directory-level overview for the broader field catalog.

## Common Binary Infrastructure

[`../../CompPoly/Fields/Binary/Common.lean`](../../CompPoly/Fields/Binary/Common.lean)
is the shared base for characteristic-2 support, BitVec-facing helpers, and lemmas
used by both GHASH and tower/NTT developments.

If the work item is shared binary-field algebra rather than one specific protocol or
algorithm, start there.

## GHASH Surface

The GHASH model lives under `Binary/BF128Ghash/`.

- [`../../CompPoly/Fields/Binary/BF128Ghash/Prelude.lean`](../../CompPoly/Fields/Binary/BF128Ghash/Prelude.lean)
  defines the GHASH polynomial and the low-level verification helpers used by the
  later certificate files.
- [`../../CompPoly/Fields/Binary/BF128Ghash/Basic.lean`](../../CompPoly/Fields/Binary/BF128Ghash/Basic.lean)
  packages the field surface.
- [`../../CompPoly/Fields/Binary/BF128Ghash/Impl.lean`](../../CompPoly/Fields/Binary/BF128Ghash/Impl.lean)
  contains implementation-facing lemmas and constructions.
- The `XPowTwoPow*Certificate.lean` files encode concrete certificate proofs.

Use this area when the task is specifically about `GF(2^128)`, GHASH, or the
certificate-based proof strategy for binary-field arithmetic.

## Binary Tower Surface

The tower development splits into abstract theory, concrete constructions, and
support lemmas:

- `Tower/Abstract/*` - abstract tower definitions and algebra.
- `Tower/Concrete/*` - concrete basis, core definitions, and field instances.
- `Tower/Support/*` - supporting lemmas about defining polynomials, linear
  independence, and finite-index helpers.
- `Tower/Equiv.lean`, `Tower/Impl.lean`, and `Tower/TensorAlgebra.lean` connect the
  layers and expose useful transport lemmas.

Use the tower subtree when the task is about characteristic-2 extensions more
generally, not just GHASH.

## Additive NTT Surface

The additive-NTT stack is split by role rather than by one monolithic file:

- [`../../CompPoly/Fields/Binary/AdditiveNTT/Domain.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Domain.lean)
  defines the evaluation domains.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/NovelPolynomialBasis.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/NovelPolynomialBasis.lean)
  develops the basis used by the algorithm.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Intermediate.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Intermediate.lean)
  holds the intermediate polynomial layer.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Algorithm.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Algorithm.lean)
  defines evaluation points, twiddle factors, stage updates, and the algorithm data
  flow.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Impl.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Impl.lean)
  packages the implementation-facing surface.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Correctness.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Correctness.lean)
  proves the implementation correct.

When changing additive NTT, expect to read several of these files together.
Algorithm changes often cascade into `Intermediate`, `Impl`, and `Correctness`.

## Where To Start By Task

- Shared BitVec or characteristic-2 helper lemma: `Binary/Common.lean`
- GHASH field model or certificate proof: `Binary/BF128Ghash/`
- General tower-field structure or extension lemmas: `Binary/Tower/`
- Additive-NTT basis, domain, or correctness proof: `Binary/AdditiveNTT/`

## Reading Order Suggestions

- For GHASH: `Prelude` -> `Basic` -> `Impl` -> certificate files
- For tower fields: `Prelude` / `Basic` -> `Abstract` or `Concrete` branch ->
  `Equiv` / `Impl`
- For additive NTT: `Domain` -> `NovelPolynomialBasis` -> `Intermediate` ->
  `Algorithm` -> `Impl` -> `Correctness`
