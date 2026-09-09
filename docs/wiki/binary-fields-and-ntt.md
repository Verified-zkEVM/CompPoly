# Binary Fields And NTT

The `CompPoly/Fields/` subtree mixes a broad concrete-field catalog with a more
specialized characteristic-2 stack used for GHASH and additive-NTT work.

## Top-Level Layout

This page owns `CompPoly/Fields/Binary/` only:

```text
CompPoly/Fields/Binary/
  Common.lean
  BF128Ghash/
    Prelude.lean
    Basic.lean
    Impl.lean
    XPowTwoPowGcdCertificate.lean
    XPowTwoPowModCertificate.lean
  BF64.lean
  BF64/
    BaseCertificate.lean
    Basic.lean
    Reduce.lean
    Impl.lean
    Ext3.lean
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

For everything else under `CompPoly/Fields/` — the prime-field catalog, the
Montgomery fast paths, and the extension framework — see
[`../../CompPoly/Fields/README.md`](../../CompPoly/Fields/README.md), which is the
per-module source of truth, and
[`field-extensions.md`](field-extensions.md) for the odd-characteristic extension
architecture. That catalog is deliberately not duplicated here.

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

## Polynomial-Basis GF(2^64) Surface

`Binary/BF64/` builds `GF(2^64)` as the flat quotient
`GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)`, together with its degree-three extension
`GF(2^192)`.

This is a *different presentation* from the `GF(2^64)` that appears as level 6 of
`Binary/Tower/`. The tower builds it by iterated quadratic extension, so the two use
different bases and their bit-level encodings disagree — on the same bit patterns, `2 * 3`
is `6` here and `1` in the tower's rung. Neither substitutes for the other wherever the
encoding is observable.

- [`../../CompPoly/Fields/Binary/BF64/BaseCertificate.lean`](../../CompPoly/Fields/Binary/BF64/BaseCertificate.lean)
  holds generated Rabin certificate data; regenerate it with
  [`../../scripts/gen_rabin_certificate.py`](../../scripts/gen_rabin_certificate.py)
  rather than editing it.
- [`../../CompPoly/Fields/Binary/BF64/Basic.lean`](../../CompPoly/Fields/Binary/BF64/Basic.lean)
  defines the modulus, proves it irreducible, and gives the quotient model `BF64Quot` with
  its cardinality. Degree 64 is composite, so the general `Polynomial.irreducible_of_rabin`
  is used; the collapsed prime-degree form is unsound here.
- [`../../CompPoly/Fields/Binary/BF64/Reduce.lean`](../../CompPoly/Fields/Binary/BF64/Reduce.lean)
  folds a 128-bit carry-less product back into 64 bits using the reduction constant `0x1B`.
- [`../../CompPoly/Fields/Binary/BF64/Impl.lean`](../../CompPoly/Fields/Binary/BF64/Impl.lean)
  carries the nominal field elements with `BitVec 64` coordinates, their quotient bridge, and the
  `CommRing` / `Field` instances built around an Itoh-Tsujii inverse.
- [`../../CompPoly/Fields/Binary/BF64/Ext3.lean`](../../CompPoly/Fields/Binary/BF64/Ext3.lean)
  instantiates the extension framework at `y^3 + y + 1`, whose irreducibility needs no
  certificate.

Use `BF64.ofBitVec` to construct polynomial-basis words and `BF64.toBitVec` to recover them;
the maps are inverse and introduce no implicit conversion to another field presentation.
For example, `BF64.ofBitVec (2#64)` denotes `X`, while `(2 : BF64)` is zero. Raw reference
vectors must use the coordinate constructor rather than field numeral casts.

`BF64` and `BF64.Ext3` expose proof-only `Finite` instances and the cardinality theorems
`BF64.nat_card_bf64` and `BF64.nat_card_ext3`. They provide no default enumeration dictionary.
A proof that needs `Fintype` can choose `Fintype.ofFinite` locally; `card_bf64` and `card_ext3`
then apply to that chosen enumeration. Arithmetic does not enumerate these enormous fields.
The [native startup test](../../tests/README.md#native-startup-and-field-arithmetic) checks
linked initialization and actual base/extension arithmetic under resource bounds.

The instances here are assembled field-by-field on purpose: a transport such as
`Function.Injective.commRing` takes the bridge as *data* and would make the arithmetic
noncomputable, which would also break `Ext3`. The `#guard` checks in
[`../../tests/CompPolyTests/Fields/Binary/BF64.lean`](../../tests/CompPolyTests/Fields/Binary/BF64.lean)
run the compiled arithmetic and fail the build if that ever regresses.

## Binary Tower Surface

The tower development splits into abstract theory, concrete constructions, and
support lemmas:

- `Tower/Abstract/*` - abstract tower definitions and algebra.
- `Tower/Concrete/*` - concrete basis, core definitions, and field instances.
- `Tower/Support/*` - supporting lemmas about defining polynomials, linear
  independence, and finite-index helpers.
- `Tower/Fast.lean` - packed machine-word tower arithmetic with a GF(2^8)
  lookup-table base, proven against `ConcreteBTField`; `Field` instances and ring
  isomorphisms at every level up to GF(2^128). Runtime definitions live in the
  zero-import `Tower/FastDefs.lean` for `precompileModules` consumers.
- `Tower/Equiv.lean` and `Tower/Impl.lean` connect the layers and expose useful
  transport lemmas.
- `Tower/TensorAlgebra.lean` re-exports the generic tensor basis API from
  `CompPoly/LinearAlgebra/TensorProduct/Basis.lean`. Its right scalar action is
  explicit; importing either path preserves Mathlib's default left action. See
  [`../../CompPoly/LinearAlgebra/README.md`](../../CompPoly/LinearAlgebra/README.md)
  for the local algebra, module and scalar-action selection needed for equal tensor factors.

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
- Polynomial-basis `GF(2^64)` or its cubic extension: `Binary/BF64/`
- General tower-field structure or extension lemmas: `Binary/Tower/`
- Additive-NTT basis, domain, or correctness proof: `Binary/AdditiveNTT/`

## Reading Order Suggestions

- For GHASH: `Prelude` -> `Basic` -> `Impl` -> certificate files
- For polynomial-basis `GF(2^64)`: `Basic` -> `Reduce` -> `Impl` -> `Ext3`
- For tower fields: `Prelude` / `Basic` -> `Abstract` or `Concrete` branch ->
  `Equiv` / `Impl`
- For additive NTT: `Domain` -> `NovelPolynomialBasis` -> `Intermediate` ->
  `Algorithm` -> `Impl` -> `Correctness`
