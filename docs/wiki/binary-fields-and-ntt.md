# Binary Fields And NTT

The `CompPoly/Fields/` subtree mixes a broad concrete-field catalog with a more
specialized characteristic-2 stack used for GHASH and additive-NTT work.

## Top-Level Layout

This page owns `CompPoly/Fields/Binary/` only:

```text
CompPoly/Fields/Binary/
  Common.lean
  Common/
    Arithmetic.lean
  BF128Ghash/
    Arithmetic.lean
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

[`Common.Arithmetic`](../../CompPoly/Fields/Binary/Common/Arithmetic.lean) provides width-generic
zero extension, carry-less multiplication, and the 128-bit multiplication and squaring helpers.
It imports neither polynomial quotients nor finite-field certificates.

[`Common`](../../CompPoly/Fields/Binary/Common.lean) reexports that arithmetic and adds the
polynomial interpretation, characteristic-two algebra, and correspondence proofs.

## AES byte presentation

`AesField` is the nominal `Ext` presentation over `ZMod 2` with modulus
`X^8 + X^4 + X^3 + X + 1`. Import
[`Aes.Arithmetic`](../../CompPoly/Fields/Binary/Aes/Arithmetic.lean) for executable arithmetic,
`ofBitVec`, `toBitVec`, and their inverse laws. Bit `i` is the coefficient of `X^i`.
Import [`Aes.Basic`](../../CompPoly/Fields/Binary/Aes/Basic.lean) for the certified `Field`,
characteristic two, cardinality 256, and quotient equivalence. The raw arithmetic module does
not import those proofs or the generated certificate.

A field numeral `(2 : AesField)` is zero; `AesField.ofBitVec (2#8)` is the polynomial generator.
This differs from the level-three binary tower despite their equal cardinalities. There are no
implicit conversions between those presentations or from raw bytes. An embedding into another
field requires a separately specified generator image and a proof that it satisfies the modulus.

[`Aes.Ghash`](../../CompPoly/Fields/Binary/Aes/Ghash.lean) supplies the executable ring
homomorphism `AesField.toGhash`. It sends the AES generator to GHASH polynomial-basis word
`0x0dcb364640a222fe6b8330483c2e9849`, and proves the root identity, generator image and
injectivity. Its actual function evaluates the eight coefficients; the quotient universal
property proves the homomorphism laws without introducing a new scalar-action instance.
Ordinary `map_add`, `map_mul`, `map_inv₀` and `map_pow` lemmas apply. The pinned implementations
selecting this root are referenced in the module docstring. This field embedding does not
establish a protocol's weight-basis or soundness conditions.

The degree-eight irreducibility proof uses the general Rabin criterion, checking Frobenius
remainders at exponents 256 and 16. Regenerate its certificate with the command recorded in
[`Aes.Certificate`](../../CompPoly/Fields/Binary/Aes/Certificate.lean).

## GHASH Surface

The GHASH model lives under `Binary/BF128Ghash/`.

- [`Arithmetic`](../../CompPoly/Fields/Binary/BF128Ghash/Arithmetic.lean) provides the nominal
  carrier, word maps, XOR addition, folded multiplication, and named inversion without
  polynomial quotients or irreducibility certificates.
- [`../../CompPoly/Fields/Binary/BF128Ghash/Prelude.lean`](../../CompPoly/Fields/Binary/BF128Ghash/Prelude.lean)
  defines the GHASH polynomial and the low-level verification helpers used by the
  later certificate files.
- [`../../CompPoly/Fields/Binary/BF128Ghash/Basic.lean`](../../CompPoly/Fields/Binary/BF128Ghash/Basic.lean)
  packages the field surface.
- [`../../CompPoly/Fields/Binary/BF128Ghash/Impl.lean`](../../CompPoly/Fields/Binary/BF128Ghash/Impl.lean)
  reexports the arithmetic, proves its quotient correspondence, and assembles the canonical
  ring and field instances.
- The `XPowTwoPow*Certificate.lean` files encode concrete certificate proofs.

Use this area when the task is specifically about `GF(2^128)`, GHASH, or the
certificate-based proof strategy for binary-field arithmetic.

`BF128Ghash.ConcreteBF128Ghash` is a nominal carrier. Use `BF128Ghash.ofBitVec` to construct
elements and `.toBitVec` to recover polynomial-basis coordinates: bit `i` denotes the coefficient
of `X^i`. These maps form `BF128Ghash.equivBitVec`; there is no implicit conversion to raw words
or the 128-bit binary tower. A field numeral such as `(2 : ConcreteBF128Ghash)` is zero, whereas
`ofBitVec (2#128)` denotes `X`. This coordinate interface does not specify a byte or wire format.

`square`, `powTwoPow`, and `invItohTsujii` take nominal elements. The deprecated names `pow_2k`
and `inv_itoh_tsujii` retain those same nominal signatures; callers with raw words must convert
explicitly. The former `ConcreteBF128Ghash_eq_BitVec` type equality is replaced by the coordinate
equivalence. Raw carry-less multiplication and reduction retain their word interfaces.

The generic `Field` dictionary uses the same executable multiplication and Itoh–Tsujii inverse
as the named operations. Natural and integer powers use binary exponentiation. Division and
rational scalar actions use total field inversion, so an even rational denominator maps to
zero in characteristic two. The legacy `instHDivConcreteBF128Ghash` and
`instDivisionRingConcreteBF128Ghash` names remain deprecated abbreviations; they no longer
register competing instances.

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
  These modules use shared support lemmas without importing the abstract tower construction.
  `Tower/Equiv.lean` imports both constructions to relate them; use that bridge or
  `Tower/Impl.lean` when both presentations are needed.
  [Concrete/Coordinates.lean](../../CompPoly/Fields/Binary/Tower/Concrete/Coordinates.lean)
  supplies `ConcreteBinaryTower.Coordinates.succCoordinates`: an
  executable linear equivalence from level `k + 1` to two level-`k` coefficients, ordered
  constant term first and generator term second. It uses the existing tower embedding
  for the scalar action. Pass it to `AlgebraTower.natCoordinatesOfLE` or
  `AlgebraTower.natCoordinatesConstOfLE` for coordinates between arbitrary ordered levels.
  [Concrete/CoordinateArithmetic.lean](../../CompPoly/Fields/Binary/Tower/Concrete/CoordinateArithmetic.lean)
  supplies the quadratic product, conjugate, norm, and total inverse formulas for these
  successor coordinates, including zero, without importing the abstract tower bridge.
  [Concrete/RelativeCoordinates.lean](../../CompPoly/Fields/Binary/Tower/Concrete/RelativeCoordinates.lean)
  specializes these maps as `coordinates` and `pack`, with round-trip and scalar-action laws.
  Its readback theorems identify each coefficient with the corresponding raw bit block,
  including natural-word and individual-bit readback. These coordinates use the tower field's
  own embedding and retain low-first block order.
  [Concrete/BasisCoordinates.lean](../../CompPoly/Fields/Binary/Tower/Concrete/BasisCoordinates.lean)
  identifies these executable coordinates with the representation of `multilinearBasis`
  at the same numeric indices. Its packing formula reconstructs a word as the sum of
  embedded coefficients times those basis vectors.
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
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Executable.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Executable.lean)
  defines the generic function-backed and array-backed algorithms without importing a tower
  construction.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Impl.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Impl.lean)
  re-exports those algorithms with concrete tower bases, instances, and the existing example.
- [`../../CompPoly/Fields/Binary/AdditiveNTT/Correctness.lean`](../../CompPoly/Fields/Binary/AdditiveNTT/Correctness.lean)
  proves the generic implementations correct without requiring a concrete tower. The umbrella
  `AdditiveNTT.lean` retains the combined generic and concrete surface for existing consumers.

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
  `Algorithm` -> `Executable` -> `Correctness`; add `Impl` for concrete tower instances
