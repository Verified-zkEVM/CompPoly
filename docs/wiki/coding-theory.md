# Coding Theory

Reed-Solomon encoding and decoding, and the two computational engines the
decoders are built on: univariate root finding and computable linear algebra.

This page owns the decoding stack. It spans four subtrees that are easy to miss
because none of them is named after coding theory:

```text
CompPoly/Univariate/ReedSolomon/    encoding, and unique decoding (Gao)
CompPoly/Bivariate/GuruswamiSudan/  list decoding
CompPoly/Univariate/Roots/          univariate root finding
CompPoly/LinearAlgebra/             dense and polynomial matrices
```

The last two are general-purpose and useful on their own; they live outside
`ReedSolomon/` and `GuruswamiSudan/` for that reason. See
[`../../CompPoly/LinearAlgebra/README.md`](../../CompPoly/LinearAlgebra/README.md)
for the matrix layer in detail.

## Two Decoding Regimes

A Reed-Solomon code of block length `n` and message length `k` has minimum
distance `n - k + 1`. That splits decoding into two regimes, and CompPoly
implements one algorithm for each.

| | Unique decoding | List decoding |
|---|---|---|
| Radius | up to `(n - k) / 2` errors | beyond it, up to the Johnson bound |
| Output | at most one message | a list of candidates |
| Algorithm here | Gao's key-equation decoder ([Gao02]) | Guruswami-Sudan ([GS99]) |
| Entry point | `ReedSolomon.Gao.decode` | `GuruswamiSudan.decode` |
| Cost | one extended-Euclid run | interpolation plus root finding |

Use Gao unless you genuinely need to decode past half the minimum distance: it
is far cheaper, it returns a decisive answer, and its refusal carries
information (see `decode_none_farness` below). Reach for Guruswami-Sudan when
the application is proximity testing or soft decoding, where a candidate list is
the point.

## Encoding

[`Univariate/ReedSolomon.lean`](../../CompPoly/Univariate/ReedSolomon.lean) fixes
the code itself: `Domain` (an array of distinct evaluation points), `messagePoly`,
and `encode`, which evaluates the message polynomial on the domain. For
`1 ≤ k < n ≤ #F` that is an `(n, k, n - k + 1)` code.

[`ReedSolomon/NTTEncode.lean`](../../CompPoly/Univariate/ReedSolomon/NTTEncode.lean)
then identifies the forward NTT with that encoder. Over the domain induced
by a radix-2 NTT domain — the node array `#[ω⁰, ω¹, …, ω^(n-1)]`, nodup because
powers of a primitive `n`-th root below `n` are pairwise distinct — the forward
transform of a message polynomial's coefficients **is** the codeword:

- `forwardImpl_eq_encode` ties `NTT.Forward.forwardImpl` (natural order,
  `O(n log n)`) to the definitional `ReedSolomon.encode`, exactly, for every
  message of length at most the domain size. No padding is needed, because
  `messagePoly` trims and so the degree bound `k ≤ D.n` suffices.
- `nttCodeword_eq_encode` is the same statement for the length-indexed packaging.

So the fast encoder needs no separate correctness argument: it is the
specification, transported.

## Unique Decoding: Gao

| Layer | File | Owns |
|---|---|---|
| Decoder | [`ReedSolomon/GaoDecoder.lean`](../../CompPoly/Univariate/ReedSolomon/GaoDecoder.lean) | `nodalPoly`, `receivedInterpolant`, `partialGcd`, `decode` |
| Correctness | [`ReedSolomon/GaoCorrectness.lean`](../../CompPoly/Univariate/ReedSolomon/GaoCorrectness.lean) | `decode_sound`, `decode_eq_some`, `decode_eq_none_iff`, `decode_none_farness` |

The algorithm interpolates the received word, then runs a partial extended
Euclid against the nodal polynomial and stops at the degree threshold; the
message falls out of the resulting Bézout relation. `decode` returns
`Option (CPolynomial F)`.

The correctness layer is stronger than plain soundness, and the extra results
are the reason to prefer this decoder:

- `decode_sound` — a returned polynomial really is within the decoding radius.
- `decode_eq_some` / `decode_unique` — completeness and uniqueness inside the
  radius.
- `decode_eq_none_iff` — an iff, so refusal is characterized, not merely allowed.
- `decode_none_farness` — refusal is a *certificate* that the received word is
  far from every codeword. A verifier can use a failed decode as positive
  evidence, which is what proximity testing needs.

Supporting uniqueness machinery (`bezout_solutions_cross_mul`, error locators,
Hamming distance) lives in the same correctness file, sectioned by role.

## List Decoding: Guruswami-Sudan

The 40-file `GuruswamiSudan/` subtree follows the interpolation-and-root-finding
decomposition of [GS99]: fit a bivariate `Q(X, Y)` vanishing to prescribed
multiplicity at every received point, then recover every `Y = f(X)` root of `Q`
with `deg f < k`. Each candidate is then checked against the received word.

**The important structural fact: the core is backend-parametric.** Interpolation
and root finding are each supplied as a context carrying both the operation and
the contract the correctness proofs consume. `Core.lean` and
`CoreCorrectness.lean` never mention a concrete algorithm, so a new backend costs
a context instance and inherits every theorem.

| Layer | File | Owns |
|---|---|---|
| Contexts | [`GuruswamiSudan/Context.lean`](../../CompPoly/Bivariate/GuruswamiSudan/Context.lean) | `GSInterpParams`, `LinearKernelContext`, `GSInterpContext`, `FieldRootContext`, `GSRootContext`, `ValidInterpolationWitness`, `DistinctXCoordinates` |
| Core | [`GuruswamiSudan/Core.lean`](../../CompPoly/Bivariate/GuruswamiSudan/Core.lean) | `gsCore`, backend-parametric |
| Core correctness | [`GuruswamiSudan/CoreCorrectness.lean`](../../CompPoly/Bivariate/GuruswamiSudan/CoreCorrectness.lean) | `gsCore_sound`, `gsCore_complete_of_interpolate`, `gsCore_complete_of_roots_all_valid_witnesses` |
| Candidate filtering | `Filter.lean`, `FilterCorrectness.lean` | `gsFilteredCore_sound`, `mem_gsFilteredCore_iff`, `gsFilteredCore_complete_of_enough_matches` |
| Concrete instances | `Implementations.lean` | named dense / Lee-O'Sullivan / Roth-Ruckenstein combinations with specialized correctness theorems |
| Executable API | `Executable.lean` | `GSReceivedWord`, `GSExecParams`, `GSParamSelector`, `decodeWithParams`, `decode` |
| Shared helpers | `Polynomial.lean`, `PolynomialCorrectness.lean`, `Util.lean` | polynomial operations used by both kernels |

### Interpolation backends

Both produce a valid witness in the sense of `ValidInterpolationWitness`; they
differ in how the constrained linear system is solved.

| Backend | Files | When to use |
|---|---|---|
| Dense | `Interpolation/Dense/{Algorithm,Correctness}.lean` | Small parameters. Builds the constraint matrix explicitly and calls the dense kernel solver. Simple, and the easiest to reason about. |
| Lee-O'Sullivan | `Interpolation/LeeOSullivan/` ([LOS06]) | Larger parameters. Works from a Gröbner-basis perspective: build a module basis, then shift-reduce it with Mulders-Storjohann. `leeOSullivanInterpolate_sound` and `leeOSullivanInterpolate_complete`, with the argument split across nine files under `Correctness/`. |

`Interpolation/Basic.lean` holds the constraints and normalized-witness helpers
shared by both, and `Interpolation/Correctness.lean` the shared results
(`interpolationWitnessIsValidBool_iff`, `lowMessageDegreeInterpolation_sound`).

### Root-finding backends

Both find the `Y`-roots of the interpolated `Q` that are polynomials of bounded
degree, and both come with soundness *and* completeness.

| Backend | Files | Character |
|---|---|---|
| Roth-Ruckenstein | `Root/RothRuckenstein/` ([RR00]) | Coefficient-by-coefficient recursion; the classical choice. `rothRuckensteinRootsYDegreeLt_sound` / `_complete`. |
| Alekhnovich | `Root/Alekhnovich/` ([Ale05]) | Divide-and-conquer over polynomial Diophantine equations; better asymptotics. `alekhnovichRootsYDegreeLt_sound`, `alekhnovichRootPrefixesWithFuel_complete`. |

Shared infrastructure: `Root/Common/` (helpers for bounded bivariate root
backends), `Root/ShiftedSubstitution/` (substituting `Y = f(X) + X^t Y`, the step
both recursions are built from), and `Root/FieldRoots/` — the univariate
field-root dependency, behind an explicit `FieldRootContext` so it can be
replaced for large concrete fields. `Root/FieldRoots/FiniteField.lean` is the
generic instance and `Root/FieldRoots/KoalaBear.lean` a concrete one.

That context is where this subtree meets `Univariate/Roots/`.

## Univariate Root Finding

[`CompPoly/Univariate/Roots/`](../../CompPoly/Univariate/Roots) is a
general-purpose root finder, used by the Guruswami-Sudan root search but not
specific to it.

| File | Owns |
|---|---|
| `Context.lean` | `FiniteFieldContext`, `LinearFactorProductSplitter`, `IsLinearFactor` and the candidate predicates |
| `Backend.lean` | `rootsInFiniteFieldWith`, `rootsInFiniteField` — the pipeline entry points |
| `Splitter.lean` | represented-linear-factor helpers and `xPowModWith` |
| `Extraction.lean` | candidate extraction, validation, and deduplication |
| `RootProduct.lean` | the product of linear factors over a root set |
| `Correctness.lean` | `monicNormalize_root_iff`, `gcdMonic_root_iff_left_right`, and the divisibility transport lemmas |
| `SmoothSubgroup/` | subgroup-refinement splitting ([MOV92]) for fields whose multiplicative group admits a smooth schedule |
| `Shoup/` | small-characteristic trace-coordinate splitting ([vzGS92]); `SmallPrimeTraceContext` + adapter to `LinearFactorProductSplitter` |
| `LasVegas/` | bounded Las Vegas Cantor–Zassenhaus (odd-char and char-2 trace branches) with explicit `ProbeFamily` randomness, deterministic fallback, and probability proofs |

The pipeline consumes a `LinearFactorProductSplitter`. Three backends supply that
interface:

| Backend | When to use |
|---|---|
| SmoothSubgroup | Multiplicative group admits a smooth cyclic refinement schedule |
| Shoup | Small base characteristic `p`, presented as `GF(p^k)`; splits via `k` trace coordinates without enumerating the field |
| LasVegas | General finite fields; odd-field CZ and/or even-trace attempts under a probe cutoff, with enumeration fallback |

Concrete coverage includes `ZMod` odd primes (Las Vegas tests) and degree-one
binary cases via `ZMod 2` and binary-tower level 0 (Shoup tests). Larger Tower
levels as char-2 Shoup contexts are the natural integration path for production
binary fields.

## Where To Start By Task

- Encoding, or tying a transform to `ReedSolomon.encode`: `ReedSolomon/NTTEncode.lean`
- Unique decoding, or using decode failure as a proximity certificate:
  `ReedSolomon/GaoCorrectness.lean`
- Changing what the GS decoder *does* without touching proofs: add a context
  instance in `GuruswamiSudan/Context.lean` and register it in `Implementations.lean`
- A new interpolation or root-finding algorithm: implement against the context
  interface; `Core`/`CoreCorrectness` should need no change
- Root finding over a new field: supply a `LinearFactorProductSplitter`, or a
  `FieldRootContext` if the caller is the GS root search
- Matrix-level work underneath any of this:
  [`../../CompPoly/LinearAlgebra/README.md`](../../CompPoly/LinearAlgebra/README.md)

## Reading Order

- Gao: `GaoDecoder` → `GaoCorrectness` (soundness → completeness → farness)
- Guruswami-Sudan: `Context` → `Core` → `CoreCorrectness` → one interpolation
  backend → one root backend → `Filter` → `Executable`
- Root finding: `Context` → `Backend` → `Extraction` → `Correctness`, then the
  splitter that fits the field (`SmoothSubgroup/`, `Shoup/`, or `LasVegas/`)

Read `Context.lean` first for GS. The contexts are the interface the rest of the
subtree is written against, and the correctness theorems are unreadable without
knowing which contracts they assume.

## Gaps

- **No Berlekamp-Welch.** Gao's decoder covers the same unique-decoding regime,
  so this is only worth adding as a cross-check, or if a downstream specification
  asks for it by name.
- **No FRI or polynomial-commitment integration.** `decode_none_farness` is the
  hook a proximity test would use, but nothing consumes it yet.
- **Binary Tower root contexts for high widths** (e.g. 32/64-bit) are not yet
  packaged as named `SmallPrimeTraceContext` instances; the Shoup tests exercise
  tower level 0 and `ZMod 2`. Wire higher levels when char-2 root search is needed
  in production paths.
- **List-size bounds are not formalized.** Soundness and completeness are proved
  relative to the supplied parameters; the Johnson-bound analysis that says how
  many candidates can survive is not.

## References

* [Gao, S., *A New Algorithm for Decoding Reed-Solomon Codes*][Gao02]
* [Guruswami, V., and Sudan, M., *Improved decoding of Reed-Solomon and
    algebraic-geometry codes*][GS99]
* [Lee, K., and O'Sullivan, M. E., *List decoding of Reed-Solomon codes from a
    Groebner basis perspective*][LOS06]
* [Roth, R. M., and Ruckenstein, G., *Efficient decoding of Reed-Solomon codes
    beyond half the minimum distance*][RR00]
* [Alekhnovich, M., *Linear Diophantine Equations Over Polynomials and Soft
    Decoding of Reed-Solomon Codes*][Ale05]
* [Menezes, A. J., van Oorschot, P. C., and Vanstone, S. A., *Subgroup
    Refinement Algorithms for Root Finding in GF(q)*][MOV92]
* [von zur Gathen, J., and Shoup, V., *Computing Frobenius maps and factoring
    polynomials*][vzGS92]
* Cantor–Zassenhaus equal-degree factorization (odd characteristic) and
  char-2 trace splitting as used in `LasVegas/`

BibTeX entries for these keys are in
[`../../blueprint/src/references.bib`](../../blueprint/src/references.bib).
