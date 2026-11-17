# CompPoly AI Agent Guide

Lean 4 library for formally verified computable polynomial operations over rings and
finite fields. Start with [`README.md`](README.md) for the public project overview.

`AGENTS.md` is the canonical root guide for AI agents and agent-oriented tooling.
Human contributors should usually start with [`README.md`](README.md),
[`CONTRIBUTING.md`](CONTRIBUTING.md), and [`docs/wiki/README.md`](docs/wiki/README.md).
`CLAUDE.md` is a symlink to this file.

## Fast Start

1. Run `lake build` for routine validation.
2. Run `lake test` when changing proofs, public APIs, or regression tests.
3. If you add, rename, or delete files under `CompPoly/`, run
   `./scripts/update-lib.sh` and then `./scripts/check-imports.sh`.
4. Use `./scripts/lint-style.sh` when touching Lean style-sensitive files.
5. If you touch repo docs or links, run `uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py`.
6. When you fill or add a `sorry` (or change anything that must stay axiom-clean),
   run `lake exe axiomsweep --check`. If the change is intentional, refresh
   `scripts/axiom_baseline.json` with `lake exe axiomsweep --update-baseline`
   and commit the diff. Native-compiler trust is never baselineable.
7. When you make a fast implementation faster, follow the loop in
   [`docs/wiki/autoresearch.md`](docs/wiki/autoresearch.md). Edit, test, measure,
   and prove, in that order. Run the implementation's tests and `--validate-only` first.
   `./scripts/bench-ab.sh run <group>` is the measurement. Prove the refinement
   theorem only after a `faster` verdict without `SUSPECT`. A `sorry` on that theorem
   stays inside an iteration and never goes into a commit.
8. When you add a field carrier or a polynomial representation, add its codec in the
   same PR. A fixed-width scalar needs `CanonicalNat` and `ByteCodec`.
   A fixed-length composite needs `ByteCodec`. A variable-length type needs `DelimitedCodec`.
   Also add the round-trip and injectivity theorems through the class interfaces. For a fast carrier, add the agreement lemma with its specification
   field. See
   "New Types Owe a Codec" in [`CONTRIBUTING.md`](CONTRIBUTING.md) and
   [`docs/wiki/serialization.md`](docs/wiki/serialization.md).
9. Before you draft or revise prose, follow
   [`docs/wiki/write-technical-prose.md`](docs/wiki/write-technical-prose.md).

## Where To Work

- `CompPoly/Univariate/` - canonical univariate representation, quotient model,
  interpolation, and Mathlib bridges. It also contains the NTT transforms, batch
  evaluation, root finding (`Univariate/Roots/`), and Reed-Solomon encoding and Gao
  decoding (`Univariate/ReedSolomon/`).
- `CompPoly/Multivariate/` - sparse computable multivariate polynomials,
  operations, renaming, restriction, and `MvPolynomial` equivalences.
- `CompPoly/Multilinear/` - coefficient and Boolean-hypercube evaluation forms for
  multilinear polynomials.
- `CompPoly/Bivariate/` - specialized bivariate layer built from nested
  univariate polynomials, including the Guruswami-Sudan list decoder
  (`Bivariate/GuruswamiSudan/`).
- `CompPoly/LinearAlgebra/` - executable dense matrices and polynomial matrices
  with shifted row reduction. The decoders use these engines.
- `CompPoly/Fields/` - concrete field instances plus the computable
  field-extension framework (`Fields/Extension/`, `F[X]/f` for an arbitrary monic
  `f`, with binomials `X^d - W` as the ergonomic special case) and binary-field,
  GHASH, and additive-NTT infrastructure.
- `CompPoly/Data/` - reusable supporting lemmas and helper definitions.
- `CompPoly/ToMathlib/` - local bridge lemmas and Mathlib-facing support code.
- `tests/` - regression coverage under the `CompPolyTests` namespace.
- `scripts/` - repo utilities for import maintenance, linting, and CI support.

## Guardrails

- `./scripts/update-lib.sh` generates `CompPoly.lean`. Do not hand-edit it.
- Edit source, not derived output under `.lake/`.
- If a PR changes commands, repo structure, generated outputs, or recurring repo
  guidance, update the matching page in [`docs/wiki/`](docs/wiki/README.md) in the
  same PR.
- Promote stable repo-specific guidance into [`docs/wiki/`](docs/wiki/README.md)
  instead of leaving it only in transient notes.
- Use the [writing standard](docs/wiki/writing.md) for documentation,
  comments, docstrings, commit messages, PR and issue text, and review comments. Use
  [`write-technical-prose.md`](docs/wiki/write-technical-prose.md) for the workflow.
  The writing rules are advice. Leave clear, correct text alone, even when a checker suggests an
  edit. CONTRIBUTING owns the contribution requirements. Keep trust and soundness statements exact.

## Deeper Docs

- [`docs/wiki/README.md`](docs/wiki/README.md) - wiki hub and maintenance contract.
- [`docs/wiki/quickstart.md`](docs/wiki/quickstart.md) - validation commands and CI
  mapping.
- [`docs/wiki/repo-map.md`](docs/wiki/repo-map.md) - subtree map and task routing.
- [`docs/wiki/generated-files.md`](docs/wiki/generated-files.md) - source-of-truth
  rules for generated or derived outputs.
- [`docs/wiki/benchmarking.md`](docs/wiki/benchmarking.md) - how the benchmark suite
  measures, how to read its output, and how to add a group.
- [`docs/wiki/benchmark-best-times.md`](docs/wiki/benchmark-best-times.md) - the
  current best time of every benchmarked component, and the log of optimization
  passes that produced them.
- [`docs/wiki/autoresearch.md`](docs/wiki/autoresearch.md) - the optimization loop
  over the fast implementations: test, measure, and prove. It also covers verdicts,
  proofs that survive the next change, and targets.
- [`docs/wiki/build-cache.md`](docs/wiki/build-cache.md) - Mathlib's olean cache and
  CompPoly's prebuilt release archive.
- [`docs/wiki/module-system.md`](docs/wiki/module-system.md) - module headers,
  `public`/`meta` imports, module privacy, and migration fix patterns.
- [`docs/wiki/representations-and-bridges.md`](docs/wiki/representations-and-bridges.md)
  - main polynomial representations and Mathlib bridge layers.
- [`docs/wiki/typeclass-minimization.md`](docs/wiki/typeclass-minimization.md) -
  minimal typeclass assumptions and no-blanket-scope guidance.
- [`docs/wiki/binary-fields-and-ntt.md`](docs/wiki/binary-fields-and-ntt.md) -
  binary-field stack, GHASH, and additive NTT.
- [`docs/wiki/coding-theory.md`](docs/wiki/coding-theory.md) - Reed-Solomon
  encoding, unique and list decoding, root finding, and the matrix layer.
- [`docs/wiki/field-extensions.md`](docs/wiki/field-extensions.md) - computable
  field extensions for an arbitrary monic modulus, and their two irreducibility
  paths. Binomials use Rabin's test collapsed to base-field exponentiations. Other
  moduli use kernel-checked Rabin certificates.
- [`docs/wiki/serialization.md`](docs/wiki/serialization.md) - byte encodings of
  field elements and polynomials, the `CanonicalNat`/`ByteCodec` classes, and the
  ArkLib protocol classes they feed.
- [`docs/wiki/writing.md`](docs/wiki/writing.md) - the writing standard for all
  prose, with its [vocabulary](docs/wiki/writing-vocabulary.md) and
  [workflow](docs/wiki/write-technical-prose.md).

## Canonical Project Docs

- [`README.md`](README.md) - project overview and main exported surfaces.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) - contribution process, naming, style,
  docstrings, and citations.
- [`ROADMAP.md`](ROADMAP.md) - planned directions and current phase priorities.
- [`tests/README.md`](tests/README.md) - test layout and test commands.
- [`scripts/README.md`](scripts/README.md) - script inventory and operator notes.

## Trusted Code Base (TCB) Policy

**`native_decide` is forbidden.** The project must not depend on `Lean.ofReduceBool`.
All proofs must be kernel-safe, verifiable by Lean's type-checker alone without
trusting the compiler.

- Use `decide` for decidable propositions.
- For expensive kernel computations such as BitVec arithmetic, use `Nat`-based
  structural recursion instead of `Finset.fold` over `BitVec`. See the `clMulNat`
  pattern in `CompPoly/Fields/Binary/BF128Ghash/Prelude.lean`.
- If `decide` is too slow, restructure the proposition, for example by batching
  checks into a single conjunction, rather than reaching for `native_decide`.
- Keep concrete certificate proofs free of rewrite transports. A criterion that
  depends on a field size takes it as a numeral `q` with `hcard : Fintype.card F = q`,
  and it substitutes `q` internally. A concrete caller then states its conditions at
  the numeral, and an abstract caller passes `rfl`. State a new criterion that way.
  Do not add a variant that takes only `Fintype.card F`. Such a variant invites a
  caller-side `rw [hcard]`, which leaves a transport around a certificate whose type
  carries a huge exponent. A from-empty kernel replay can then unfold `npowRec` step
  by step. See [`docs/wiki/field-extensions.md`](docs/wiki/field-extensions.md).

## Performance Guidelines

### Typeclass instances

- **Never** put `@[simp]` on `instance` declarations. Instances are found by
  typeclass synthesis, not `simp`. Marking them `@[simp]` registers equation lemmas
  that cause `simp` to unfold typeclass internals and balloon unification work.
- Prefer explicit instance constructions such as `Field.isDomain` over
  `inferInstance` when the synthesis path is long or ambiguous.
- State the minimal typeclass assumptions for each new `def`, `instance`,
  `lemma`, and `theorem`. Avoid blanket section-level `variable [...]`
  declarations unless every declaration in scope needs them. See
  [`docs/wiki/typeclass-minimization.md`](docs/wiki/typeclass-minimization.md).

### Tactics

- Prefer `simp only [...]` to bare `simp`, because bare `simp` uses the full simp set.
- Avoid `grind` when a simpler tactic suffices, such as `omega`, `ring`,
  `simp only`, or `exact`. `grind` generates large proof terms via
  saturation-based reasoning.
- Use `decide` sparingly on large types, because the kernel must evaluate each `decide`.
- Some theorems must stay true while an implementation changes, such as the
  refinement theorem of a fast implementation. State the facts of such a theorem as
  named lemmas marked `@[simp]` or `@[grind =]`. Close the theorem over that set
  (`simp only [...]` or `grind`), not with a hand-written `rw` chain. The next
  change to the implementation then updates lemmas, not proof steps. See
  [`docs/wiki/autoresearch.md`](docs/wiki/autoresearch.md).

### Certificate / computational proofs

- Some proofs reduce large arithmetic in the kernel, for example modular squaring
  certificates over finite fields. For these proofs, define kernel-efficient checkers
  with structural recursion over `Nat` primitives such as `Nat.testBit`, `Nat.xor`,
  and `Nat.shiftLeft`.
- Prove equivalence to the mathematically clean definition once, then use the fast
  checker in all certificate lemmas.
- Specialize operations where possible. For example, if a polynomial has few
  nonzero coefficients, hardcode the multiplication instead of iterating over all
  bits.

### Imports

- Avoid umbrella imports like `import Mathlib.Tactic`. Import only the specific
  modules you need, for example `Mathlib.Tactic.Ring` and
  `Mathlib.Tactic.Omega`.
