# Contributing to CompPoly

Contribute a definition, a proof, a fast implementation, a test, or a documentation change.
The [roadmap](ROADMAP.md) describes the planned directions of the library. The
[open issues](https://github.com/Verified-zkEVM/CompPoly/issues) include bugs, requested
features, and formalization tasks. Issues labeled `good first issue` or `help wanted` are suitable
starting points.

Start with [`README.md`](README.md), the [wiki](docs/wiki/README.md), and the `README.md` file of
the subtree that you change. [`AGENTS.md`](AGENTS.md) gives the entry points and guardrails for AI
agents. If you do not know where to begin, open an issue or a discussion that describes your
interest.

## Before You Start

### Check for Overlap

Before you start a formalization or an optimization, search the open pull requests and issues for
the same target:

```bash
gh pr list -R Verified-zkEVM/CompPoly --state open --search "<topic>"
gh issue list -R Verified-zkEVM/CompPoly --state open --search "<topic>"
```

If an open PR covers the same declarations, ask its author whether the work is active. Do not
duplicate active work. If you open a PR for the same target, link the earlier PR and explain how
your work relates to it.

If earlier work appears abandoned, you may ask a maintainer whether to proceed. A maintainer may
waive the overlap restriction for that contribution.

### Large Contributions

For a large contribution, such as a new polynomial representation or a new field family, we
strongly encourage a [blueprint](https://github.com/PatrickMassot/leanblueprint) before you write the Lean
code. A blueprint describes these items:

- The contents of the formalization.
- The key definitions, theorems, and assumptions of the proposed Lean formalization.
- A dependency graph from the intermediate results to the final result.
- References to the relevant literature.
- Possible difficulties and design choices.

Open an issue or a discussion that proposes the contribution and its blueprint. Discuss the blueprint
before you start a large implementation. A blueprint makes the structure of the work
visible early, so that reviewers can comment before you invest in proofs.

### Set Up

For Python check prerequisites and commands, see
[Python tooling](docs/wiki/quickstart.md#python-tooling).

On a new clone, download the Mathlib build cache, and then build the library:

```bash
lake exe cache get
lake build
```

The cache covers Mathlib and its dependencies. `lake build` compiles the CompPoly modules.
The [build-cache page](docs/wiki/build-cache.md) explains both caches. The writing checker in the
[Writing](#writing) section runs with [uv](https://docs.astral.sh/uv/getting-started/installation/).
Its commands select Python 3.12 and do not install a project package.

## Validate Your Change

The [quickstart](docs/wiki/quickstart.md) is the canonical list of validation commands and their
CI mapping. Run the commands for each type of change in your PR:

| Change | Commands |
|---|---|
| Any Lean change | `lake build` |
| Public API, proof refactor, or regression test | `lake build` and `lake test` |
| Added, renamed, or deleted file under `CompPoly/` | `./scripts/update-lib.sh`, then `./scripts/check-imports.sh` and `lake build` |
| A `sorry` filled or added, or work that must stay axiom-clean | `lake build`, then `lake exe axiomsweep --check` |
| Lean style cleanup or a large amount of new Lean code | `./scripts/lint-style.sh` |
| Native field arithmetic or startup | The `CompPolyNativeSmoke` commands in [`tests/README.md`](tests/README.md#native-startup-and-field-arithmetic) |
| Benchmark | `lake build CompPolyBench`, then `lake exe CompPolyBench --medium --validate-only` |
| Documentation | `uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py` |

If `CompPoly.lean` changes, commit the regenerated file with the source changes. If you
intentionally add or close a `sorry`, refresh the axiom baseline with
`lake exe axiomsweep --update-baseline` and commit the diff. The axiom sweep never accepts
native-compiler trust in the baseline.

## Performance Contributions

A faster version of a fast implementation is a welcome contribution. The
[optimization loop](docs/wiki/autoresearch.md) gives the full protocol.
[`benchmarking.md`](docs/wiki/benchmarking.md) explains how the suite measures.
[`benchmark-best-times.md`](docs/wiki/benchmark-best-times.md) gives the time to beat for each
row.

### Rules

* **Every function stays formally verified.** Do not change the specification definition.
  Connect a faster implementation to it in one of the two accepted forms. The first form is a
  `@[csimp]` lemma with an equality theorem. The second form is a twin definition with an `_eq_`
  theorem that the call site depends on. `@[implemented_by]` substitutes code without a proof, so
  it is not accepted for this purpose. `native_decide` is forbidden everywhere, as the
  [TCB policy](AGENTS.md#trusted-code-base-tcb-policy) states. `lake exe axiomsweep --check` must
  pass.
* **One change per PR.** Give a PR one optimization with one measured effect, so that the verdict
  belongs to that change. Put two independent ideas in two PRs.
* **The digest must not move.** Benchmark inputs are seeded for each group, so the digest of a
  group is the same across builds and commits. A `mismatch` verdict means that the candidate
  computes a different result. The verdict shows a bug, not a measurement.
* **Test, then measure, then prove.** The proof is the expensive part, so do it last. Prove only a
  change that tests show correct on concrete inputs and that measurement shows faster. If the
  implementation has no tests of its own under `tests/`, add them first. Make sure that the
  original, formally verified function passes them before you change anything. These tests are
  then the test step of every iteration.
* **Add a test for each bug that the proof finds.** If the proof finds a bug that the tests did not
  catch, add a test for that bug. While you explore, the refinement theorem can contain a `sorry`,
  so that the tests and the timings use the new code. A PR never contains that `sorry`. Use
  `lake exe axiomsweep --check` to confirm that none remains.
* **`lake test` is part of the gate, as well as `lake build`.** An implementation is not faster if
  its tests take hours to elaborate. In this repository, inlining attributes on loop-shaped bodies
  caused that problem.
* **Write the proof so that the next optimization does not break it.** State the coefficient and
  unfolding facts of the implementation as named lemmas marked `@[simp]` or `@[grind =]`. Close
  the refinement theorem with `simp only [...]` over these lemmas or with `grind`, not with a
  hand-written `rw` chain. The next change to the implementation then changes lemmas, not proof
  steps. See [Proving so the proof survives the next iteration](docs/wiki/autoresearch.md#proving-so-the-proof-survives-the-next-iteration).
* **Quote ratios, not nanoseconds.** Numbers from your machine are not comparable with the tables in
  `benchmark-best-times.md`, which come from one reference machine. Report the A/B verdict and the
  candidate-over-baseline ratio for each row. The tables and pass log use measurements from that
  reference machine. Do not edit them in your PR.
* **Keep the harness out of it.** Do not change `bench/` and a fast implementation in the same PR.
  Both sides of the comparison would change, so a reviewer cannot judge the result. If you need a new
  benchmark group, add it first in its own PR. Follow
  [Adding a benchmark](docs/wiki/benchmarking.md#adding-a-benchmark).

### Running the benchmarks

```bash
lake build CompPolyBenchLib CompPolyBench           # `lake build` alone does not build bench/
lake exe CompPolyBench --list                        # every group key
lake exe CompPolyBench --medium --validate-only --groups <key>   # correctness only, no timings
lake exe CompPolyBench --medium --groups <key>       # timed; output under bench/out/
```

CI, the A/B loop, and the best-times tables use the `--medium` preset. The results, a Markdown
report, and a manifest go to `bench/out/`, which git ignores. Read the `Spread` column before the
number. A row with `n=1` has no dispersion, so do not read a ratio from it.

### Running the loop

```bash
./scripts/bench-ab.sh freeze                 # build the baseline binary from the current tree
# edit the fast implementation (a `sorry` on its refinement theorem is fine here)
lake build && lake test                      # test: the implementation's tests and the digest gate
./scripts/bench-ab.sh run <key>[,<key>...]   # measure: both binaries turn about, then --compare
# on `faster` without SUSPECT: prove the refinement theorem, then
lake build && lake test && lake exe axiomsweep --check
```

Freeze the baseline from `main` before you edit. The `run` command builds the candidate once and
runs the two binaries alternately. It adds the harness groups to measure machine drift, and it
prints the comparison. A copy of the comparison goes to `bench/out/ab/<run>/compare-*.md`.

A row is `faster` only when two conditions are true. The ratio of medians must clear the threshold,
which is 5% by default. Every candidate invocation must also beat every baseline invocation.

If the harness drift is outside ±10%, repeat the run instead of reading it. Otherwise, keep the
change on a `faster` verdict without `SUSPECT`, and revert it on any other verdict. Use a quiet
machine. Do not rebuild or edit `bench/` while a run is in progress.

### What the PR must contain

* The title `perf(<scope>): <subject>`.
* The change in one paragraph: what was slow, the reason, and what the new code does.
* The proof: the `@[csimp]` or `_eq_` theorem that connects the new code to the specification.
  Name it in the description. Close it over the lemma set of the implementation, not with a
  rewrite chain.
* The tests: the concrete-input tests for the implementation. Add them in this PR if the
  implementation had none.
* The A/B evidence: the `compare-*.md` table or its relevant rows, with the preset, the rounds, and
  the drift line. If you keep a `same` or `slower` verdict for a different reason, such as a
  compile-time fix or a correctness repair, give that reason.
* A statement that `lake build`, `lake test`, `--validate-only` on the affected groups, and
  `lake exe axiomsweep --check` pass.

## New Types Owe a Codec

A new field carrier or polynomial representation becomes a protocol type as soon as ArkLib can
name it. Add its serialization in the same PR. [`serialization.md`](docs/wiki/serialization.md)
gives the formats and the invariants that they keep. Its "Adding an instance" section is the
procedure. The PR must contain these items:

* The codec. A fixed-width scalar, such as a prime-field carrier or a binary field, gets
  `CanonicalNat` and `ByteCodec := ByteCodec.ofCanonicalNat _`. A fixed-length composite, such as
  an extension or a dense coefficient vector, gets `ByteCodec` by concatenation, usually through
  `ByteCodec.instVector`. A variable-length type gets `DelimitedCodec`. Build it from the list,
  pair, and vector codecs, with `Valid` stating what fits the `u64` framing.
* The theorems through the class interfaces, not only through the raw functions. These theorems
  are `deserialize (serialize x) = some x`, injectivity, and, for a scalar, the round trip of the
  total decoder (`CanonicalNat.deserialize_serialize`). The derived instances give the first two
  when you prove the one law of the codec.
* For a fast carrier of an existing field, the agreement lemma with the specification field,
  `toBytes (ofField x) = toBytes x`. Add a test that the stored word is not the emitted value. The
  agreement lemma is the correctness statement of the instance. It keeps the bytes independent of
  the carrier.
* A `Bytes.lean` test module that mirrors the source module. It contains a known byte vector, a
  round trip through `serialize` and `deserialize`, and one rejected input.
* A `Repr` instance if the type has none. It is not part of the byte format, but a type that can be
  written out should also be printable.

Do not add `ToJson`, `FromJson`, or a different ad hoc encoding. If a consumer needs JSON, it will
be hex strings of these same bytes.

## Pull Request Guidelines

### Title Format

Use this format:

```text
<type>(<optional-scope>): <subject>
```

**Types:**

* `feat`: A feature or formalized result
* `fix`: A defect correction
* `doc`: Documentation
* `docs`: Documentation, as an alternative to `doc`
* `style`: Formatting
* `refactor`: A change to the organization or interfaces
* `test`: Tests
* `chore`: Maintenance
* `perf`: A performance improvement
* `ci`: CI workflows and checks

**Subject:**

* Name the change with an imperative phrase, such as "add the coset NTT", or with a noun phrase
  for the result, such as "the additive NTT over a coset". Do not use "changed" or "changes".
* Start with a lowercase letter. Keep the capitalization of a name or identifier, such as `NTT`.
* Do not end the subject with a period.
* Use the scope when it helps identify the affected component, such as `fields` or `bench`.

For a breaking change, put `!` before the colon, as in
`refactor(univariate)!: rename the evaluation API`. The PR summary workflow adds a warning to its
summary when a title does not follow this format.

### Description

Keep the description proportional to the change. Give the reader the information needed to assess
the contribution:

* The problem, the change, and its purpose.
* How the change differs from the previous behavior.
* The headline declarations, with their hypotheses when a reader needs them to judge the claim.
* The `sorry` admissions that the PR adds or closes, and any change to
  `scripts/axiom_baseline.json`.
* The validation commands that you ran and their results. Identify checks that you did not run.
* Renamed or removed declarations and the affected callers.
* Related issues, such as `Closes #123`, and overlapping PRs.

Keep the claims in the title and the description consistent with the code and the evidence.
A successful build does not show that a statement is correct or that a fast implementation is
faster. If the PR changes commands, repository structure, generated outputs, or recurring
contributor guidance, update the matching page in [`docs/wiki/`](docs/wiki/README.md) in the same
PR.

### Size and Stacking

Give each PR one topic. Separate mechanical changes from mathematical changes when each can be
reviewed and validated independently.

Use a stack of PRs when a contribution needs several dependent PRs. Each PR must build against its
stated base. Name that base in the description. The import check in `check_imports.yml` runs only
on PRs that target `main`, so run `./scripts/check-imports.sh` yourself for a PR in a stack.

CompPoly permits squash and rebase merges. It does not permit merge commits.

### Writing

The [writing guide](docs/wiki/writing.md) offers advice for documentation, docstrings, comments,
commit messages, PR and issue text, and review comments. Use it to improve clarity and precision.
Leave clear, correct text alone, even if it does not follow a rule or the checker reports it.
The contribution requirements in this document retain their stated force.

Use the [writing workflow](docs/wiki/write-technical-prose.md) when you draft or revise that text.
Keep claims, hypotheses, uncertainty, trust statements, and requirement strength unchanged during
a style edit. The [vocabulary](docs/wiki/writing-vocabulary.md) records technical meanings. It does
not prohibit other meanings when their context is clear.

The writing checker gives optional wording suggestions. It does not establish clarity, accuracy
or STE conformance. You can run it on changed prose or a draft PR description:

```bash
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
uv run --no-project --python 3.12 python scripts/check-writing.py --stdin description < description.md
```

The `Writing` workflow runs the same check on each PR and reports its findings as warnings. These
warnings do not fail the build. Read findings in context. Correct claim and source errors, and
use style suggestions when they improve clarity.

## Style and Naming Guidelines

Follow the [Lean community's contribution
guidelines](https://github.com/leanprover-community/leanprover-community.github.io/tree/lean4/templates/contribute).
The [linting script](scripts/lint-style.sh) enforces some of them.

### Naming Conventions

* **Files**: `UpperCamelCase.lean` (for example, `BinarySearch.lean`).
* **Types and Structures**: `UpperCamelCase` (for example, `MonoidHom`, `Visualizer`).
* **Functions and Terms**: `lowerCamelCase` (for example, `binarySearch`, `isPrime`).
* **Theorems and Proofs**: `snake_case` (for example, `add_comm`, `list_reverse_id`).
* **Acronyms**: Treat an acronym as a word (for example, `HtmlParser`, not `HTMLParser`).
* **Prop-valued Classes**: Use `UpperCamelCase`. If the class is an adjective, use the `Is` prefix
  (for example, `IsCompact`, `IsPrime`). If it is a noun, use no prefix (for example, `Group`,
  `TopologicalSpace`).
* **Spelling**: Use American English for declaration names (for example, `analyze`, not
  `analyse`, and `color`, not `colour`).
* **Dot Notation**: Use namespaces to group related definitions (for example, `List.map`).
  Namespaces enable dot notation (for example, `l.map f`) when the type is known. Use manual dot
  notation for logical connectives and equality (for example, `And.intro`, `Eq.refl`, `Iff.mp`).
  *Preferred but not enforced. The merged code uses both `h.symm` and `Eq.symm h`. Flag a use only
  when it is ambiguous.*
* **Axiomatic Names**: Use the standard names for properties: `refl`, `symm`, `trans`, `comm`,
  `assoc`, `inj` (injective), and `congr`.
* **Identifiers**:
    * Use namespaces for logical properties (for example, `And.comm`, `Or.intro`).
    * Use descriptive names for arithmetic and algebraic properties (for example, `mul_comm`,
      `add_assoc`).

### Theorem Naming Logic

* **Hypotheses**: Use `_of_` to separate hypotheses, in the order in which they occur. For example,
  `lt_of_succ_le` means "less than *follows from* successor less equal".
* **Variants**: Use `left` or `right` to describe which argument changes or is relevant (for
  example, `add_le_add_left`).
* **Structural Lemmas**:
    * `ext`: For extensionality (`∀ x, f x = g x → f = g`).
    * `iff`: For bidirectional implications.
    * `inj` / `injective`: For injectivity results.
    * `mono` / `antitone`: For monotonicity.
* **Induction and Recursion**:
    * `induction_on` / `recOn`: Use when the value comes before the constructions (the motive
      eliminates to `Prop` or `Type`).
    * `induction` / `rec`: Use when the constructions come before the value.
* **Predicates**: Usually use prefixes (for example, `isClosed_Icc`, not `Icc_isClosed`).
  Property suffixes such as `_inj`, `_mono`, `_injective`, and `_surjective` are exceptions.

### Module Layout

* **Theorem-only helper modules**: Prefer the name `Lemmas` for a new theorem-only leaf module.
* **Proof placement**: Keep transport and equivalence lemmas near the bridge layer, such as
  `ToPoly` or `MvPolyEquiv`. Keep the first user-facing correctness theorem next to the definition
  that it justifies. For example, the bridge lemmas in `CompPoly/Univariate/ToPoly/Core.lean` and
  `CompPoly/Multivariate/MvPolyEquiv/Eval.lean` stay with the bridge. A theorem such as
  `eval_interpolatePow_at_node` stays with `interpolatePow` in `CompPoly/Univariate/Lagrange.lean`.

### Variable Conventions

We follow the Mathlib style, adapted for algebraic code. The conventions below agree with the use
across the repository (`Univariate/`, `Multivariate/`, `Multilinear/`, `Bivariate/`, `Fields/`).
If you are not sure, read the adjacent files.

* `u`, `v`, `w`, ...           : Universes
* `α`, `β`, `γ`, ...            : Generic types (in non-algebraic contexts)
* `R`, `M`, `G`, `F`, ...       : Algebraic carrier types (rings, modules, groups, fields). Prefer
  these names to `α` and `β` in algebraic declarations such as `variable {R : Type*} [Semiring R]`
* `a`, `b`, `c`, ...            : Propositions
* `x`, `y`, `z`, ...            : Elements of a generic type
* `h`, `h₁`, ...                : Assumptions and hypotheses
* `p`, `q`                     : Polynomials or predicates. The type and the context tell them
  apart. In this repository, `p` and `q` are usually `CPolynomial`, `CMvPolynomial`, or
  `CMlPolynomial` values
* `m`, `n`, `k`, ...            : Natural numbers
* `i`, `j`, `k`, ...            : Indices into vectors, lists, or `Fin n`. They can be `ℕ`-valued
  or `ℤ`-valued. The convention describes the indexing role, not the underlying type
* `s`, `t`, ...                : Sets or lists

### Symbol Naming Dictionary

When we translate theorem statements into names, we use these standard mappings for symbols:

**Logic**
| Symbol | Name | Symbol | Name | Symbol | Name |
|---|---|---|---|---|---|
| `∨` | `or` | `∧` | `and` | `¬` | `not` |
| `→` | `of` / `imp` | `↔` | `iff` | `∃` | `exists` |
| `∀` | `all` / `forall` | `=` | `eq` | `≠` | `ne` |

**Sets and Lattices**
| Symbol | Name | Symbol | Name | Symbol | Name |
|---|---|---|---|---|---|
| `∈` | `mem` | `∉` | `notMem` | `⊆` | `subset` |
| `∩` | `inter` | `∪` | `union` | `\` | `sdiff` |
| `≤` | `le` | `<` | `lt` | `⊥` | `bot` |
| `⊤` | `top` | `⊔` | `sup` | `⊓` | `inf` |

**Algebra**
| Symbol | Name | Symbol | Name | Symbol | Name |
|---|---|---|---|---|---|
| `+` | `add` | `*` | `mul` | `^` | `pow` |
| `-` | `neg` / `sub` | `⁻¹`| `inv` | `/` | `div` |
| `∑` | `sum` | `∏` | `prod` | `•` | `smul` |

As in Mathlib, use `≤` (`le`) and `<` (`lt`) in theorem statements. Use `≥` (`ge`) or `>` (`gt`)
only when the argument order makes them necessary.

### Syntax and Formatting

* **Line Length**: Keep `.lean` source lines under 100 characters. The rule does not apply to
  Markdown, CI, or workflow files, because the enforced linter `scripts/lint-style.py` processes
  only `.lean` files.
* **Indentation**: Use 2 spaces for indentation.
* **Headers**: Start each file with the copyright, license, and authors block. Do not add a
  separate AI-attribution line. List only the credited authors on the `Authors:` line. Then follow
  the module-system shape that [`module-system.md`](docs/wiki/module-system.md) describes:
  ```lean
  /-
  Copyright (c) 2026 CompPoly Contributors. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Author Name
  -/
  module

  public import CompPoly.Data.Array.Lemmas

  /-!
  # Module docstring
  -/

  public section
  ```
* **Imports**: Group the imports at the top of the file.
* **Operators**: Put spaces on both sides of `:`, `:=`, and infix operators. Put an operator before
  a line break, not at the start of the next line.
* **Hypotheses**: Prefer hypotheses to the left of the colon (for example, `(h : P) : Q`), not in
  arrows (`: P → Q`), when the proof introduces them.
* **Functions**: Prefer `fun x ↦ ...` to `λ x, ...`.
* **Instances**: Use the `where` syntax to define instances and structures. *Preferred but not
  enforced. The merged code uses both `instance ... := ⟨...⟩` and `instance ... where`.*
* **Binders**: Put a space after a binder (for example, `∀ x,`, not `∀x,`).
* **Tactic Mode**: Put `by` at the end of the line before the tactic block. Indent the tactic
  block.
* **Calculations**: Align the relations in a `calc` block.
* **Empty Lines**: Do not put empty lines *inside* definitions or proofs.
* **Delimiters**: Avoid parentheses where possible. Use `<|` (pipe left) and `|>` (pipe right) to
  reduce nesting. Do not use `;` to separate tactics, except in short, single-line tactic
  sequences. *The `<|` and `|>` preference is preferred but not enforced. The merged code uses both
  styles. The `;` guidance still applies.*
* **Error Messages**: In a custom error or trace message, put interpolated data in backticks
  (inline) or on a new indented line.

### Normal Forms

We aim for consistent representations of equivalent statements:

* **Standard Forms**: Use established normal forms (for example, `s.Nonempty` instead of
  `s ≠ ∅`). They enable dot notation and keep statements consistent.
* **Inequalities with Bottom and Top**:
    * In **assumptions**, use `x ≠ ⊥`, which is easier to check.
    * In **conclusions**, use `⊥ < x`, which gives a stronger result.
    * Use the same forms for top: `x ≠ ⊤` in assumptions and `x < ⊤` in conclusions.

### Tactic Mode and Performance

* **Squeezing Simp**: Do not "squeeze" a terminal `simp` call into `simp only [...]` unless
  performance or stability makes it necessary. An unsqueezed `simp` is often easier to read, and
  small library changes break it less often.
* **Comments**: Use `--` for inline comments and `/- ... -/` for block comments.

### Transparency and API Design

* **Definitions (`def`)**: By default, `def` creates a `semireducible` definition. Tactics such as
  `rw` and `simp` usually do not unfold it without an explicit instruction. Prefer `def` for most
  definitions, because it keeps terms manageable.
* **Abbreviations (`abbrev`)**: `abbrev` creates a `reducible` definition that is always unfolded.
  Use it for type synonyms or light aliases whose underlying term should stay visible.
* **Irreducible**: Use `irreducible` (or a `structure` wrapper) to seal an API boundary when the
  internal implementation details should not leak.

### Deprecation Policy

* **Renaming**: When you rename a declaration, fix the breakage that the rename causes. If you
  cannot fix it, for example in downstream code, keep the old name as a deprecated alias:
  ```lean
  @[deprecated (since := "YYYY-MM-DD")] alias oldName := newName
  ```
* **Removal**: When you remove a declaration, give a message that explains the transition:
  ```lean
  @[deprecated "Use `better_theorem` instead" (since := "YYYY-MM-DD")]
  theorem old_theorem ...
  ```

### Documentation Standards

Every definition and major theorem should have a docstring. Write docstrings and comments to the
[writing standard](docs/wiki/writing.md).

* **Module Docstrings**: Each file should start with a `/-! ... -/` block that contains a title, a
  summary, the notation, and the references.
* **Sectioning Comments**: Use `/-! ### Title -/` to divide a large file into sections. These
  comments appear in the generated documentation.
* **Declaration Docstrings**: Put a `/-- ... -/` docstring above each definition. State the
  meaning of the object or the claim of the theorem, with the relevant hypotheses.
* **Trust Statements**: In a certificate or checker docstring, name the checker, the checked
  data, and the components that stay trusted. Rule C9 of the writing standard gives the details.
* **Syntax**:
    * Use backticks for Lean names: `` `List.map` ``.
    * Use LaTeX for mathematics: `$ f(x) = y $` (inline) or `$$ \sum_{i=0}^n i $$` (display).
* **Tactic Documentation**: Give each tactic a complete, self-contained description.

### Citation Standards

When you cite a paper in a Lean docstring, follow these conventions:

* **Use citation keys in text**: Cite a paper with a key such as `[ACFY24]`, not with its full title
  or URL.

* **Include a References section**: Each file that cites papers should have a `## References` section in
  its module docstring:
  ```lean
  ## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
  ```
  Use the format `* [Author Last Name, First Initial, *Title*][citation_key]`.

* **Add BibTeX entries**: Give each academic paper an entry in
  [`blueprint/src/references.bib`](blueprint/src/references.bib). When you add a paper, add the
  BibTeX entry, use the citation key in your Lean file, and list the paper in the References
  section. The file is a standalone bibliography, and the repository has no rendered leanblueprint
  project. Its header gives the `grep` command that lists cited keys without an entry.

* **Non-academic references**: An implementation reference, such as a GitHub repository or a
  specification, can give its URL directly. It usually does not need a BibTeX entry.

## Code of Conduct

CompPoly follows the principles of the
[Mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

Project participation includes contributions, issues, and discussions. Participants agree to the
code of conduct. Treat other contributors with respect. You can report unacceptable behavior to the
project maintainers.

## Licensing

Like many other Lean projects, CompPoly is licensed under the terms of the Apache License 2.0. The
full license text is in the [LICENSE](LICENSE) file.

By contributing to CompPoly, you agree that your contributions will be licensed under this same
license. Ensure you are comfortable with these terms before submitting contributions.
