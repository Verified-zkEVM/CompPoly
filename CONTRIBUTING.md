## Contributing to CompPoly

We enthusiastically welcome contributions to CompPoly!

Whether you are fixing bugs, improving documentation, or adding new formalizations, your input is valuable. We particularly encourage contributions that address:

* **Repository handbook:** Contributors should usually start with [`README.md`](README.md), [`docs/wiki/README.md`](docs/wiki/README.md), and the module-level `README.md` files. [`AGENTS.md`](AGENTS.md) is the AI-agent entrypoint and is mainly for agent-oriented tooling and workflow guardrails.
* **Active formalizations:** Please see the list of active formalization efforts and their blueprints.
* **Open Issues:** Please see the list of open issues for bugs, requested features, and specific formalization tasks. Issues tagged as `good first issue` or `help wanted` are great places to start.
* **Roadmap Goals:** We maintain a [ROADMAP](ROADMAP.md) outlining the planned direction and major goals for the library.
* **Documentation:** Please check [`README.md`](README.md), [`docs/wiki/README.md`](docs/wiki/README.md), and the module-level `README.md` files for current usage and structure notes, and feel free to propose improvements.

If you are interested in contributing but unsure where to begin, please get in touch.

### Large Contributions

For substantial contributions, such as a new proof system, we strongly encourage the development of a [blueprint](https://github.com/PatrickMassot/leanblueprint) first.

* **What is a Blueprint?** A blueprint is a document that outlines:
    * The contents of the formalization.
    * The proposed formalization strategy in Lean (key definitions, theorems, assumptions).
    * A dependency graph relating all intermediate results to the final desired result.
    * References to relevant literature.
    * Potential challenges and design choices.
* **Why a Blueprint?** This helps align the contribution with the project's structure and goals *before* significant coding and proving effort is invested. It facilitates discussion and feedback from maintainers and the community. It also makes it easier to manage large efforts in a distributed way.
* **Process:** Please open a new discussion or issue to propose your planned contribution and discuss the blueprint before starting implementation.

## Performance Contributions

Making a fast implementation faster is a welcome contribution, and it has its
own rules, because the thing being changed is code that a proof is about. The
full protocol is [`docs/wiki/autoresearch.md`](docs/wiki/autoresearch.md); how the
suite measures is [`docs/wiki/benchmarking.md`](docs/wiki/benchmarking.md); the
time to beat for every row is
[`docs/wiki/benchmark-best-times.md`](docs/wiki/benchmark-best-times.md).

### Rules

* **Every function stays formally verified.** The specification definition does
  not change. A faster implementation is swapped in by `@[csimp]` with an
  equality theorem, or as a twin definition with an `_eq_` theorem that the call
  site depends on. Those are the two accepted shapes. `@[implemented_by]`
  substitutes code without a proof and is not accepted for this purpose, and
  `native_decide` is forbidden everywhere (see the TCB policy in
  [`AGENTS.md`](AGENTS.md)). `lake exe axiomsweep --check` must pass.
* **One change per PR.** A PR is one optimisation with one measured effect, so
  the verdict is attributable. Two independent ideas are two PRs.
* **The digest must not move.** Benchmark inputs are seeded per group, so a
  group's digest is the same across builds and commits. A `mismatch` verdict
  means the candidate computes something else; it is a bug, not a measurement.
* **Test, then measure, then prove.** The proof is the expensive part, so
  spend it last, on a change already shown correct on concrete inputs and
  faster in measurement. If the kernel you are optimising has no tests of its
  own under `tests/`, add them first. While exploring, the refinement theorem
  may carry a `sorry` so the new code is what gets tested and timed; a PR never
  contains one, and `lake exe axiomsweep --check` is how you confirm that.
* **`lake test` is part of the gate, not just `lake build`.** A kernel whose
  tests take hours to elaborate is not faster: inlining attributes on
  loop-shaped bodies have done exactly that here.
* **Write the proof so the next optimisation does not break it.** State the
  kernel's coefficient and unfolding facts as named lemmas marked `@[simp]` or
  `@[grind =]`, and close the refinement theorem with `simp only [...]` over
  them or with `grind`, rather than a hand-written `rw` chain. The next change
  to the kernel then updates lemmas, not proof steps. See "Proving so the proof
  survives the next iteration" in `docs/wiki/autoresearch.md`.
* **Quote ratios, not nanoseconds.** Numbers from your machine are not
  comparable with the tables in `benchmark-best-times.md`, which are taken on
  one reference machine. Report the A/B verdict and the candidate-over-baseline
  ratio per row. A maintainer re-measures on the reference machine after merge
  and updates the tables and the pass log; do not edit them in your PR.
* **Keep the harness out of it.** A PR that changes `bench/` and a fast
  implementation at once cannot be judged, since both sides of the comparison
  moved. If a new benchmark group is needed, add it first in its own PR,
  following "Adding a benchmark" in `docs/wiki/benchmarking.md`.

### Running the benchmarks

```bash
lake build CompPolyBenchLib CompPolyBench           # `lake build` alone does not build bench/
lake exe CompPolyBench --list                        # every group key
lake exe CompPolyBench --medium --validate-only --groups <key>   # correctness only, no timings
lake exe CompPolyBench --medium --groups <key>       # timed; output under bench/out/
```

`--medium` is the preset CI, the A/B loop and the best-times tables use.
Results, a Markdown report and a manifest land in `bench/out/`, which is
ignored by git. Read the `Spread` column before the number: an `n=1` row
carries no dispersion and no ratio should be read off it.

### Running the loop

```bash
./scripts/bench-ab.sh freeze                 # build the baseline binary from the current tree
# edit the fast implementation (a `sorry` on its refinement theorem is fine here)
lake build && lake test                      # test: the kernel's tests and the digest gate
./scripts/bench-ab.sh run <key>[,<key>...]   # measure: both binaries turn about, then --compare
# on `faster` without SUSPECT: prove the refinement theorem, then
lake build && lake test && lake exe axiomsweep --check
```

Freeze from `main` before editing. `run` builds the candidate once, runs the
two binaries alternately, appends the harness groups so machine drift is
measured alongside, and prints the comparison; a copy lands in
`bench/out/ab/<run>/compare-*.md`. A row is `faster` only when the ratio of
medians clears the threshold (5% by default) and every candidate invocation
beat every baseline invocation. Keep on `faster` without `SUSPECT` and with
harness drift inside ±10%; revert otherwise, and repeat rather than read a run
whose drift is outside that band. Use a quiet machine, and do not rebuild or
edit `bench/` while a run is in flight.

### What the PR must contain

* Title `perf(<scope>): <subject>`.
* The change in one paragraph: what was slow, why, what the new code does.
* The proof: the `@[csimp]` or `_eq_` theorem that ties the new code to the
  specification, named in the description, and closed over the kernel's lemma
  set rather than by a rewrite chain.
* The tests: the concrete-input tests for the kernel, added in this PR if the
  kernel had none.
* The A/B evidence: the `compare-*.md` table or its relevant rows, with the
  preset, rounds, and the drift line. A `same` or `slower` verdict that is kept
  for another reason (a compile-time fix, a correctness repair) says so.
* Confirmation that `lake build`, `lake test`, `--validate-only` on the affected
  groups and `lake exe axiomsweep --check` pass.

## Pull Request Guidelines

We follow the specific convention for pull request titles and descriptions used by the Lean community.

### Title Format
The title should follow the format:
```
<type>(<optional-scope>): <subject>
```

**Types:**
* `feat`: New feature
* `fix`: Bug fix
* `doc`: Documentation changes
* `style`: Formatting, missing semicolons, etc.
* `refactor`: Code refactoring
* `test`: Adding missing tests
* `chore`: Maintenance
* `perf`: Performance improvements
* `ci`: CI workflow changes

**Subject:**
* Use imperative, present tense ("change" not "changed" or "changes").
* Do not capitalize the first letter.
* No dot (.) at the end.

### Description
The description should include:
* Motivation for the change.
* Contrast with previous behavior.
* References to issues (e.g., `Closes #123`).
* If the PR changes commands, repo structure, generated outputs, or recurring contributor guidance, update the matching page in [`docs/wiki/`](docs/wiki/README.md) in the same PR.

## Style and Naming Guidelines
We aim to adhere to the [Lean community's contribution guidelines](https://github.com/leanprover-community/leanprover-community.github.io/tree/lean4/templates/contribute).
Our [linting script](scripts/lint-style.sh) helps enforce some aspects of these guidelines.

### Naming Conventions

* **Files**: `UpperCamelCase.lean` (e.g., `BinarySearch.lean`).
* **Types and Structures**: `UpperCamelCase` (e.g., `MonoidHom`, `Visualizer`).
* **Functions and Terms**: `lowerCamelCase` (e.g., `binarySearch`, `isPrime`).
* **Theorems and Proofs**: `snake_case` (e.g., `add_comm`, `list_reverse_id`).
* **Acronyms**: Treat as words (e.g., `HtmlParser` not `HTMLParser`).
* **Prop-valued Classes**: Use `UpperCamelCase`. If the class is an adjective, use the `Is` prefix (e.g., `IsCompact`, `IsPrime`). If it is a noun, no prefix is needed (e.g., `Group`, `TopologicalSpace`).
* **Spelling**: Use American English for declaration names (e.g., `analyze` not `analyse`, `color` not `colour`).
* **Dot Notation**: Use namespaces to group related definitions (e.g., `List.map`). This enables dot notation (e.g., `l.map f`) when the type is known. Use manual dot notation for logical connectives and equality (e.g., `And.intro`, `Eq.refl`, `Iff.mp`). *Preferred but not enforced — the merged codebase uses both `h.symm` and `Eq.symm h` forms freely; flag only when truly ambiguous.*
* **Axiomatic Names**: Use standard names for properties: `refl`, `symm`, `trans`, `comm`, `assoc`, `inj` (injective), `congr`.
* **Identifiers**: 
    * Use namespaces for logical properties (e.g., `And.comm`, `Or.intro`).
    * Use descriptive names for arithmetic/algebraic properties (e.g., `mul_comm`, `add_assoc`).

### Theorem Naming Logic

* **Hypotheses**: Use `_of_` to separate hypotheses, listed in the order they appear (e.g., `lt_of_succ_le` means "less than *follows from* successor less equal").
* **Variants**: Use `left` or `right` to describe which argument changes or is relevant (e.g., `add_le_add_left`).
* **Structural Lemmas**:
    * `ext`: For extensionality (`∀ x, f x = g x → f = g`).
    * `iff`: For bidirectional implications.
    * `inj` / `injective`: For injectivity results.
    * `mono` / `antitone`: For monotonicity.
* **Induction/Recursion**:
    * `induction_on` / `recOn`: Use when the value comes before the constructions (motive eliminates to Prop / Type).
    * `induction` / `rec`: Use when the constructions come before the value.
* **Predicates**: Generally use prefixes (e.g., `isClosed_Icc` not `Icc_isClosed`). Exceptions include property suffixes like `_inj`, `_mono`, `_injective`, `_surjective`.

### Module Layout

* **Theorem-only helper modules**: Prefer `Lemmas` for new theorem-only leaf modules.
* **Proof placement**: Keep transport and equivalence lemmas near the bridge layer (`ToPoly`, `MvPolyEquiv`, etc.), but keep the first user-facing correctness theorem next to the definition it justifies. For example, bridge lemmas like those in `CompPoly/Univariate/ToPoly/Core.lean` and `CompPoly/Multivariate/MvPolyEquiv/Eval.lean` stay with the bridge, while a theorem like `eval_interpolatePow_at_node` stays with `interpolatePow` in `CompPoly/Univariate/Lagrange.lean`.

### Variable Conventions

We follow Mathlib style, adapted for algebraic code. The conventions below
reflect actual usage across the repository (`Univariate/`, `Multivariate/`,
`Multilinear/`, `Bivariate/`, `Fields/`); please consult adjacent files when
in doubt.

* `u`, `v`, `w`, ...           : Universes
* `α`, `β`, `γ`, ...            : Generic types (in non-algebraic contexts)
* `R`, `M`, `G`, `F`, ...       : Algebraic carrier types (rings, modules,
  groups, fields) — preferred over `α`, `β` in algebraic declarations such
  as `variable {R : Type*} [Semiring R]`
* `a`, `b`, `c`, ...            : Propositions
* `x`, `y`, `z`, ...            : Elements of a generic type
* `h`, `h₁`, ...                : Assumptions / hypotheses
* `p`, `q`                     : Polynomials or predicates (disambiguate by
  type and surrounding context — in this repo `p`, `q` are most often
  `CPolynomial`, `CMvPolynomial`, or `CMlPolynomial` values)
* `m`, `n`, `k`, ...            : Natural numbers
* `i`, `j`, `k`, ...            : Indices into vectors, lists, or `Fin n`
  (these may be `ℕ`- or `ℤ`-valued; the convention is about the indexing
  role, not the underlying type)
* `s`, `t`, ...                : Sets or lists

### Symbol Naming Dictionary

When translating theorem statements into names, we use standard mappings for symbols:

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

> **Note**: In adherence with mathlib, we standardize on `≤` (`le`) and `<` (`lt`). Avoid `≥` (`ge`) and `>` (`gt`) in theorem statements unless necessary for argument ordering.

### Syntax and Formatting

* **Line Length**: Keep `.lean` source lines under 100 characters. (Markdown and CI / workflow files are not subject to this rule — the enforced linter at `scripts/lint-style.py` only processes `.lean` files.)
* **Indentation**: Use 2 spaces for indentation.
* **Headers**: Use standard file headers including copyright, license (Apache 2.0), and authors.
  ```lean
  /-
  Copyright (c) 2024 Author Name. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Author Name
  -/
  ```
* **Imports**: Group imports at the top of the file.
* **Operators**: Put spaces on both sides of `:`, `:=`, and infix operators. Place them before a line break rather than at the start of the next line.
* **Hypotheses**: Prefer placing hypotheses to the left of the colon (e.g., `(h : P) : Q`) rather than using arrows (`: P → Q`) when the proof introduces them.
* **Functions**: Prefer `fun x ↦ ...` over `λ x, ...`.
* **Instances**: Use the `where` syntax for defining instances and structures. *Preferred but not enforced — the merged codebase uses both `instance ... := ⟨...⟩` and `instance ... where` forms freely.*
* **Binders**: Use a space after binders (e.g., `∀ x,` not `∀x,`).
* **Tactic Mode**: Place `by` at the end of the line preceding the tactic block. Indent the tactic block.
* **Calculations**: In `calc` blocks, align relations.
* **Empty Lines**: Avoid empty lines *inside* definitions or proofs.
* **Delimiters**: Avoid parentheses where possible. Use `<|` (pipe left) and `|>` (pipe right) to reduce nesting. Avoid using `;` to separate tactics unless writing short, single-line tactic sequences. *The `<|` / `|>` preference is preferred but not enforced — the merged codebase uses both styles freely. The `;` guidance still applies.*
* **Error Messages**: In custom error or trace messages, surround interpolated data with backticks (inline) or place it on a new indented line.

### Normal Forms

We aim for consistent representations of equivalent statements:
* **Standard Forms**: Use established normal forms (e.g., `s.Nonempty` instead of `s ≠ ∅`) to enable dot notation and consistency.
* **Inequalities with Bottom/Top**:
    * In **assumptions**, use `x ≠ ⊥` (easier to check).
    * In **conclusions**, use `⊥ < x` (more powerful result).
    * Similarly for top: `x ≠ ⊤` in assumptions, `x < ⊤` in conclusions.

### Tactic Mode & Performance

* **Squeezing Simp**: Do not "squeeze" terminal `simp` calls (replacing `simp` with `simp only [...]`) unless necessary for performance or stability. Un-squeezed `simp` is often more readable and robust to minor library changes.
* **Comments**: Use `--` for inline comments and `/- ... -/` for block comments.

### Transparency and API Design

* **Definitions (`def`)**: By default, `def` creates `semireducible` definitions. These are usually not unfolded by tactics like `rw` and `simp` without explicit instruction. This is preferred for most definitions to keep terms manageable.
* **Abbreviations (`abbrev`)**: Creates `reducible` definitions that are always unfolded. Use this for type synonyms or lightweight aliases where the underlying term should be exposed.
* **Irreducible**: Use `irreducible` (or `structure` wrappers) to seal API boundaries when the internal implementation details should not leak.

### Deprecation Policy

* **Renaming**: If you rename a declaration, please ensure you fix any breakage this causes. If that is not possible, keep the old name as a deprecated alias to avoid breaking downstream code immediately.
  ```lean
  @[deprecated (since := "YYYY-MM-DD")] alias oldName := newName
  ```
* **Removal**: For removals, provide a message explaining the transition.
  ```lean
  @[deprecated "Use `better_theorem` instead" (since := "YYYY-MM-DD")]
  theorem old_theorem ...
  ```

### Documentation Standards

Every definition and major theorem should have a docstring.

* **Module Docstrings**: Each file should start with a `/-! ... -/` block containing a title, summary, notation, and references.
* **Sectioning Comments**: Use `/-! ### Title -/` to structure large files into sections. These appear in the generated documentation.
* **Declaration Docstrings**: Use `/-- ... -/` above definitions.
* **Syntax**:
    * Use backticks for Lean names: `` `List.map` ``.
    * Use LaTeX for math: `$ f(x) = y $` (inline) or `$$ \sum_{i=0}^n i $$` (display).
* **Tactic Documentation**: Complete and self-contained descriptions for tactics.

### Citation Standards

When referencing papers in Lean docstrings:

* **Use citation keys in text**: Reference papers with citation keys like `[ACFY24]` rather than full titles or URLs.

* **Include a References section**: Each file that cites papers should have a `## References` section in its docstring header:
  ```lean
  ## References
  
  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
      for Reed-Solomon Codes*][BCIKS20]
  ```
  Format: `* [Author Last Name, First Initial, *Title*][citation_key]`.

* **Add BibTeX entries**: All academic papers must have entries in [`blueprint/src/references.bib`](blueprint/src/references.bib). When adding a new paper, add the BibTeX entry, use the citation key in your Lean file, and list it in the References section. That file is currently a standalone bibliography — there is no rendered leanblueprint project yet — and its header records the `grep` that lists cited-but-missing keys.

* **Non-academic references**: Implementation references (GitHub repos, specifications) may include URLs directly and typically don't need BibTeX entries.

## Code of Conduct

To ensure a welcoming and collaborative environment, CompPoly follows the principles outlined in the [mathlib Code of Conduct](https://github.com/leanprover-community/mathlib4/blob/master/CODE_OF_CONDUCT.md).

By participating in this project (e.g., contributing code, opening issues, commenting in discussions), you agree to abide by its terms. Please treat fellow contributors with respect. Unacceptable behavior can be reported to the project maintainers.

## Licensing

Like many other Lean projects, CompPoly is licensed under the terms of the Apache License 2.0 license. The full license text can be found in the [LICENSE](LICENSE) file.

By contributing to CompPoly, you agree that your contributions will be licensed under this same license. Ensure you are comfortable with these terms before submitting contributions.
