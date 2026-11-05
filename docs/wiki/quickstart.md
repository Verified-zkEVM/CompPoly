# Quickstart

This page is the recommended playbook for routine local validation.

## Python tooling

Install [uv](https://docs.astral.sh/uv/getting-started/installation/) for
all repository Python entry points, including validation scripts and CI.
CI uses uv 0.13.6. The uv commands below select Python
3.12; uv downloads it if needed. Run them from the repository root.
These checks use only the standard library. `--no-project` runs them without
installing a Python package or creating a project environment.

## Recommended Validation

For a routine Lean change, run:

```bash
lake build
```

On a cold clone, fetch precompiled dependencies first:

```bash
lake exe cache get
lake build
```

`lake exe cache get` covers Mathlib and its dependencies, which is the expensive half.
It does not cover CompPoly's own modules, which `lake build` compiles. Downstream
projects that depend on CompPoly get its prebuilt oleans automatically. See
[`build-cache.md`](build-cache.md).

## Validation By Change Type

### Existing Lean files only

```bash
lake build
```

### Public API changes, proof refactors, or regression-test updates

```bash
lake build
lake test
```

### Native field arithmetic or startup changes

Build the dedicated native smoke target and run it with the resource limits documented in
[`../../tests/README.md`](../../tests/README.md#native-startup-and-field-arithmetic). The checks
exercise linked module initialization and actual BF64/Ext3 arithmetic. `lake test` alone does not
exercise that startup path.

### Filling a `sorry`, or work that must stay axiom-clean

```bash
lake build && lake test
lake exe axiomsweep --check
lake exe kernelreplay
```

`axiomsweep` is kernel-level axiom/`sorry` accounting for every reportable
declaration owned by a `CompPoly.*` or `CompPolyTests.*` module, diffed against the
committed baseline `scripts/axiom_baseline.json`. It sweeps the library and the tests as
their umbrella modules import them (`bench/` is outside it). It has the blind spots of any
environment walk (structure-field defaults and `example`s never enter the
environment). CI's blocking `lake build --wfail` over the library and the tests covers
those, because every `sorry` there is a "declaration uses `sorry`" warning. The module
docstring in `scripts/AxiomSweep.lean` describes the blind spots.
It fails only on *new* `sorryAx` or non-standard-axiom taint, so pre-existing gaps
stay allowed. After you intentionally add or close a `sorry`, refresh and commit the
baseline:

```bash
lake exe axiomsweep --update-baseline
```

CI runs the same check as an enforcing gate (see `lean_action_ci.yml`). On a pull request
the `trusted-gates` job also runs the *base revision's* sweep against the *base revision's*
baseline, so a PR cannot approve its own new taint by editing the baseline or the sweep.
That job uses the base revision's checkout, scripts and Mathlib cache, and from the PR only
its compiled `.olean` files, whose layout it checks. It runs the PR's own kernel replay
last, after every verdict. Two cases need a sign-off: an approving review of the PR's
current head commit by a user listed in the base revision's `.github/CODEOWNERS` who did not
author the PR or any of its commits. A later push needs a new review.

- The PR changes `lean-toolchain` or `lake-manifest.json`. Installing the PR's toolchain
  and packages runs code they choose, so this sign-off is checked first, before any of it
  runs; only then does the job switch to the PR's lock files.
- The base sweep finds new `sorry` or axiom taint. Any other sweep failure fails outright:
  native-compiler trust, which is never baselineable, and a sweep that did not run.

`kernelreplay` re-checks every declaration of the library and the tests in Lean's kernel.
The sweep trusts that the build sent each declaration to the kernel. A declaration added
under `set_option debug.skipKernelTC true`, or by meta code calling
`addDeclWithoutChecking`, looks axiom-clean to it and fails here. The replay also checks
that each module's exported constants match the ones it checks, and it checks every copy
of a name that several modules store. It replays the modules in chunks of 16, one chunk
per child process. `--jobs N` runs N at once, each needing up to about 5 GB.

These checks do not cover everything:

- On `pull_request`, GitHub reads the trusted job's definition from the PR's own copy of
  the workflow. The job is only as trustworthy as the rule that a change to
  `.github/workflows/` needs a code owner's review, so branch protection must require it.
  A `workflow_run` workflow, defined by the default branch, would remove this dependency.
- The job checks the oleans the PR's build produced. Nothing ties them to the PR's source,
  so a build that runs malicious code could upload oleans that differ from what its
  source compiles to. A crafted olean could also attack the loader itself.
- Until the base revision's sweep stops running initializers (this change does that), a
  PR's `initialize` blocks still run inside the base sweep.

### Added, renamed, or deleted files under `CompPoly/`

```bash
./scripts/update-lib.sh
./scripts/check-imports.sh
lake build
```

`CompPoly.lean` is generated from tracked `CompPoly/**/*.lean` files. If it changes,
commit the regenerated file with the source changes.

### Lean style cleanup or new Lean-heavy code

```bash
./scripts/lint-style.sh
```

`./scripts/lint-style.sh` is stricter than a plain build. It runs the repository style
linter and the global Lean-file checks in [`../../scripts/README.md`](../../scripts/README.md).

### Docs, handbook, or link updates

```bash
uv run --no-project --python 3.12 python scripts/check-docs-integrity.py
```

Run this when editing `AGENTS.md`, `README.md`, `CONTRIBUTING.md`, or files under
`docs/`.

### Prose in docs, docstrings, comments, commits, or PR text

```bash
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
```

The writing checker reports possible defects against the
[writing standard](writing.md) in the prose that the branch changes. It is advisory.
[`write-technical-prose.md`](write-technical-prose.md) describes its other modes and
how to read its findings. If you change the checker or the vocabulary, run its tests:

```bash
uv run --no-project --python 3.12 python scripts/test-check-writing.py
```

### Benchmark changes

```bash
lake build CompPolyBench
lake exe CompPolyBench --medium
```

CI gates on benchmark *correctness*, not timings:

```bash
lake exe CompPolyBench --medium --validate-only
```

Both CI tracks run a curated subset rather than the full suite, so a new
benchmark group must be added to `bench/ci-groups.txt` to be covered. Timings
come from the on-demand Benchmarks workflow. See
[`../../bench/README.md`](../../bench/README.md) and
[`benchmarking.md`](benchmarking.md).

## CI Mapping

- [`../../.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)
  runs a **warm** (incremental) `lake build` by default. The warm build reuses cached
  Lake oleans, so only dirty modules rebuild. The workflow then runs `lake test`, a
  linked native field smoke test under the documented resource bounds, and these
  enforcing gates: the axiom sweep (under this revision's policy and, on a PR, the base
  revision's), the kernel replay, and a `--wfail` build of the library and the tests.
  It posts a build-timing report, which compares with a baseline run only when the CPU
  model, CPU count and cache state match. On a PR it also reports the declarations whose
  statement or value changed against the base commit (`scripts/statement_diff.py` over
  `axiomsweep --statements` exports). It also builds
  `CompPolyBench` and runs it in `--validate-only` mode over the curated group set in
  `bench/ci-groups.txt`. That run checks that the implementations of each group agree,
  without timing ordinary workloads. Harness checks can still record samples. The
  workflow uploads the digests as an artifact.
  A full cold rebuild (`rm -rf .lake/build && lake build`) runs automatically
  when `lean-toolchain` or `lake-manifest.json` differs from the comparison base
  (PR base, previous push tip, or merge-base with `main` on manual dispatch).
  You can also force a clean via **Actions → Lean Action CI → Run workflow** with
  the `clean_build` input. Ordinary source-only PR/push runs stay warm.
  Two Actions caches feed the warm path: `.lake/packages` keyed on
  `lean-toolchain` plus `lake-manifest.json`, and `.lake/build` keyed additionally
  per commit. A dependency-cache miss is not expensive, because `lean-action` runs
  `lake exe cache get` for us, so Mathlib's oleans are downloaded rather than
  compiled.
- [`../../.github/workflows/linting.yml`](../../.github/workflows/linting.yml) runs
  the style linter on changed `.lean` files in PRs and push builds.
- [`../../.github/workflows/check_imports.yml`](../../.github/workflows/check_imports.yml)
  checks that `CompPoly.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks the `CLAUDE.md` symlink, local markdown links, and backticked file paths
  in the docs.
- [`../../.github/workflows/writing.yml`](../../.github/workflows/writing.yml) runs
  the tests of the writing checker as a gate. Its other job runs the checker on the
  changed prose and on the PR description. That job reports findings as warnings
  and returns success for those findings. Operational errors fail the job.

Five further workflows exist that are not part of the pass/fail gate:

- [`../../.github/workflows/benchmarks.yml`](../../.github/workflows/benchmarks.yml)
  produces benchmark **timings** **on demand only**. Three events start it:
  **Actions → Benchmarks → Run workflow**, a `/bench` comment from a repo member,
  and a PR that touches `bench/**`. Timings stay out of the gate because
  `ubuntu-latest` is a shared 2-vCPU VM, and its wall-clock time is not a useful gate.
  `lean_action_ci.yml` gates benchmark *correctness* instead. The workflow restores
  the build caches but never saves them.
- [`../../.github/workflows/summary.yml`](../../.github/workflows/summary.yml)
  posts a PR summary on open and on every new commit. It runs under
  `pull_request_target` and never builds or executes PR code. It reads the diff
  and the committed source as data, so it is safe for fork PRs.
- [`../../.github/workflows/review.yml`](../../.github/workflows/review.yml) runs a
  PR review **on demand only**, triggered by a `/review` comment from a repo
  member. It is deliberately not run on PR open, because the review path builds and
  elaborates the PR's Lean code with secrets in scope.
- [`../../.github/workflows/update_lean_project.yml`](../../.github/workflows/update_lean_project.yml)
  bumps the Lean toolchain and dependencies nightly, and can be dispatched manually.
- [`../../.github/workflows/lean_release_tag.yml`](../../.github/workflows/lean_release_tag.yml)
  adds a release tag when `lean-toolchain` changes on `main`.

## Lower-Level Commands

Use the direct scripts when debugging a specific failure:

```bash
./scripts/update-lib.sh
./scripts/check-imports.sh
./scripts/lint-style.sh
uv run --no-project --python 3.12 python scripts/check-docs-integrity.py
lake test
lake build CompPolyBench
lake exe axiomsweep --check
lake exe kernelreplay
```

For more detail on the helper scripts, see
[`../../scripts/README.md`](../../scripts/README.md).
