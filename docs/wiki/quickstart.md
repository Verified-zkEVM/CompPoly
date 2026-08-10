# Quickstart

This page is the recommended playbook for routine local validation.

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

This is stricter than a plain build. It runs the repository style linter and the
global Lean-file checks in [`../../scripts/README.md`](../../scripts/README.md).

### Docs, handbook, or link updates

```bash
python3 ./scripts/check-docs-integrity.py
```

Run this when editing `AGENTS.md`, `README.md`, `CONTRIBUTING.md`, or files under
`docs/`.

### Benchmark changes

```bash
lake build CompPolyBench
lake exe CompPolyBench --medium
```

CI runs a curated subset rather than the full suite, so a new benchmark group must
be added to `BENCH_CI_GROUPS` in
[`../../.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)
to be covered there. See [`../../bench/README.md`](../../bench/README.md).

## CI Mapping

- [`../../.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)
  runs a **warm** (incremental) `lake build` by default — reusing cached Lake
  oleans so only dirty modules rebuild — then `lake test`, and posts a
  build-timing report. It also builds and runs `CompPolyBench --medium` over the curated
  `BENCH_CI_GROUPS` selection, then uploads benchmark reports as CI artifacts.
  A full cold rebuild (`rm -rf .lake/build && lake build`) runs automatically
  when `lean-toolchain` or `lake-manifest.json` differs from the comparison base
  (PR base, previous push tip, or merge-base with `main` on manual dispatch).
  You can also force a clean via **Actions → Lean Action CI → Run workflow** with
  the `clean_build` input. Ordinary source-only PR/push runs stay warm.
- [`../../.github/workflows/linting.yml`](../../.github/workflows/linting.yml) runs
  the style linter on changed `.lean` files in PRs and push builds.
- [`../../.github/workflows/check_imports.yml`](../../.github/workflows/check_imports.yml)
  checks that `CompPoly.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks the `CLAUDE.md` symlink, local markdown links, and backticked file paths
  in the docs.

Four further workflows exist that are not part of the pass/fail gate:

- [`../../.github/workflows/summary.yml`](../../.github/workflows/summary.yml)
  posts a PR summary on open and on every new commit. It runs under
  `pull_request_target` and never builds or executes PR code — it reads the diff
  and committed source as data — which is what makes that safe for fork PRs.
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
python3 ./scripts/check-docs-integrity.py
lake test
lake build CompPolyBench
```

For more detail on the helper scripts, see
[`../../scripts/README.md`](../../scripts/README.md).
