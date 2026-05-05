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
lake exe CompPolyBench
```

## CI Mapping

- [`../../.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)
  runs a clean build, warm rebuild, and `lake test`, then posts a build-timing
  report. It also builds and runs `CompPolyBench`, then uploads benchmark reports
  as CI artifacts.
- [`../../.github/workflows/linting.yml`](../../.github/workflows/linting.yml) runs
  the style linter on changed `.lean` files in PRs and push builds.
- [`../../.github/workflows/check_imports.yml`](../../.github/workflows/check_imports.yml)
  checks that `CompPoly.lean` matches the tracked source tree.
- [`../../.github/workflows/docs-integrity.yml`](../../.github/workflows/docs-integrity.yml)
  checks the `CLAUDE.md` symlink and local markdown links.

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
