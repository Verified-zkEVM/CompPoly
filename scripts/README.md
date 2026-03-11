# Scripts

This directory contains the main helper scripts for local validation and CI support.

## Recommended Entry Points

- `./scripts/update-lib.sh` - regenerate `CompPoly.lean` from tracked source files.
- `./scripts/check-imports.sh` - verify that `CompPoly.lean` is up to date.
- `./scripts/lint-style.sh` - run the Lean style linter and repo-wide Lean-file
  checks.
- `python3 ./scripts/check-docs-integrity.py` - verify the `CLAUDE.md` symlink and
  local markdown links across the handbook.

## Script Inventory

### `update-lib.sh`

Regenerates [`../CompPoly.lean`](../CompPoly.lean) by scanning tracked
`CompPoly/**/*.lean` files. Run this after adding, renaming, or deleting source
files under `CompPoly/`.

### `check-imports.sh`

Runs `update-lib.sh`, compares the result with the committed `CompPoly.lean`, and
fails if the generated umbrella import file is stale.

Use this when:

- you changed the source tree layout,
- CI reports that imports are out of date,
- you want a quick check before pushing.

### `lint-style.sh`

Runs the Lean style linter across the repository and then performs a few repo-wide
checks such as executable-bit detection and filename collisions.

This is the higher-level wrapper around `lint-style.py`.

### `lint-style.py`

The underlying Python linter for Lean style issues. It checks module docstrings,
line length, forbidden imports or tactics, trailing whitespace, and the local
`native_decide` policy, while honoring entries in `style-exceptions.txt`.

Use this directly only when you want to lint a specific subset of files.

### `build_timing_report.sh`

Helper used by CI to measure and render build timings for clean builds, warm
rebuilds, and the `lake test` path. This supports
[`../.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml).

## Typical Workflows

### Added or renamed source files

```bash
./scripts/update-lib.sh
./scripts/check-imports.sh
lake build
```

### Lean-heavy cleanup

```bash
./scripts/lint-style.sh
lake build
```

### Docs-only change

```bash
python3 ./scripts/check-docs-integrity.py
```
