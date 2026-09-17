# Scripts

This directory contains the main helper scripts for local validation and CI support.

## Recommended Entry Points

- `./scripts/update-lib.sh` - regenerate `CompPoly.lean` from tracked source files.
- `./scripts/check-imports.sh` - verify that `CompPoly.lean` is up to date.
- `./scripts/lint-style.sh` - run the Lean style linter and repo-wide Lean-file
  checks.
- `python3 ./scripts/check-docs-integrity.py` - verify the `CLAUDE.md` symlink,
  local markdown links, and backticked source paths across the handbook.
- `lake exe axiomsweep --check` - kernel-level axiom/`sorry` regression gate against
  `scripts/axiom_baseline.json` (run after `lake build`).

## Script Inventory

### `AxiomSweep.lean` (`lake exe axiomsweep`)

Kernel-level axiom/`sorry` accounting for every reportable `CompPoly.*` declaration,
computed from the built `.olean` environment, with a committed regression baseline
(`axiom_baseline.json`). `--check` fails only on new taint; `--update-baseline`
refreshes the baseline; `--out FILE` writes a full per-declaration report. Bare and
generated native-compiler trust is rejected regardless of the baseline. See the module
docstring for modes and known blind spots.

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

It also enforces one library-specific rule, `ERR_PCARD`: a file under `CompPoly/Fields/`
or `tests/CompPolyTests/Fields/` may not name an irreducibility criterion stated at
`Fintype.card F` outside a comment, because a concrete field must call that criterion's
`_of_card` form. The banned names are listed in `PLAIN_CARD_CRITERIA`; extend that list
whenever a criterion gains an `_of_card` form. Two neighbouring knobs move less often but
matter as much: `PLAIN_CARD_SCOPE` is the subtree list, which has to grow if concrete fields
ever live outside those two paths, and `PLAIN_CARD_OWNERS` exempts the files that *state*
the criteria rather than applying them. `tests/CompPolyTests/Data/` stays out of scope
because those tests name the plain forms deliberately, to pin that each `_of_card` form
recovers its plain statement. See `docs/wiki/field-extensions.md` for the rationale.

Use this directly only when you want to lint a specific subset of files.

### `gen_rabin_certificate.py`

TCB-external generator for kernel-checkable Rabin irreducibility certificates of a
monic polynomial `f` over a prime field `F_p`. Computes the repeated-squaring steps
for `X^(p^d) mod f` (the trace condition) and, for each prime factor `l` of
`d = deg f`, the steps for `X^(p^(d/l)) mod f` plus a Bezout pair witnessing
`gcd(f, X^(p^(d/l)) - X) = 1` (the coprimality conditions). Emits them as JSON, and
with `--lean` as a complete compilable Lean module. Nothing it produces is trusted:
the Lean side re-checks every step in the kernel via `rfl`.

The per-prime-factor loop matters at composite `d`: checking only the linear-factor
case `gcd(f, X^p - X)` admits a product of equal-degree factors, so a product of two
irreducible cubics would be reported irreducible at `d = 6`.

Parameterized by `--p` and `--f` (little-endian monic coefficients); defaults to
KoalaBear with `f = x^5 + x^2 - 1`. Used to build the degree-5 and degree-6 KoalaBear
extensions. The exit code is the verdict — non-zero means `f` is reducible — so the
script doubles as a checker.

Run `python3 scripts/gen_rabin_certificate.py --self-test` to check the generator
against known-answer cases, including a reducible sextic that the prime-degree form of
the test would wrongly accept.

### `check-docs-integrity.py`

Three checks over every tracked `.md` file:

1. `CLAUDE.md` exists and is a symlink to `AGENTS.md`.
2. Local markdown links resolve.
3. Backticked source paths — `` `CompPoly/Univariate/Basic.lean` `` and friends,
   with extensions `.lean`, `.py`, `.sh`, `.yml`, `.bib` — point at files that
   exist.

The third check is the one that catches module splits and renames, since the docs
cite far more paths in backticks than in markdown links. Bare filenames with no
directory, glob patterns, and paths ending in `/` are skipped as prose. Paths may
be written relative to the repo root, to the citing file's directory, or to one of
the subtree roots in `PATH_PREFIXES` — so a page about `Fields/` may write
`KoalaBear/Ext4.lean`. Adding a prefix weakens the check; prefer fixing the doc.

### `build_timing_report.sh`

Helper used by CI to measure and render build timings. Labels:

- `warm_rebuild` — default library gate: `lake build` with cached oleans
  (incremental; only dirty modules rebuild).
- `test_path` — `lake test`.
- `clean_build` — `rm -rf .lake/build && lake build`, when Lean Action CI
  detects a `lean-toolchain` or `lake-manifest.json` change vs the comparison
  base, or when the workflow is run manually with the `clean_build` input.

The CI workflow uploads timing-data artifacts so PR runs can compare against a
previously recorded baseline without rerunning that baseline in the same job.
This supports
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
