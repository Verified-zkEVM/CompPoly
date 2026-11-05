# Scripts

This directory contains the main helper scripts for local validation and CI support.

## Recommended Entry Points

- `./scripts/update-lib.sh` - regenerate `CompPoly.lean` from tracked source files.
- `./scripts/check-imports.sh` - verify that `CompPoly.lean` is up to date.
- `./scripts/lint-style.sh` - run the Lean style linter and repo-wide Lean-file
  checks.
- `uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py` - verify the `CLAUDE.md` symlink,
  local markdown links, and backticked source paths across the handbook.
- `lake exe axiomsweep --check` - kernel-level axiom/`sorry` regression gate against
  `scripts/axiom_baseline.json` (run after `lake build`).
- `./scripts/bench-ab.sh run <group>` - A/B the current build against a frozen
  baseline on one benchmark group and print a verdict per row.
- `uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main` -
  report possible writing defects in the prose that the branch changes (advisory).

## Script Inventory

### `AxiomSweep.lean` (`lake exe axiomsweep`)

The axiom sweep gives kernel-level axiom/`sorry` accounting for every reportable
`CompPoly.*` declaration. It computes the accounting from the built `.olean`
environment and compares it with a committed regression baseline
(`axiom_baseline.json`). The sweep rejects bare and generated native-compiler trust
regardless of the baseline.

`--check` fails only on new taint. `--update-baseline` refreshes the baseline.
`--out FILE` writes a full per-declaration report. See the module docstring for modes
and known blind spots.

### `update-lib.sh`

The script regenerates [`../CompPoly.lean`](../CompPoly.lean) from the tracked
`CompPoly/**/*.lean` files. Run it after you add, rename, or delete source files
under `CompPoly/`.

### `check-imports.sh`

The script runs `update-lib.sh` and compares the result with the committed
`CompPoly.lean`. It fails if the generated umbrella import file is stale.

Use this script in these cases:

- You changed the source tree layout.
- CI reports that the imports are out of date.
- You want a quick check before you push.

### `lint-style.sh`

The script runs the Lean style linter across the repository. It then runs a few
repo-wide checks, such as executable-bit detection and filename collisions.

`lint-style.sh` is the higher-level wrapper around `lint-style.py`.

### `lint-style.py`

`lint-style.py` is the underlying Python linter for Lean style issues. It checks module docstrings,
line length, forbidden imports or tactics, trailing whitespace, and the local
`native_decide` policy, while honoring entries in `style-exceptions.txt`.

Use this script directly only when you want to lint a specific subset of files.

### `check-writing.py`

`check-writing.py` is an advisory writing checker for the
[writing standard](../docs/wiki/writing.md). It reads
Markdown files and the comments and docstrings of Lean files. `lint-style.py` checks
the source style of Lean code, and `check-writing.py` checks the prose. It reports
optional suggestions about listed vocabulary, phrasal verbs, Latin abbreviations, contractions,
history words in reference documents and approximate sentence lengths. It does not judge grammar
or clarity. Leave clear, correct prose alone. The [vocabulary](../docs/wiki/writing-vocabulary.md)
provides the word list.

It has three modes. `--base REF` checks the prose that changed since the merge base
with `REF`. A list of files checks all prose in those files. `--stdin LABEL` checks
standard input, such as a PR description. In `--base` mode, it skips generated files.

Findings return exit code 0. CI reports them as warnings.
Usage, Git, and configuration errors return exit code 2.
Non-UTF-8 source input and symlinks produce advisory Input diagnostics. Symlink targets are not
read as source prose. A suggestion does not establish a defect or require a rewrite.

A finding is a prompt to read the passage. It is not a verdict on the prose.
[`write-technical-prose.md`](../docs/wiki/write-technical-prose.md) describes how to
use it.

### `test-check-writing.py`

Unit tests for `check-writing.py`. Run them with
`uv run --no-project --python 3.12 python scripts/test-check-writing.py` after you
change the checker or the "Words to avoid" table of the vocabulary.

### `gen_mersenne31_circle_certificate.py`

The script emits the `generatorDoublings` declaration for the Mersenne31 circle
generator by 30 successive doublings modulo `2^31 - 1`. It prints the declaration without modifying
source files. Run `uv run --no-project --python 3.12 python scripts/gen_mersenne31_circle_certificate.py --check` to
verify the checked-in data, or pass a Lean file after `--check` to compare that file.
The script is outside the trusted code base: Lean checks every step with kernel
`decide` and proves the connection to scalar multiplication. See the
[circle-group documentation](../docs/wiki/field-extensions.md#mersenne31-circle-group).

### `gen_rabin_certificate.py`

The script is a generator outside the TCB. It produces kernel-checkable Rabin
irreducibility certificates for a monic polynomial `f` over a prime field `F_p`.
It computes the repeated-squaring steps for `X^(p^d) mod f` (the trace condition).
For each prime factor `l` of `d = deg f`, it also computes the steps for
`X^(p^(d/l)) mod f` and a Bezout pair witnessing `gcd(f, X^(p^(d/l)) - X) = 1` (the
coprimality conditions). It emits them as JSON, and with `--lean` as a complete
compilable Lean module. Nothing it produces is trusted: the Lean side re-checks every
step in the kernel via `rfl`.

The per-prime-factor loop matters at composite `d`. A check of only the linear-factor
case `gcd(f, X^p - X)` admits a product of equal-degree factors. For example, it
would report a product of two irreducible cubics as irreducible at `d = 6`.

The parameters are `--p` and `--f` (little-endian monic coefficients). The defaults
are KoalaBear with `f = x^5 + x^2 - 1`. The script built the degree-5 and degree-6
KoalaBear extensions. The exit code is the verdict: non-zero means that `f` is
reducible. The script is therefore also a checker.

Run `uv run --no-project --python 3.12 python scripts/gen_rabin_certificate.py --self-test` to check the generator
against known-answer cases, including a reducible sextic that the prime-degree form of
the test would wrongly accept.

### `check-docs-integrity.py`

The script makes three checks over every tracked `.md` file:

1. `CLAUDE.md` exists and is a symlink to `AGENTS.md`.
2. Local markdown links resolve.
3. Backticked source paths, such as `` `CompPoly/Univariate/Basic.lean` ``, point at
   files that exist. The check covers the extensions `.lean`, `.py`, `.sh`, `.yml`,
   and `.bib`.

The third check catches module splits and renames, because the docs cite far more
paths in backticks than in markdown links. The check skips bare filenames with no
directory, glob patterns, and paths ending in `/`. A path can be relative to the
repo root, to the directory of the citing file, or to one of the subtree roots in
`PATH_PREFIXES`. For example, a page about `Fields/` can write `KoalaBear/Ext4.lean`.
Each added prefix weakens the check, so prefer a fix to the doc.

### `build_timing_report.sh`

CI uses this helper to measure and render build timings. The labels are:

- `warm_rebuild` — default library gate: `lake build` with cached oleans. The
  build is incremental, so only dirty modules rebuild.
- `test_path` — `lake test`.
- `clean_build` — `rm -rf .lake/build && lake build`. Lean Action CI runs it when
  `lean-toolchain` or `lake-manifest.json` differs from the comparison base, or
  when a manual run sets the `clean_build` input.

The CI workflow uploads timing-data artifacts so PR runs can compare against a
previously recorded baseline without rerunning that baseline in the same job.
This supports
[`../.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml).

### `bench-ab.sh`

The script drives the optimization loop in
[`../docs/wiki/autoresearch.md`](../docs/wiki/autoresearch.md). It has three
subcommands:

- `freeze [--force]` builds `CompPolyBench` and keeps a copy under
  `bench/out/ab/baseline/` together with the commit it came from.
- `run <group>[,<group>...]` builds the current tree once. It then runs the frozen
  baseline and the fresh binary alternately on the given groups and the harness
  self-check. `BENCH_AB_ROUNDS` (default 5) sets the rounds, and `BENCH_AB_PRESET`
  (default `medium`) sets the preset. Each invocation writes to its own `--out-dir`.
  The command finishes with `CompPolyBench --compare` and returns its exit code.
- `clean [--all]` removes comparison runs under `bench/out/ab/`.

Use this script in these cases:

- You changed a fast implementation and want to know whether it got faster.
- You want a same-machine number rather than one compared against yesterday's.
- An agent iterates on an arithmetic kernel and needs a keep-or-revert signal.

The script writes only under `bench/out/`, which git ignores. It never runs
`lake exe` after measurement starts, so a rebuild cannot race a run.

## Typical Workflows

### Optimizing a fast kernel

```bash
./scripts/bench-ab.sh freeze
# edit one kernel
lake build
lake exe CompPolyBench --validate-only --groups fields-koalabear-mul
./scripts/bench-ab.sh run fields-koalabear-mul
```

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
uv run --no-project --python 3.12 python ./scripts/check-docs-integrity.py
uv run --no-project --python 3.12 python scripts/check-writing.py --base origin/main
```
