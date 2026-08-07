# Evaluation Benchmarks

This directory contains the compiled benchmark executable for CompPoly.

## Running

Run the benchmark from the repository root:

```bash
lake exe CompPolyBench
```

Presets:

```bash
lake exe CompPolyBench --large
lake exe CompPolyBench --medium
lake exe CompPolyBench --small
```

The default preset is `--large`. CI uses `--medium`.
Presets only change warmup and measured iteration counts; they do not change
which benchmark groups run.

List benchmark groups:

```bash
lake exe CompPolyBench --list
```

Run selected groups:

```bash
lake exe CompPolyBench univariate-low-product-koalabear
lake exe CompPolyBench --group univariate-low-product-koalabear --group additive-ntt-btf3-l2-r2
lake exe CompPolyBench --groups univariate-low-product-koalabear,additive-ntt-btf3-l2-r2
lake exe CompPolyBench --small univariate-low-product-koalabear
```

Output modes:

```bash
lake exe CompPolyBench --json-only univariate-low-product-koalabear
lake exe CompPolyBench --markdown-only --groups univariate-low-product-koalabear,additive-ntt-btf3-l2-r2
```

## Output

Each run writes generated JSONL and Markdown reports under `bench/`:

```text
results-YYMMDD-HHMMSS.jsonl
report-YYMMDD-HHMMSS.md
```

By default, a run writes both files. A checksum mismatch is reported in the
Markdown report and makes the executable exit nonzero after writing artifacts.
Within each group, checksums are computed over the shared prefix of iterations
run by every implementation in that group.

## What Is Measured

Roughly by area, with representative group prefixes:

| Area | Groups |
|---|---|
| Univariate evaluation and multiplication | `univariate-dense-*`, `univariate-sparse-*`, `univariate-mul-*`, `univariate-low-product-*` |
| Modular reduction | `univariate-mod-by-monic-*`, `univariate-monic-remainder-*` |
| Batch and many-polynomial evaluation | `univariate-batch-*`, `univariate-many-one-point-*` |
| Multilinear and multivariate | `multilinear-coeff-*`, `multilinear-hypercube-*`, `multilinear-many-mle-*`, `multivariate-dense-*`, `multivariate-sparse-*` |
| Bivariate | `bivariate-full-*` (evaluation and Kronecker-backed multiply), `bivariate-divlinear-*` and `bivariate-deflate-*` (linear-factor deflation) |
| Guruswami-Sudan decoding | `guruswami-sudan-core-*`, across dense / Lee-O'Sullivan interpolation and Roth-Ruckenstein / Alekhnovich root search |
| Univariate root finding | `univariate-roots-finite-field-*` |
| Additive NTT | `additive-ntt-btf*` |
| Extension fields | `fields-extension-*-mul`, `fields-extension-*-inv` |
| Scalar-field inversion | `fields-mont64x8-*-inv`: `ZMod` extended Euclid vs checked binary GCD vs Fermat |

Use `--list` for the authoritative set; the prefixes above drift as groups are
added.

Some groups run each implementation over both the canonical `ZMod`
representation and the native-word Montgomery representation, so the two appear as
separate rows in the same group and are cross-checked against each other. KoalaBear,
BabyBear, and the large scalar fields are covered this way:

```text
univariate-dense-koalabear    univariate-dense-babybear
univariate-mul-koalabear      univariate-mul-babybear
univariate-dense-bn254
univariate-dense-bls12-381    univariate-dense-bls12-377
```

## Determinism

Input generation uses a fixed seed. Checksums are stable for the same group
selection and preset. They are a cross-check between implementations within one
group, not a value to compare across runs: the generator is threaded through the
selected groups in order, so changing the selection — or adding a group — changes
the inputs, and therefore the checksums, of the groups that follow it.

## CI

GitHub Actions runs `lake exe CompPolyBench --medium` over the curated group list
in the `BENCH_CI_GROUPS` environment variable, uploads generated artifacts, and
appends the Markdown report to the step summary.

CI does not run every registered group, so **a new group must be added to
`BENCH_CI_GROUPS` in `.github/workflows/lean_action_ci.yml` to be covered there**.
An unknown key in that list fails the run, so a renamed group is caught rather than
silently dropped.
