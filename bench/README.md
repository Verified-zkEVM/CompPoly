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
lake exe CompPolyBench univariate-low-product-babybear
lake exe CompPolyBench --group univariate-low-product-babybear --group additive-ntt-btf3-l2-r2
lake exe CompPolyBench --groups univariate-low-product-babybear,additive-ntt-btf3-l2-r2
lake exe CompPolyBench --small univariate-low-product-babybear
```

Output modes:

```bash
lake exe CompPolyBench --json-only univariate-low-product-babybear
lake exe CompPolyBench --markdown-only --groups univariate-low-product-babybear,additive-ntt-btf3-l2-r2
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

The benchmark covers evaluation paths, direct and NTT-backed univariate
multiplication, and additive NTT implementations.

## Determinism

Input generation uses a fixed seed. Checksums are stable for the same group
selection and preset.

## CI

GitHub Actions runs `lake exe CompPolyBench --medium`, uploads generated
artifacts, and appends the Markdown report to the step summary.
