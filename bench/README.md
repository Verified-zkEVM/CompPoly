# Evaluation Benchmarks

This directory contains the compiled evaluation benchmark executable for
CompPoly. The benchmark is intentionally small enough for CI, but broad enough
to cover the main polynomial evaluation surfaces and the existing additive NTT
implementation.

## Running

Run the benchmark from the repository root:

```bash
lake exe CompPolyBench
```

The executable is defined by the `CompPolyBench` Lake target and uses
`bench/CompPolyBench.lean` as its source module.

For routine validation after editing the benchmark, run:

```bash
lake build
lake exe CompPolyBench
```

## Output

Each benchmark run writes two generated artifacts under `bench/`, with both the
`jsonl` and the `.md` reports.

```text
evaluation-bench-results-YYMMDD-HHMMSS.jsonl
evaluation-bench-report-YYMMDD-HHMMSS.md
```

Generated benchmark artifacts are ignored by `bench/.gitignore`.

## What Is Measured

The benchmark covers the main polynomial evaluation paths and the existing
additive NTT implementation. It currently includes univariate, multivariate,
multilinear, bivariate, and additive NTT cases over the concrete field
configurations defined in `bench/CompPolyBench.lean`.

Each record includes the benchmark name, representation, method, field or
configuration, input shape, iteration counts, elapsed nanoseconds, average time,
and checksum. The exact benchmark cases and input shapes live in the Lean source
so that this README does not duplicate benchmark configuration.

## Determinism

Input generation is deterministic. The benchmark uses a fixed seed:

```text
20260504
```

Polynomial coefficients and evaluation points are generated from Lean core's
`StdGen` / `randNat` support.

The benchmark output is deterministic in its inputs and checksums, but timing
results still vary with machine load, CPU behavior, and CI environment.

## Interpreting Results

The benchmark is useful for trend tracking and local comparison, but CI
performance comparisons should not be treated as pass/fail gates yet.

Current reports use wall-clock averages. They do not yet record min, max,
median, percentiles, or variance.

The benchmark also measures the current implementations as they exist. For
example, `Goldilocks.Field` is currently generic `ZMod` arithmetic, not a
specialized `UInt64` Goldilocks implementation.

## CI

GitHub Actions builds and runs `CompPolyBench`. Generated reports are uploaded
as the `evaluation-bench-results` artifact, and the Markdown report is appended
to the GitHub Actions step summary.
