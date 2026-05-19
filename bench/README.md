# Evaluation Benchmarks

This directory contains the compiled benchmark executable for
CompPoly. The benchmark is intentionally small enough for CI, but broad enough
to cover the main polynomial evaluation surfaces, direct univariate
multiplication, root-of-unity NTT multiplication, and the existing additive NTT
implementation.

## Running

Run the benchmark from the repository root:

```bash
lake exe CompPolyBench
```

The executable is defined by the `CompPolyBench` Lake target. Its entrypoint is
`bench/CompPolyBench.lean`; shared helpers live in
`bench/CompPolyBench/Common.lean`, and `bench/CompPolyBench/Setup.lean`
assembles the full suite.

Benchmark files mirror the source tree they exercise. For example,
benchmarks for `CompPoly/Univariate/NTT/FastMul.lean` live in
`bench/CompPolyBench/Univariate/NTT/FastMul.lean`, and benchmarks for
`CompPoly/Fields/Binary/AdditiveNTT/Impl.lean` live in
`bench/CompPolyBench/Fields/Binary/AdditiveNTT/Impl.lean`.

## Output

Each run writes generated JSONL and Markdown reports under `bench/`:

```text
evaluation-bench-results-YYMMDD-HHMMSS.jsonl
evaluation-bench-report-YYMMDD-HHMMSS.md
```

Generated benchmark artifacts are ignored by `bench/.gitignore`.

The JSONL output remains one row per benchmark case. The Markdown report groups
rows into separate result tables when those rows are expected to produce a
matching checksum.

## What Is Measured

The benchmark covers the main polynomial evaluation paths, direct versus
NTT-backed univariate multiplication, and the existing additive NTT
implementation. Exact cases, input shapes, deterministic input generation, and
reported fields are defined by the benchmark modules under `bench/CompPolyBench/`.

## Determinism

Input generation is deterministic and uses a fixed seed. This keeps
the generated polynomial data and evaluation points fixed across runs,
so checksums should stay stable.

## CI

GitHub Actions builds and runs `CompPolyBench`, uploads generated reports as
the `evaluation-bench-results` artifact, and appends the Markdown report to the
step summary.
