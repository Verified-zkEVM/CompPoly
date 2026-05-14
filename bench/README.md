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

## Output

Each run writes generated JSONL and Markdown reports under `bench/`:

```text
evaluation-bench-results-YYMMDD-HHMMSS.jsonl
evaluation-bench-report-YYMMDD-HHMMSS.md
```

Generated benchmark artifacts are ignored by `bench/.gitignore`.

## What Is Measured

The benchmark covers the main polynomial evaluation paths and the existing
additive NTT implementation. Exact cases, input shapes, deterministic input
generation, and reported fields are defined in `bench/CompPolyBench.lean`.

## Determinism

Input generation is deterministic and uses a fixed seed. This keeps
the generated polynomial data and evaluation points fixed across runs,
so checksums should stay stable.

## CI

GitHub Actions builds and runs `CompPolyBench`, uploads generated reports as
the `evaluation-bench-results` artifact, and appends the Markdown report to the
step summary.
