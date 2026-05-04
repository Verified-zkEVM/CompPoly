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

Each benchmark run writes two generated artifacts under `bench/`:

```text
evaluation-bench-results-YYMMDD-HHMMSS.jsonl
evaluation-bench-report-YYMMDD-HHMMSS.md
```

For example:

```text
evaluation-bench-results-260504-141633.jsonl
evaluation-bench-report-260504-141633.md
```

The JSONL file is the machine-readable output. Each line is one benchmark
record.

The Markdown report is the human-readable output used by CI artifacts and the
GitHub Actions step summary.

Generated benchmark artifacts are ignored by `bench/.gitignore`.

## What Is Measured

The benchmark currently records:

- benchmark name,
- representation,
- evaluation method,
- field or concrete configuration,
- input shape,
- warmup iterations,
- measured iterations,
- total measured nanoseconds,
- average nanoseconds per measured call,
- checksum.

Warmup iterations are run before timing and are not included in the reported
total or average.

The checksum forces benchmark outputs to be consumed. It is not a cryptographic
checksum.

## Current Cases

### Univariate

Dense univariate evaluation is measured over:

- `BabyBear.Field`,
- `Goldilocks.Field`,
- `BN254.ScalarField`.

For each field, the benchmark compares:

- `eval₂ sum-of-powers`,
- `eval₂Horner`.

The dense shape is:

```text
degree<512, dense, 32 points
```

This means a 512-coefficient polynomial, with all coefficient positions
populated from the deterministic input stream, evaluated by cycling over 32
pre-generated points during repeated iterations.

Sparse univariate evaluation is currently measured only over `BabyBear.Field`,
with one nonzero coefficient position per four coefficients.

### Multivariate

The multivariate case measures `CMvPolynomial.eval` over `BabyBear.Field`:

```text
3 vars, 512 generated terms, sparse coeffs, 32 points
```

### Multilinear

The multilinear cases measure both coefficient-form and hypercube-evaluation
form over `BabyBear.Field`:

- `CMlPolynomial.eval`,
- `CMlPolynomialEval.eval`.

Both use 8 variables and 32 pre-generated evaluation points.

### Bivariate

The bivariate case measures `CBivariate.evalEval` over `BabyBear.Field`:

```text
xDegree<32, yDegree<16, sparse coeffs, 32 points
```

### Additive NTT

The additive NTT case measures the existing computable additive NTT
implementation over the known-good concrete binary tower configuration:

```text
ConcreteBTField 0 -> BTF3, l=2, R_rate=2
```

The input shape is:

```text
4 input coeffs, 16 output evals
```

This case uses fewer measured iterations than the other cases because the
current implementation is proof-oriented and substantially slower.

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

GitHub Actions runs:

```bash
lake exe CompPolyBench
```

The generated Markdown and JSONL files are uploaded as the
`evaluation-bench-results` artifact. Markdown reports are also appended to the
GitHub Actions step summary.
