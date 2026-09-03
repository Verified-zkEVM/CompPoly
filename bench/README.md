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
| Binary tower fields | `fields-tower-bt128-*`: `BitVec` spec vs packed-word implementation |
| Goldilocks arithmetic | `fields-goldilocks-{mul,inv}`: canonical `ZMod` vs single-word `UInt64` |
| Scalar-field inversion | `fields-mont64x8-*-inv`: `ZMod` extended Euclid vs checked binary GCD vs Fermat |
| Harness self-check | `harness-floor`, `harness-canary`: the harness measuring itself, see below |

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

## How A Benchmark Is Measured

`runTimed` does two passes over each benchmark body.

The **validation pass** is untimed and folds a strong `Nat` digest
(`mixChecksum`) over the full result. This is what the group agreement check
compares, and it is the reason a wrong-but-fast implementation cannot be
benchmarked: a mismatch inside a group exits nonzero.

The **timed pass** folds each result through `sink : α → UInt64` instead. A sink
exists only to keep the result live so the body cannot be optimised away; its
value is never compared against anything. The default sink truncates the `Nat`
digest, which is free when that digest already fits a machine word. Pass an
explicit `sink :=` when it does not:

- carriers whose canonical value exceeds `2 ^ 63` — a `Nat` digest there
  allocates a bignum on most inputs (`sinkGoldilocksFast`, `sinkZMod`);
- aggregate results — sink a fixed-position sample rather than walking the whole
  structure, and make every row of a group sink the *same* shape, or the group's
  ratio measures the digests rather than the implementations.

Both rows of a group should carry comparable sink cost. Where a representation
makes that impossible — a `ZMod` element above `2 ^ 63` has no cheap word digest
while its fast counterpart does — the residual shows up in `harness-floor`
territory and the group's ratio is a lower bound on the real speedup.

### Harness self-check

`harness-floor` times an empty body, giving the per-iteration cost of the loop
and the sink; every other benchmark's reported time sits on top of it.
`harness-canary` times a body with a known, non-eliminable cost and **fails the
run** if it does not exceed the floor by at least `canaryFloorRatio`. A benchmark
that has been optimised away otherwise looks exactly like a benchmark that got
very fast, and the canary is what tells the two apart. Both are measured whenever
either is selected, because the check is a comparison between them.

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
