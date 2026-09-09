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

Each run writes generated JSONL and Markdown reports under `bench/out/`, which
is created on demand and ignored in its entirety:

```text
bench/out/results-YYMMDD-HHMMSS.jsonl
bench/out/report-YYMMDD-HHMMSS.md
```

By default, a run writes both files. A checksum mismatch is reported in the
Markdown report and makes the executable exit nonzero after writing artifacts.
Within each group, checksums are computed over the shared prefix of iterations
run by every implementation in that group, capped at `validationIterationCap`.

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
(`mixChecksum`) over the full result. It is capped at
`validationIterationCap` iterations — above every benchmark's operand-pool
size, so the oracle sees every input, without the pass costing as much as the
measurement it validates. This is what the group agreement check
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

### Sampling and dispersion

A benchmark's cost is collected as a *set* of samples, not one total. Each
benchmark's iteration count is treated as a total-work budget and split into up
to `targetSampleCount` timed samples; every sample replays the same iteration
indices, so samples differ only in machine state.

Reports show the **median** sample as the headline number and a `Spread` column
holding the median absolute deviation as a percentage of the median:

| Spread | Meaning |
|---|---|
| `±2.4%` | normal: 20 samples, MAD 2.4% of the median |
| `±1.1% (n=3)` | replicated, but too few times for the spread to mean much |
| `n=1` | one iteration exhausted the budget; a single unrepeated sample |
| `±0.4% !2` | two samples were labelled severe Tukey outliers |

`n=1` rows carry no dispersion information at all and no ratio should be read
off them. They occur where a single iteration is already expensive; the fix is a
smaller input shape, not more iterations.

Outliers are **labelled, never dropped**, at the conventional Tukey fences of
1.5x and 3x the interquartile range. Labelling is suppressed when the
interquartile range is zero, since fences of zero width would mark every sample
that differs at all. The full per-sample vector is emitted as `samples_picos` in
the JSONL, along with `min`, `median`, `mean`, `p95`, `stddev` and `mad` in
picoseconds per iteration.

Warmup is at least one sample's worth of iterations regardless of the preset, so
no benchmark is measured entirely cold.

### Harness self-check

`harness-floor` times an empty body, giving the per-iteration cost of the loop
and the sink; every other benchmark's reported time sits on top of it.
`harness-canary` times a body with a known, non-eliminable cost and **fails the
run** if it does not exceed the floor by at least `canaryFloorRatio`. A benchmark
that has been optimised away otherwise looks exactly like a benchmark that got
very fast, and the canary is what tells the two apart. Both are measured whenever
either is selected, because the check is a comparison between them.

## Determinism

Each group derives its own input generator from its key (`genFor`), so a group's
inputs do not depend on which other groups ran, or in what order. Concretely:

- `--group X` and `--groups X,Y` measure the same inputs for `X`, in either order;
- adding, removing or renaming a group changes nothing for any other group;
- the curated CI subset measures the same inputs as a full local run;
- a checksum is comparable across runs and across commits, so a change in one is
  a real change in behaviour rather than a change in the input schedule.

Checksums remain a cross-check between the implementations within a group; that
they are now also stable across runs is what makes them usable as regression
fixtures. Digests are still preset-dependent, because the validation pass runs
`min validationIterationCap` of the group's measured iteration count and that
count varies by preset.

## The two CI tracks

Correctness and timing are separated, because only one of them is trustworthy on
a shared runner.

**Correctness gates every PR.** `lean_action_ci.yml` runs

```bash
lake exe CompPolyBench --medium --validate-only --groups "<curated set>"
```

which does the untimed digest pass and the group agreement check but collects no
samples. It takes about 34 seconds over the curated set and fails the run on a
digest mismatch or a collapsed harness canary. `--validate-only` is worth running
locally for the same reason: it is the fast way to ask whether an implementation
is still correct.

**Timings run on demand.** `benchmarks.yml` produces them three ways: **Actions →
Benchmarks → Run workflow** with a preset and optional group list, a `/bench`
comment on a PR from a repo member, or automatically on any PR touching
`bench/**`. Results are posted as a PR comment and uploaded as an artifact.

They are kept out of the blocking path deliberately, though not for the reason
you might expect. *Within* one run the shared runner is actually steadier than a
busy laptop — median MAD 0.2% against 1.4% locally — but severe outliers are
about twice as common, and neither figure is the one a gate needs. What a
regression gate compares is **runs against each other**, on a runner whose CPU
model changes between runs, and no single run can measure that. Until it is
measured, the timings are advisory.

## The curated group set

Both tracks default to the group list in `bench/ci-groups.txt` — one key per
line, `#` comments ignored. Neither runs every registered group, so **a new group
must be added there to be covered**. An unknown key fails the run, so a renamed
group is caught rather than silently dropped.
