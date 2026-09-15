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
bench/out/manifest-YYMMDD-HHMMSS.json
```

The manifest records what produced the numbers — commit, whether the tree was
dirty, toolchain, preset and the budget it resolved to, seed, selection, and
host details — and is written for every run, `--validate-only` included. It is
a separate file rather than a header line in the JSONL, because every consumer
of that file assumes uniform records.

By default, a run writes both files. A checksum mismatch is reported in the
Markdown report and makes the executable exit nonzero after writing artifacts.
Within each group, checksums are computed over the group's `digestPeriod` — the
period of its bodies in the iteration index, capped at `digestIterationCap`.

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
| Base-field arithmetic | `fields-{koalabear,babybear,mersenne31,goldilocks}-{mul,add,inv,pow}`: canonical `ZMod` vs native-word, latency and throughput |
| Pairing scalar multiplication | `fields-{bn254,bls12-381,bls12-377}-mul` |
| Scalar-field inversion | `fields-mont64x8-*-inv`: `ZMod` extended Euclid vs checked binary GCD vs Fermat |
| Binary tower scalar kernels | `fields-tower-bt{8,64}-*`: table-driven vs recursive |
| Multiplicative NTT | `ntt-{koalabear,babybear}-l*` over `n = 2^8 … 2^16`, plus `ntt-plan-koalabear` |
| Reed-Solomon encoding | `rs-encode-koalabear-l*`: definitional encoder vs the certified NTT one |
| Schoolbook / NTT crossover | `univariate-mul-crossover-*`, degree<4 to degree<1024 |
| Harness self-check | `harness-floor`, `harness-canary`, `harness-chain-floor`, `harness-chain-linearity`: the harness measuring itself, see below |

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

`runTimedSpec` does two passes over each benchmark body.

The **validation pass** is untimed and folds a strong `Nat` digest
(`mixChecksum`) over the full result. It runs for `digestPeriod` iterations —
the period of the body in its iteration index, capped at `digestIterationCap`,
so the oracle sees every input without the pass costing as much as the
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

### Chained bodies and the per-unit column

An operation of one or two nanoseconds cannot be measured one per timed
iteration: the harness floor is about the same size, and the operand-pool
idiom around it — `xs.getD (i % xs.size) unit` — is a boxed-`Nat` modulo, a
bounds check and a boxed array read, twice. So the field and kernel groups
perform their operation `workUnits` times per iteration, through the
combinators in `bench/CompPolyBench/Harness/Chain.lean`, and the report gains a
**Per unit (ps)** column dividing the median by that count.

Two shapes, reported separately because a prover is bounded by different ones
in different places, and named as Plonky3 names them:

- **latency** — each operation depends on the last, so the pipeline cannot
  overlap two;
- **throughput** — ten independent accumulators, so it can.

Every row of a group must agree on `workUnits`, because the count describes the
*problem* and not the implementation; a group whose rows disagree fails the
run. A per-unit number is **not** comparable with `harness-floor`, which is a
per-iteration cost: the chain floor for comparison is `harness-chain-floor`.

### Sampling and dispersion

A benchmark's cost is collected as a *set* of samples, not one total, and the
sizes come from the preset's wall-clock budget rather than from a written-down
iteration count. A calibration ramp times 1, 2, 4, … iterations until the
warmup budget is met — the ramp *is* the warmup — and its last step estimates
the per-iteration cost. That estimate fixes how many iterations make up a
`sampleNanos` sample, and `measureNanos` caps how many samples the row can
afford. Every sample replays the same iteration indices, so samples differ only
in machine state.

A consequence worth knowing: `Iterations` is no longer comparable between runs,
because it depends on how fast the machine was when the row was calibrated.
`Median` and `Spread` are the columns to compare.

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

`harness-chain-floor` and `harness-chain-linearity` do the same two jobs for
chained bodies. The floor group carries the cheapest honest operation in both
chain shapes, so a per-unit number can be read against something; the linearity
group **fails the run** unless eight times the chain length costs at least four
times as much, which is what catches a chain the compiler has collapsed.

Both checks earn their keep. The chain floor's first operation was
`x ^^^ (x >>> 7)`, whose 64-deep block is algebraically the identity in
characteristic two, and LLVM found that: the row reported a sixteenth of a
cycle per operation *and the linearity check still passed*, because what
collapsed was each block rather than the loop over blocks.

## Determinism

Each group derives its own input generator from its key (`genFor`), so a group's
inputs do not depend on which other groups ran, or in what order. Concretely:

- `--group X` and `--groups X,Y` measure the same inputs for `X`, in either order;
- adding, removing or renaming a group changes nothing for any other group;
- the curated CI subset measures the same inputs as a full local run;
- a checksum is comparable across runs and across commits, so a change in one is
  a real change in behaviour rather than a change in the input schedule.

Checksums remain a cross-check between the implementations within a group; that
they are also stable across runs, and across presets, is what makes them usable
as regression fixtures. The digest length is the period of the group's bodies in
the iteration index, which is a property of the benchmark rather than of the
preset or the machine it runs on.

## The two CI tracks

Correctness and timing are separated, because only one of them is trustworthy on
a shared runner.

**Correctness gates every PR.** `lean_action_ci.yml` runs

```bash
lake exe CompPolyBench --medium --validate-only --groups "<curated set>"
```

which does the untimed digest pass and the group agreement check but collects no
samples. It takes about 29 seconds of CPU over the curated set and fails the run on a
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
