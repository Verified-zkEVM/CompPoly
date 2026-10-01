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

Output directory:

```bash
lake exe CompPolyBench --out-dir bench/out/mine --groups fields-koalabear-mul
```

## Output

Each run writes generated JSONL and Markdown reports under `bench/out/`, which
is created on demand and ignored in its entirety, or under the directory given
by `--out-dir`:

```text
bench/out/results-YYMMDD-HHMMSS.jsonl
bench/out/report-YYMMDD-HHMMSS.md
bench/out/manifest-YYMMDD-HHMMSS.json
```

Run ids have one-second resolution, so two invocations within the same second
would collide in one directory; `--out-dir` exists so a driver can give each
invocation its own.

The manifest records what produced the numbers — commit, whether the tree was
dirty, toolchain, preset and the budget it resolved to, seed, selection, and
host details — and is written for every run, `--validate-only` included. It is
a separate file rather than a header line in the JSONL, because every consumer
of that file assumes uniform records.

## Comparing Two Builds

`--compare` judges a candidate build against a baseline build from the results
files each wrote, one file per invocation. It measures nothing itself.

```bash
lake exe CompPolyBench --compare \
  --baseline bench/out/ab/run/baseline/1 --baseline bench/out/ab/run/baseline/2 \
  --candidate bench/out/ab/run/candidate/1 --candidate bench/out/ab/run/candidate/2 \
  --threshold 5 --out-dir bench/out/ab/run
```

Each path is a `results-*.jsonl` file or a directory holding some. Rows are
matched on `(group_key, name, digest_class, method)`, and each side's evidence
is its per-invocation `median_picos`. A row is `faster` when the ratio of the
two medians is at least `--threshold` percent (default 5) below one **and**
every candidate invocation beat every baseline invocation; `slower` is the
mirror image; everything else is `same`. Rows whose digests or work units differ
between the builds are `mismatch`, and a row absent from some file on one side
is `missing`. A candidate that is implausibly fast with an unchanged digest is
flagged `SUSPECT`. Harness rows, when present on both sides, are reported as
machine drift in the header.

Exit codes: `0` when every row was judged, whatever the verdicts; `1` when
nothing could be compared (a path that does not exist, a malformed file, sides
measured under different presets); `3` when at least one row is `mismatch` or
`missing`.

The intended driver is `scripts/bench-ab.sh`, which freezes a baseline binary,
runs both binaries turn about, and calls `--compare`; the loop built on it is
described in [`docs/wiki/autoresearch.md`](../docs/wiki/autoresearch.md).

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
| Four-limb field arithmetic | `fields-{bn254,bls12-381,bls12-377}-{mul,add}`, `fields-secp256k1-{scalar,base}-{mul,add}`: canonical `ZMod` vs four-limb Montgomery |
| Scalar-field inversion | `fields-mont64x8-*-inv`: `ZMod` extended Euclid vs checked binary GCD vs Fermat |
| Binary tower scalar kernels | `fields-tower-bt{8,64}-*`: table-driven vs recursive |
| Multiplicative NTT | `ntt-{koalabear,babybear}-l*` over `n = 2^8 … 2^16`, plus `ntt-plan-koalabear` |
| Reed-Solomon encoding | `rs-encode-koalabear-l*`: definitional encoder vs the certified NTT one |
| Interpolation | `univariate-interp-koalabear-l*` (Lagrange vs subproduct tree vs NTT vs planned NTT), `univariate-interp-coset-*`, `univariate-barycentric-*` (generic vs closed-form weights) |
| Reed-Solomon decoding | `rs-gao-decode-koalabear-l*`: definitional Gao decoder vs `decodeNTT` / `decodePlan` |
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
- **throughput** — parallel accumulators: two for BN254, ten for other fields.

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

For fork PR runs, the report is available in the Actions summary and artifact; automatic commenting is skipped because the token is read-only. Ordinary PR comments do not cancel benchmark jobs; only a new eligible benchmark job supersedes a running one.

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

## Rust field comparison

Run `python3 scripts/bench-fields.py --suite all --cpu 0` from the repository root on Linux. For scalar field suites, choose an available logical CPU: the driver pins itself and both runners there, builds with one job, and runs Lean and Rust sequentially. It validates matching result digests and operation counts before five paired timing runs in alternating order. `--validate-only` skips timing; `--skip-build` requires a matching build record from a previous driver run.

| Suite | Selected fields and operations | Rust library |
| --- | --- | --- |
| `small-prime` (default) | KoalaBear, Mersenne31, Goldilocks: add/mul latency and throughput, inv/exp latency | Plonky3 0.4.2 |
| `large-prime` | BN254 scalar field: add/mul latency and throughput, inv/exp latency | arkworks 0.5.0 (`ark_bn254::Fr`) |
| `binary` | 8-, 64-, 128-bit Fan–Paar towers: mul latency/throughput, square/inv latency | Binius 0.2.0, pinned Git revision |
| `poly-eval` | One polynomial at one point: KoalaBear, Goldilocks, BN254 scalar, binary tower 128; 2^12, 2^16, 2^20 coefficients | Same libraries, Rayon 1.11 worker pool |
| `all` | The 36 scalar cases plus the polynomial evaluation suite | All three libraries |

One Cargo project under `bench/rust/` shares the measurement and chain harness. Library-specific modules decode inputs and supply canonical checksums and cheap result sinks. Rust nightly-2026-02-26 is pinned for Binius’s x86 support, and Cargo.lock pins dependencies. The driver defaults `RUSTFLAGS` to `-C target-cpu=native` and records its value and the host instruction features; CI builds with the same flag. CI validates all selected suites on every PR; it does not gate on relative speed. Tables show fast Lean against Rust. Prime-field reference implementations still participate in validation and runs, but are omitted from the tables. Binary rows time only the verified fast Lean implementation and Binius; their cross-language result agreement is checked before timing.

Each run creates an ignored `bench/out/fields-*` directory containing exact fixtures, raw samples, a machine/toolchain manifest, and `report.md` suitable for a PR comment. Timings are advisory, especially on a shared host.

### Inputs and field correspondence

`CompPolyFieldFixtures` exports pools in `field-coordinates-le-v1` format with an explicit `basis`. Prime-field operands use `canonical-integer`: fixed-width little-endian integers in `[0, p)`, with the modulus supplied separately. Binary operands use `fan-paar-tower`: little-endian tower coefficients in 1, 8, or 16 bytes, with an empty modulus array. These coordinates are not characteristic-two field numerals. Rust checks the encoding, basis, width, field identity, and workload parameters before decoding. The full coordinate word contributes to the untimed checksum, including both limbs at 128 bits.

BN254 here means the **scalar** field with modulus `21888242871839275222246405745257275088548364400416034343698204186575808495617`, matching `ark_bn254::Fr`, not `Fq`. This common prime and canonical integer representation establish the correspondence. Future binary-field comparisons must additionally establish a basis mapping; equal bit patterns alone do not establish that correspondence.

### Workloads

Rust matches existing Lean batch shapes: 1,280 small-prime add/mul operations, 320 BN254 additions/multiplications, or 64 inv/exp steps with an added constant between steps. Small-prime throughput updates ten lanes from their previous values and combines them with nine extra operations at the end. The reported divisors exclude that merge, matching Lean. Exp uses `0x5A5A5A5A`; inverse maps zero to zero. Only the final batch result is consumed. BN254's timed sink samples native Montgomery words, avoiding canonical conversion or serialization in the timed loop. Rust uses scalar library APIs with native CPU target flags; arkworks parallel and optional assembly features are disabled.

BN254 inversion uses `FastField.invGcd`, the checked binary-GCD path, rather than the default Fermat inverse. Arkworks uses its field `inverse`. Each chain step adds the same fixed constant before inversion; zero maps to zero. BN254 exponentiation uses the same 32-bit exponent `0x5A5A5A5A` as the small fields, not a random full-width exponent.

BN254 add/mul throughput uses two independent chains with the same fixed second operand as latency, 160 steps per lane (320 operations total), four rounds unrolled per loop, and one final combining operation excluded from the divisor. This avoids the ten-lane ring’s excessive live state for multi-limb values. Small-prime throughput retains its ten-lane ring.

The BN254 throughput configuration was selected manually on Rust, then fixed identically in Lean. It is not selected independently per language or tuned during benchmark runs. Rust screening covered 1, 2, 3, 4, 6, and 8 lanes with 1, 4, and 8 rounds unrolled; two lanes avoided the spill overhead of wider configurations. Shortlisted unroll factors were checked again in the production Rust runner.

### Binary tower workloads

`--suite binary` selects three representation boundaries: the 8-bit table base, a 64-bit machine word, and the two-word 128-bit carrier. CompPoly's tower matches Binius's `BinaryField8b`, `BinaryField64b`, and `BinaryField128b`. The dependency is the original [Binius field library](https://github.com/IrreducibleOSS/binius/tree/47675e19c86c0fb676f75437073a77af8e337938/crates/field), pinned because Binius64 uses different field representations. CPU-supported instructions are enabled, but the workloads use scalar field types, not explicit packed SIMD batches.

Multiplication uses 64 dependent steps or two independent 32-step chains with the same fixed operand; the final combining multiply is timed but excluded from the divisor, identically in both languages. Inversion uses 64 dependent `inv(x XOR b)` steps, with zero mapped to zero. Squaring uses 63 dependent squares, unrolled seven at a time. Neither the block nor the complete chain is a whole Frobenius cycle at any selected size. No per-operation result accumulation occurs. The pool holds 64 deterministic full-width words, excluding zero and one to avoid trivial multiplication constants.

The `fields-tower-bt{8,64,128}-{mul,square,inv}` groups replace the old recursive/table comparison and pairwise 128-bit scalar workloads. Historical best-time rows from those workloads are not comparable with these chains. Lean's arithmetic refinements remain in `Tower/Fast.lean`; matching complete chain digests and operation counts establishes the new runtime correspondence with Binius.

### Build provenance

The driver records the source commit and source-content hash (including untracked, nonignored files), toolchain versions, build environment, native CPU features, and hashes of all three executables in `.lake/build/field-bench-build.json`. `--skip-build` rejects missing or mismatched records and asks for a normal run; normal runs use Lake/Cargo’s incremental builds. The run manifest copies that build record instead of inferring binary provenance from the current environment. Sources and executable hashes are checked again after validation and timing. Build flags must also match, including `CARGO_ENCODED_RUSTFLAGS` if set.

### One polynomial at one point

Run `python3 scripts/bench-fields.py --suite poly-eval --cpus 1,2,3,4`. Supply distinct logical CPU IDs available on your machine; the number of workers equals the number of selected CPUs and must be a power of two, at least two. SMT siblings are allowed; the report distinguishes worker count from physical core count. Without `--cpus`, the driver selects up to sixteen logical CPUs (the largest power of two available, capped at sixteen), selecting distinct physical cores before adding SMT siblings. `--suite all` includes this suite after scalar field benchmarks; `--cpu` selects the scalar core and `--cpus` selects the polynomial cores independently. `--validate-only` checks all cross-language/method result digests without collecting timings.

The table compares CompPoly's existing `evalHorner` with the new `evalFast`, and matched Rust implementations. Each invocation evaluates one dense polynomial at one point. It cycles through four deterministic points across invocations, not a batch of points. The three coefficient counts are 4,096, 65,536 and 1,048,576; fields are KoalaBear, Goldilocks, BN254 scalar and the 128-bit Fan–Paar binary tower. These rows use the fast field carriers. No reference-field or FFT timings are included.

`evalFast x p logWorkers` defaults to `logWorkers = 4` (sixteen blocks) and uses up to `2 ^ logWorkers` independent Horner leaves over contiguous coefficient ranges, without copying coefficients. It combines a lower and upper range as `upper * x^lowerLength + lower`; explicit square-and-multiply has the same operation schedule in Rust. Tasks form a dependency tree using `Task.bind`/`Task.map`; only the caller waits. Launching a pure task and then doing sequential work can allow the compiler to delay the launch, so the explicit dependency tree is intentional. `evalFast_eq_evalHorner` proves correctness over any semiring, including empty polynomials and uneven splits. It leaves `eval` and `evalHorner` unchanged.

Input decoding, polynomial construction, runtime pool creation and validation are outside timing. These are steady-state timings after validation/warmup; one-time input-sharing costs are excluded. Task scheduling, powers and joins are inside every timed evaluation. Rust uses a persistent Rayon pool with the same worker count and split tree. Horner is pinned to the first selected CPU; parallel evaluation uses the whole set. For scaling experiments, pass 8 or 16 logical CPU IDs to measure 8 or 16 workers; 16 workers on an 8-core/16-thread machine measures SMT, not 16 physical cores. Results report milliseconds per complete evaluation, median of paired run medians and between-run MAD, plus machine details. Small polynomials may lose to task overhead. Shared-host contention remains visible in the measurements.

The fixture files store four points followed by coefficients in ascending degree order, using fixed-width little-endian coordinates (4/8/32/16 bytes respectively). The deterministic generator uses seed `comppoly-poly-eval-v1:<field>` and nonzero canonical coordinates. Binary coordinates use the same Fan–Paar basis as the scalar suite. Fixture hashes, source/build hashes, CPU affinity and worker counts are recorded in `manifest.json`. `CompPolyEvalBench` reads these inputs; `bench/rust/src/poly_eval.rs` supplies the matched Rust workload; `scripts/bench_poly_eval.py` extends the shared driver.

The parallel prime-field leaves use matching lazy multiply-add kernels in Lean and Rust; `evalHorner` remains the baseline using existing field operations. Import `CompPoly.Univariate.EvalFastFields` to select the proved field-specific `EvalKernel` instances. Goldilocks keeps an arbitrary 64-bit accumulator, KoalaBear maintains a residue below `2p` with one correction per step, and BN254 keeps a residue below `3p < 2^256` without any per-step conditional subtraction. Each leaf normalizes its result before the existing canonical joins. Binary-field leaves are unchanged. Rust uses custom lazy kernels alongside Plonky3/arkworks types and their canonical operations for powers and joins; the parallel column is therefore a matched algorithm comparison, not a stock-library polynomial evaluator. Preparing Rust's raw coefficient and point representations is outside timing. Plonky3's public Montgomery-word deserializer wraps KoalaBear's normalized leaf result without a conversion to and from canonical coordinates.

BN254's Lean leaf carries four `UInt64` accumulator words through a loop indexed by `USize`, constructing a limb object only when the leaf returns. The modulus limbs and Montgomery inverse are parameters of that loop, which is marked `@[noinline]`: on the measured compiler, embedding the modulus constants disrupted recognition of widening multiplication. Keeping them as parameters yields native widening products without changing the four-round Montgomery schedule used by Rust. The scalar loop is proved equal to the original array fold, including clipped/empty ranges; ranges beyond the machine-word index limit retain the original fold.

## KoalaBear NTT against optimized Plonky3

```bash
python3 scripts/bench-fields.py --suite ntt
python3 scripts/bench-fields.py --suite ntt --validate-only
```

This suite measures the proved `NTTFast.NaturalPlan` against Plonky3's `Radix2DFTSmallBatch<KoalaBear>` public `dft`/`idft` API, pinned to `p3-dft` 0.4.2. Rust uses the library's optimized algorithm and native packed arithmetic; there is no custom Rust transform. Six rows cover forward and inverse transforms at 2^12, 2^16 and 2^20 elements, with a default budget of sixteen workers, capped by available logical CPUs. `--cpus` chooses a power-of-two worker allocation; `--cpu` selects a one-worker run. Plonky3's `parallel` feature and native SIMD are enabled. The existing Lean plan is sequential but receives the same CPU allocation. This suite is included in `--suite all` and its CI validation gate.

Both sides consume and return natural-order arrays. Lean's plan internally uses bit-reversed spectra, so its ordering adapter is included in timing. Plonky3's public API includes its own ordering work. Plan construction, twiddle tables and fixture decoding are outside timing; input copying, output disposal and inverse normalization are inside. This compares optimized implementations of the same mathematical transform, allowing different algorithms and arithmetic schedules. It replaces the original matched-schedule scalar Rust baseline.

Fixtures use canonical little-endian 32-bit coordinates: the certified root exported by Lean, followed by two input arrays. Rust verifies that root equals the library's selected root. Every output element contributes to an untimed digest; only four output positions feed the timed sink. Validation covers tiny odd/even log sizes and large transforms. The Rust API contract test uses an independent direct transform to check root direction, ordering and normalization. Reports and build/fixture provenance, including the selected Rust implementation and packing width, are saved under the output directory.

### Lean natural-order NTT plans

Import `CompPoly.Univariate.NTTFast.Natural` and construct `NTTFast.NaturalPlan.ofDomain domain` once, then call `plan.forward input` or `plan.inverse input`. The plan caches bit-reversal indices as well as the existing twiddle tables. Its forward path reuses correctly sized inputs until the first copy-on-write update; shorter inputs are zero-padded and longer ones truncated. Normalization uses a specialized scalar loop. Both operations are proved equal to the existing natural-order pipelines for every input array.

The imported butterfly modules also install proved compiler substitutions for `NTTFast.Plan.forwardImpl` and `inverseImpl`. Array bounds are checked once per radix-four block; the hot loop uses `USize` indices and bounds-proved accesses. The original total functions cover invalid ranges, and natural-number indexing covers ranges exceeding the machine-word limit. No new external functions or compiler changes are used. The NTT benchmark executable targets the native CPU, matching Rust's native targeting; the library retains portable build settings.

The retained Lean implementation is sequential. Experiments with per-stage parallel gathering, recursive task splitting, byte-packed storage, two-lane software arithmetic, and sixteen-element blocks did not close the large-transform gap. The block prototype generated AVX2 instructions, but packing, allocation and sharing costs limited the gain; it is not part of the verified implementation. Plonky3 combines packed arithmetic with cache-local groups of layers and parallel mutable slices. A competitive Lean parallel version needs to address the storage and data-movement costs together with the butterfly schedule.
