# Benchmarking in CompPoly: Audit and Redesign Plan

Status: proposal for review. Nothing in `bench/` has been changed.
Author's note: §4.1 contains a measured result that should be read before
anything else, because it changes how every current benchmark number in this
repo should be interpreted.

## Contents

- [0. Executive summary](#0-executive-summary)
- [1. What exists today](#1-what-exists-today)
- [2. Strengths](#2-strengths)
- [3. Weaknesses](#3-weaknesses)
- [4. Evidence](#4-evidence)
- [5. What the research says](#5-what-the-research-says)
- [6. Proposed architecture](#6-proposed-architecture)
- [7. Implementation plan](#7-implementation-plan)
- [8. Multi-backend track: Lean C backend vs Peregrine](#8-multi-backend-track-lean-c-backend-vs-peregrine)
- [9. Decisions needed from you](#9-decisions-needed-from-you)
- [10. Sources](#10-sources)
- [11. Review of this audit against the code and the run data](#11-review-of-this-audit-against-the-code-and-the-run-data)
- [12. Change log](#12-change-log)

---

## 0. Executive summary

The existing suite is well-engineered in its *plumbing* — 66 registered groups,
deterministic inputs, cross-implementation checksum validation, CLI selection,
JSONL plus Markdown output, CI wiring — and the plumbing should largely survive.
The problem is the measurement itself.

**The headline finding.** `runTimed` folds a bignum `Nat` checksum into the timed
loop on every iteration. I measured that checksum in isolation with a compiled
probe: it costs **~586 ns per call**. A `Goldilocks.Fast` multiplication costs
**~1.6 ns**. The suite therefore reports 619 ns for an operation that takes 1.6 ns,
and reports the fast field as **1.27× faster** than the `ZMod` model when the real
ratio is **~25×**. Details and full numbers in §4.1.

The practical consequence: **the benchmark suite cannot currently observe the
optimisations it exists to guide.** Halving the cost of a field multiplication
moves the reported number by about 0.3%.

Four further structural gaps, in priority order:

1. **No dispersion or repetition.** Each row is one sample of one total; there is
   no median, variance, confidence interval, or outlier signal, so a real
   regression is indistinguishable from a scheduler hiccup (§3.2).
2. **No regression detection at all** for runtime benchmarks. Results go to a
   30-day CI artifact and a step summary; nothing is stored, compared, or alerted
   on. A 30% NTT regression merges silently (§3.5).
3. **Coverage misses the stated targets.** There is no standalone multiplicative
   NTT/iNTT group, no base-field microbenchmarks for KoalaBear/BabyBear/Mersenne31,
   no `add`/`square`/`batch-inverse` anywhere, no Reed–Solomon or polynomial-matrix
   groups, and the additive NTT is measured at 4–128 coefficients when the target
   regime is 2^18–2^24 (§3.7, §3.8).
4. **~150 hand-tuned iteration-count magic numbers** that an adaptive harness
   would compute for free, and which make `Total` incomparable between rows of
   the same table (§3.3).

**The recommendation is a targeted rebuild, not a rewrite.** Keep the group
registry, the generators, the checksum-as-correctness-oracle idea, and the CLI.
Replace the timing core, add a statistics layer, make the sink cheap, seed
per-group, add size sweeps, and hand result storage and regression detection to
[Radar](https://github.com/leanprover/radar) — the Lean FRO's own continuous
benchmarking service, whose bench-script contract CompPoly can satisfy with a
~20-line `bench/run` shell script (§6, §7).

Two things I want to flag as *not* settled. First, the academic literature on
benchmark statistics is overwhelmingly about JIT-based managed runtimes; applying
it to AOT-compiled Lean→C is a defensible precaution, not a sourced result (§5.5).
Second, on your Peregrine suggestion: it is a good idea and I have designed a hook
for it, but the Lean→λ□ frontend currently maps `Nat` literals to **63-bit signed
integers** and emits every `@[extern]` function as an **axiom**, which means
CompPoly's `UInt64`/`Array`-based fast paths and its >2^63 moduli cannot pass
through it today. I recommend building the backend-agnostic hook now and gating
the Peregrine backend itself behind a one-day feasibility spike (§8).
---

## 1. What exists today

### 1.1 The compiled suite (`bench/`, `lake exe CompPolyBench`)

The primary harness is a Lean executable built from `bench/` (~5.8 kLOC across 25
modules) and wired into `lakefile.lean` as `lean_exe CompPolyBench` plus
`lean_lib CompPolyBenchLib`.

Architecture:

- `bench/CompPolyBench/Common.lean` (935 lines) — the whole harness: presets,
  the timing primitive `runTimed`, deterministic input generators, checksums,
  hardware probing, JSONL emission, and a hand-rolled Markdown table renderer.
- `bench/CompPolyBench/Setup.lean` — CLI parsing (`--small/--medium/--large`,
  `--group`, `--groups`, `--list`, `--json-only`, `--markdown-only`) and the
  `allTasks` registry.
- One module per area under `bench/CompPolyBench/{Univariate,Multivariate,
  Multilinear,Bivariate,Fields}/…`, each exporting a `List BenchTask`.

The measurement primitive, `Common.lean:533`:

```lean
def runTimed (…) (warmup measured : Nat) (run : Nat → α) (checksum : α → Nat)
    (checksumIterations : Nat := measured) : IO BenchRecord := do
  for i in [0:warmup] do
    let _ := run i
  -- untimed validation pass
  for i in [0:checksumIterations] do
    validationChecksum := mixChecksum validationChecksum (checksum (run i))
  let start ← IO.monoNanosNow
  for i in [0:measured] do
    timingChecksum := mixChecksum timingChecksum (checksum (run i))
  let stop ← IO.monoNanosNow
  …  -- totalNanos := stop - start; averageNanos := total / measured
```

Registered surface: 66 groups (`--list`), of which 41 run in CI via the
`BENCH_CI_GROUPS` allowlist in `.github/workflows/lean_action_ci.yml`.

### 1.2 CI integration

`lean_action_ci.yml` builds `CompPolyBench`, runs the allowlisted groups at
`--medium` on `ubuntu-latest`, copies `bench/results-*.jsonl` and
`bench/report-*.md` into an artifact (30-day retention), and `cat`s the Markdown
report into `$GITHUB_STEP_SUMMARY`.

### 1.3 A second, separate benchmark path (`tests/`)

Three files measure timings at *elaboration* time via `#eval`:

- `tests/CompPolyTests/Univariate/NTT/Benchmark.lean` — NTT-vs-naive crossover
  sweep over 20 operand sizes, `IO.monoMsNow`.
- `tests/CompPolyTests/Bivariate/KroneckerBenchmark.lean`
- `CommonBench.lean` under `tests/CompPolyTests/Fields/Binary/` (removed in 12.4;
  its correctness guards now live in
  `tests/CompPolyTests/Fields/Binary/Common.lean`)

None is imported by `tests/CompPolyTests.lean`, so none runs under `lake test`
or in CI. Each documents its own manual invocation (`lake build
CompPolyTests.Bivariate.KroneckerBenchmark`).

### 1.4 Build-time measurement (`scripts/build_timing_report.sh`)

430 lines of bash wrapping `lake build` / `lake test`, emitting JSONL and a
Markdown report, with a genuinely sophisticated baseline mechanism: a
`github-script` step walks previous successful workflow runs to find the
merge-base artifact and diffs against it. This is the most mature piece of
performance tooling in the repo — and it measures compile time, not run time.

---

## 2. Strengths

These are real and worth preserving through any refactor.

1. **It is a compiled binary, not `#eval`.** The main suite measures
   natively-compiled code. That is the correct fundamental choice and rules out
   the interpreter overhead that invalidates the `tests/` path.
2. **Cross-implementation checksums.** `BenchGroup` bundles implementations that
   must agree, computes a checksum over a shared iteration prefix, and exits
   nonzero on mismatch. Benchmarking a wrong-but-fast implementation is a classic
   failure mode, and the suite is structurally immune to it. This is better than
   most crypto benchmark suites manage.
3. **Deterministic inputs.** A single fixed `seed` (`20260504`) threaded through
   `StdGen` makes a run reproducible.
4. **Machine-readable output alongside human output.** JSONL rows carry
   `representation`, `method`, `field`, `input_shape`, and iteration counts —
   enough dimensional metadata to support a comparison tool that does not exist
   yet.
5. **Group-level selection with fail-closed CI keys.** `--groups` plus an
   explicit `BENCH_CI_GROUPS` allowlist where an unknown key fails the run, so a
   renamed group is caught rather than silently dropped.
6. **Environment capture.** Reports record CPU model, topology, RAM, and
   hypervisor vendor — an acknowledgement that runner identity matters.
7. **The `ZMod`-vs-fast pairing is the right comparison axis.** Every group that
   pairs the canonical Mathlib-facing model against the native-word
   implementation directly encodes the project's core claim: that the verified
   fast path is worth having.

---

## 3. Weaknesses

### 3.1 The timing loop measures the harness, not the code (critical)

`runTimed` folds a `Nat` checksum into the timed region on every iteration:

```lean
mixChecksum acc value = (acc * 16777619 + value + 97) % 18446744073709551557
```

The modulus exceeds `2^63`, so `acc` is always a GMP-backed bignum and every call
is a heap-allocating multi-precision multiply-and-mod. Measured cost: **~586 ns
per call**, against **~1.6 ns** for the operation it is supposed to be measuring.
Full numbers, method, and the corrected implementation ratios are in
[§4.1](#41-the-timing-loop-costs-more-than-the-operations-measured).

Three consequences worth stating separately:

- Every cheap-operation benchmark reports a near-constant (~590 ns) plus a small
  perturbation. Optimising a field multiplication by 2× moves the reported number
  by ~0.3%, i.e. below noise.
- The bias is **not uniform**, so it distorts comparisons *between* groups as well
  as absolute numbers. It scales with how many checksum calls an iteration makes:
  the additive-NTT groups checksum via a `List.finRange (2^n)` fold *inside* the
  timed loop, where the sink can cost more than the transform being measured.
- The checksum is also the only thing preventing dead-code elimination of the
  benchmark body, but nothing documents it as such — so "make the sink cheaper"
  is a change that can silently delete the benchmark (see §3.10 and §4.2).

### 3.2 No dispersion, no repetition, no confidence

A record is one sample of one total: `averageNanos = totalNanos / measured`
(integer division). There is no median, no standard deviation, no confidence
interval, no outlier detection, and no repeated trial. A single GC pause or
scheduler preemption is indistinguishable from a real regression, and nothing in
the output lets a reader tell the difference.

### 3.3 Iteration counts are ~150 hand-tuned magic numbers

`preset.selectNat 45000 6500 1300`, `selectNat 490000 70000 14000`,
`selectNat 14 2 1` … scattered across every bench module, different per
implementation *within* a group. Consequences:

- `Total (ms)` is not comparable across rows of the same table, because the rows
  ran different iteration counts. Only `Avg` is, and `Avg` is the biased number
  from §3.1.
- Every new benchmark requires a human to guess a count, and every hardware
  change invalidates the guesses.
- The whole mechanism is what an adaptive harness (Criterion-style: run until a
  target measurement time is reached) provides for free.

### 3.4 Input generation is order-coupled

One `StdGen` is threaded sequentially through the selected groups, so a group's
inputs depend on **which groups ran before it**. `bench/README.md` states this
outright: adding or reordering a group changes the inputs — and therefore the
checksums and timings — of every group after it. This means:

- CI's 41-group subset does not measure the same inputs as a full local run.
- Checksums cannot be committed as regression fixtures.
- Bisecting a regression across commits that added a group is unsound.

The fix is small (derive a per-group seed from the group key) and unlocks a lot.

### 3.5 No regression detection for run-time benchmarks

Results are uploaded as a 30-day artifact and pasted into the step summary. There
is no historical store, no baseline comparison, no trend, and no alert — so a 30%
NTT regression merges silently. The irony is that `build_timing_report.sh`
*already* implements merge-base baseline retrieval for build times; run-time
benchmarks get none of it.

### 3.6 Measured on shared cloud runners

`ubuntu-latest` is a 2-vCPU shared VM with a CPU model that varies between runs.
Even with a perfect harness, run-to-run wall-clock on such a runner typically
moves by tens of percent. The report collects `Hypervisor vendor` — the
infrastructure knows it is on a hypervisor, and then compares numbers across
hypervisors anyway.

### 3.7 Coverage does not match the stated optimisation targets

`ROADMAP.md` names fields, NTTs, and coding theory as the performance story.
Against the 66 registered groups:

- **No standalone multiplicative NTT/iNTT group at all.** The forward and
  inverse transforms — the single hottest primitive in the library's intended
  use — are only measured indirectly, through `univariate-mul-*` and
  `univariate-low-product-*`, where the transform's cost is entangled with
  padding, Kronecker packing, and pointwise products.
- **No base-field microbenchmarks for KoalaBear, BabyBear, Mersenne31, or
  Mont32.** Only Goldilocks has `mul`/`inv` groups. The 31-bit fields that the
  library targets most heavily have no direct field-arithmetic measurement.
- **No `add`, `sub`, `square`, `batch inverse`, or `sum-of-products` anywhere** —
  and `square`/`batch-inverse` are exactly where field implementations win.
- **No Reed-Solomon encode or Gao decode group**, despite `Univariate/ReedSolomon/`
  being a named subsystem with a roadmap success criterion.
- **No `LinearAlgebra/PolynomialMatrix/` group**, so the approximant-basis and
  Mulders–Storjohann work landed in #312/#313 is unmeasured.
- **Additive NTT is measured at ℓ = 2, 4, 7** — 4, 16, and 128 input
  coefficients. Production STARK workloads are 2^18–2^24. At n = 4 the
  measurement is dominated by setup and, per §3.1, by the checksum fold; it says
  nothing about cache behaviour, which is what determines large-transform
  performance.

### 3.8 No size sweeps

Almost every group pins one input shape. Where multiple sizes exist
(`bivariate-divlinear-*-y{8,16,32}`, `univariate-batch-{small,medium,large}`)
they are hand-enumerated as separate groups with separately hand-tuned iteration
counts. Nothing reports throughput normalised per element or per butterfly, so
asymptotic behaviour and crossover points are invisible. The only crossover
analysis in the repo is in the orphaned `tests/…/NTT/Benchmark.lean`.

### 3.9 No external yardstick

"As fast as possible" is unfalsifiable without a reference. Nothing compares
against plonky3, arkworks, gnark-crypto, or published cycles-per-operation
figures, and nothing is expressed in a comparable unit (cycles/op, ns/op at a
stated clock).

### 3.10 Smaller defects

- **`jsonString` does not escape** (`Common.lean:577`): `"\"" ++ s ++ "\""`. It
  works today only because no label contains a quote or backslash.
- **Hardware probing is Linux-only** — `lscpu`, `/proc/meminfo`, `nproc`,
  `df --output`. On macOS (the primary dev platform here) reports read
  `- Runner: unavailable outside GitHub Actions` with no CPU information at all.
- **DCE/laziness is not addressed as a stated invariant.** It happens to be
  defeated by the checksum, but nothing documents that as the reason, so removing
  the checksum for performance would silently delete the benchmark bodies. I hit
  exactly this while writing the probe above: a `let r := f ()` before reading the
  clock left the entire 2M-iteration loop outside the timed region, reporting
  0.00002 ns/iter.
- **935-line `Common.lean` mixes five concerns** (timing, generation, checksums,
  environment, reporting), and ~500 lines of it are a hand-rolled Markdown table
  renderer and a hand-maintained `implementationNameLabels` /
  `implementationMethodLabels` lookup table (~90 string pairs) that must be
  edited whenever a benchmark is added.
- **Report clutter**: 16 timestamped `report-*.md` / `results-*.jsonl` files
  accumulate in `bench/` (gitignored, including a stale `evaluation-*` generation
  from May 2026).
- **No `docs/wiki/benchmarking.md`**, despite `AGENTS.md` requiring recurring
  repo guidance to be promoted to the wiki. Benchmarking guidance lives only in
  `bench/README.md`.
---

## 4. Evidence

Both measurements below were made on this machine (darwin/arm64, Lean 4.33.1) by
adding a temporary `lean_exe` to `lakefile.lean`, building it natively with
`lake build`, running it, and then reverting the scaffolding. The working tree is
unchanged.

### 4.1 The timing loop costs more than the operations measured

Loop bodies, 2,000,000 iterations each, two runs agreeing to within ~2%:

| Loop body | ns/iter |
|---|---:|
| `mixChecksum` alone, no field operation | 586 |
| `Goldilocks.Fast` mul + `mixChecksum` — what `runTimed` does | 606 |
| `Goldilocks.Fast` mul + `UInt64` xor sink | 3.60 |
| `UInt64` xor sink alone (array index + unbox baseline) | 1.96 |
| `Goldilocks` `ZMod` mul + `mixChecksum` | 678 |
| `Goldilocks` `ZMod` mul + `UInt64` xor sink | 78.9 |
| `ZMod` xor sink alone | 38.0 |

Subtracting the sink-only baselines:

| Operation | True cost | Suite reports | Inflation |
|---|---:|---:|---:|
| `Goldilocks.Fast` mul | **1.64 ns** | 619 ns | **~380×** |
| `Goldilocks` `ZMod` mul | **40.9 ns** | 788 ns | **~19×** |

And therefore, for the comparison the group exists to make:

| | `ZMod` : `Fast` speedup |
|---|---:|
| What `fields-goldilocks-mul` reports | **1.27×** |
| What is actually true | **~25×** |

The verbatim report from `./.lake/build/bin/CompPolyBench --small --markdown-only
fields-goldilocks-mul`:

```
| Implementation           | Iterations | Total (ms) | Avg (ns) |
| ------------------------ | ---------: | ---------: | -------: |
| Naive (Goldilocks.Field) |       6000 |       4.73 |      788 |
| Naive (fast Goldilocks)  |       6000 |       3.72 |      619 |
```

Note also that `ZMod`'s own sink is expensive (38 ns) because Goldilocks exceeds
`2^63`, so `ZMod.val` yields a bignum `Nat`. Any redesigned sink must be measured
per representation, not assumed cheap.

### 4.2 Dead-code elimination is a live hazard, not a theoretical one

While writing the probe I wrote the obvious thing:

```lean
let start ← IO.monoNanosNow
let r := f ()          -- f : Unit → Nat, a 2M-iteration loop
let stop ← IO.monoNanosNow
```

This reported **0.000021 ns/iter** — the entire loop was evaluated *outside* the
timed region. Forcing `r` before reading the clock (`if r % 2 == 7 then …`) gave
the real numbers in §4.1.

This matters for the redesign because it means a Lean benchmark harness needs an
explicit, documented forcing discipline, and needs a self-check that would *fail*
if the discipline broke. A benchmark that silently measures nothing looks exactly
like a benchmark that got very fast. Recommendation in §6.2.
---

## 5. What the research says

I ran a fan-out research pass (26 sources fetched, 129 claims extracted, each
surviving claim put to a 3-voter adversarial verification where 2 of 3 refutations
kill it; 16 confirmed, 9 killed). Findings below are labelled with what actually
verified. **Read §5.6 for what did not.**

### 5.1 The Lean ecosystem already has continuous benchmarking: Radar

This is the most actionable finding in the whole document, and it is the one I
would act on first after fixing the timing core.

[`leanprover/radar`](https://github.com/leanprover/radar) ("Do you know how fast
you were going?", hosted at `radar.lean-lang.org`) is the Lean FRO's continuous
benchmarking service — a server plus **runners that live on dedicated machines**,
explicitly so that "interference by other processes" is not a problem. It is the
successor to [`leanprover/velcom`](https://github.com/leanprover/velcom), and
`radar-bench-lean4`, `radar-bench-mathlib4`, `radar-bench-cslib` and
`radar-bench-verso` are live consumers.

Its integration contract is a good fit for CompPoly, and cheap:

- A **bench script** is any executable. It receives the repo clone path and an
  output path, plus `RADAR_REPO`, `RADAR_BENCH_REPO`, `RADAR_OUT`, `RADAR_CACHE`
  (a cache directory preserved between runs — useful for `.lake`).
- Measurements are submitted either as **JSON Lines** in the output file, or by
  printing lines containing `radar::measurement=` followed by JSON. Each record is
  `{"metric": "<name>", "value": <float>, "unit": "<string>"}`.
- Units with special support: `s`, `B`, `%`, `100%`. Metric names are conventionally
  `Hierarchical/Path//Submetric`.
- The server queues new main-branch commits, stores history, serves a web UI, and
  a **GitHub bot answers `!bench` / `!radar` in PR comments** with results for the
  PR head.

And [`radar-bench-generic`](https://github.com/leanprover/radar-bench-generic) is
a ready-made adaptor that looks for a benchmark suite at *well-known locations* —
`bench`, `bench/run`, `scripts/bench/run`, `tests/bench/run` — sets `IN_RADAR=1`,
and collects `measurements.jsonl` or `radar.jsonl`.

**So CompPoly can join Lean-hosted continuous benchmarking by adding an executable
`bench/run` that shells out to `lake exe CompPolyBench` and emits
`measurements.jsonl`.** That single change buys dedicated-runner measurement,
historical storage, a web UI, and PR-comment benchmarking — every one of which
CompPoly currently lacks (§3.5, §3.6). It also removes the temptation to build a
regression-detection engine in-repo.

One caveat from the spec that will bite if missed: **when a metric is measured
multiple times, radar sums the values.** Emitting the same metric name per
iteration would silently accumulate. One record per metric per run.

*Confidence: high — read directly from the repositories' README and bench scripts
rather than from secondary documentation.*

### 5.2 Lean's own micro/cross benchmarks delegate measurement, and Mathlib reports instructions

Two ecosystem precedents, both verified:

- **`lean4/tests/bench` does not hand-roll a timing harness.** It has two suites
  built on the external [temci](https://github.com/parttimenerd/temci) tool — a
  lightweight "Speedcenter" suite and a heavyweight "Cross" suite comparing Lean
  against other functional compilers (built for the *Counting Immutable Beans*
  paper). The precedent is: *outsource measurement statistics rather than
  reimplementing them.* Caveats: both suites measure whole-program workloads, not
  per-operation microbenchmarks; temci is at 0.8.5 with substantive commits around
  2022 and a maintainer who says the project "has sadly fallen off my radar"; and
  its noise-reduction plugins are Linux-and-root-only, so unusable on darwin.
  I would take temci's *checklist* (below) and not its code.
- **Mathlib reports most benchmark results in CPU instruction counts, not
  wall-clock**, because "the number of instructions is more stable on the
  benchmarking servers than the wall-clock time which is affected by process
  scheduling" (*Growing Mathlib*, arXiv:2508.21593, by Mathlib maintainers).
  Corroborated on Zulip by Sebastian Ullrich: "Instructions is the most robust
  time-like measurement, which is why it's the only metric we use for individual
  files."

Two important qualifications on the instruction-count precedent, both of which
came out of the adversarial pass:

1. Mathlib measures **elaboration cost of Lean source**, not runtime of compiled
   executables. The *metric choice* transfers; the harness does not.
2. **Cross-machine comparability of instruction counts was explicitly refuted.**
   The defensible justification is within-machine stability under scheduling
   noise — not machine independence. Do not sell it as the latter.

And instruction counts ignore cache and memory-hierarchy effects, which is exactly
what governs large-NTT performance. Hence the two-track split in §6.5:
**instructions gate CI; wall-clock and cycles back absolute claims.**

### 5.3 Harness statistics: what verified and is worth copying

- **Geometric warmup ramp** (Criterion.rs): run the routine once, twice, four
  times… until accumulated time exceeds a warmup budget (default 3 s). This both
  warms caches/branch predictors/CPU frequency *and* yields the per-iteration cost
  estimate used to size later samples — which is precisely what would replace
  CompPoly's ~150 hand-tuned iteration counts (§3.3). Note honestly that
  Criterion's JIT-warmup rationale does not transfer to AOT Lean; the
  cache/frequency and cost-estimation rationales do.
- **Tukey outlier classification that labels rather than trims**: fences at
  1.5×IQR (mild) and 3×IQR (severe) off the 25th/75th percentiles, with outliers
  **kept in the analysis** and a warning printed as a data-quality signal.
- **Effect-size confidence intervals instead of p-values.** Kalibera & Jones:
  with large samples "the decision will nearly always be it is likely that the
  systems do not have the same performance, no matter how small or large the
  difference actually is. The method then becomes of very little use — it just
  adds an illusion of rigour." Their replacement is a CI on the **ratio of mean
  execution times**, judged against a practical-importance threshold: with a 3%
  threshold, declare a change only if the CI upper bound < 0.97 or lower bound
  > 1.03, reported as "A is 4%±1.5% faster than B, with 95% confidence". This is
  the right shape for a CompPoly regression gate.
- **Single-number reporting can invert rankings.** Georges et al. (OOPSLA 2007,
  Most Influential Paper) found single-number methods misleading in up to 16% of
  pairwise startup comparisons, and producing the *opposite* conclusion to the
  rigorous verdict in >3%. Quote the 16% carefully: it is a maximum over
  methods/configurations on 2007 JVMs, not a figure transferable to Lean→C.
- **Do not assume a steady state after a fixed warmup — test for it.** Georges
  et al. detect steady state via the coefficient of variation of the last *k*
  iterations dropping below ~0.01–0.02, then compute the CI **across process
  invocations** (because iterations within one invocation are not independent).
  Barrett et al. (*Virtual Machine Warmup Blows Hot and Cold*, OOPSLA 2017) then
  showed the underlying "discard warmup, report peak" assumption is frequently
  false — "at most 43.5% of ⟨VM, benchmark⟩ pairs consistently reach a steady
  state of peak performance" — and proposed PELT changepoint detection over
  per-iteration timings instead of hand-tuned warmup thresholds.
- **Instruction-count harnesses run each benchmark exactly once**, since
  instruction counting needs no repetition to filter timing noise
  (iai-callgrind, now [gungraun](https://github.com/gungraun/gungraun)). Their own
  authors disclaim it as a wall-clock replacement: the cycle estimate "merely
  correlates to wall-clock times". Valgrind on macOS is x86_64-only, so this track
  is CI-Linux-only for this repo.

### 5.4 The environment checklist worth stealing from temci

temci's `usable` preset enumerates the OS-level controls that matter, and claims
to cover LLVM's benchmarking guidance: `cpu_governor` (performance),
`disable_swap`, `sync`, `nice` (default −15), `disable_aslr`, `disable_ht`,
`cpuset`, `disable_intel_turbo` (because "the CPUs cannot overclock partially").
The `all` preset additionally `SIGSTOP`s non-vital processes and renices
competitors. All plugin actions are documented as reversible.

Peregrine's own Lean benchmark suite independently arrives at a subset of the same
list: Linux booted with `isolcpus`, `taskset -c 3` to pin the benchmark to an
isolated core, and [hyperfine](https://github.com/sharkdp/hyperfine) as the
timing driver — while noting that further CPU tuning "were found to not further
reduce noise on the hardware tested".

For CompPoly the actionable version is: **this is the runner's job, not the Lean
binary's.** Radar's dedicated runners are where these controls belong.

### 5.5 What did NOT verify — read before relying on anything above

The adversarial pass killed nine claims. Four are worth knowing as design traps:

1. **Cross-machine comparability of instruction counts** — refuted (see §5.2).
2. **Criterion's regression-slope / bootstrap-hypothesis-test pipeline** —
   refuted. A harness copying "Criterion methodology" should copy the warmup ramp
   and Tukey labelling that *did* verify, not a regression/bootstrap pipeline.
3. **Mathlib's "5% threshold Zulip bot" and VelCom hosting** — not established by
   this pass. It may well be true, but do not cite it without re-sourcing.
4. **"Keep running until the CI is within 1–2% of the mean, capped at 30 runs"**
   as a Georges et al. prescription — refuted; they do not prescribe that.

Two further honesty notes:

- **Every statistical result cited in §5.3 was established on JIT-based managed
  runtimes** with adaptive recompilation and managed-heap GC. Barrett et al. never
  even warmup-classified their C baseline. Lean's AOT C output has different
  non-stationarity sources — reference counting, its own allocator, page faults,
  CPU frequency and cache state. Applying these protocols to CompPoly is a
  defensible precaution presented as extrapolation, **not a sourced finding.**
- **The research pass returned nothing on two angles I asked for**, and the
  session's web-search budget was exhausted before I could cover them myself:
  - **zk/finite-field benchmark methodology and published cycle baselines** —
    arkworks, plonky3, gnark-crypto, blst, zkalc, ZPrize. Zero surviving claims.
    **I therefore quote no cycle-count baselines in this document.** §6.6 specifies
    how to obtain a yardstick by measurement instead of by citation.
  - **Lean-4-specific measurement hazards** — refcount traffic, `UInt64`/`USize`
    boxing, `@[inline]`/`@[specialize]` effects, allocator/GC noise, black-box
    patterns, `perf`/Instruments/valgrind over Lean-generated C. Zero surviving
    claims. This is the single most decision-relevant gap, which is why §4
    measures the two hazards that matter most directly rather than citing anyone.
---

## 6. Proposed architecture

Design goal, stated so it can be checked: **a 5% improvement to a
`KoalaBear.Fast` multiplication should be visible in the suite's output, and a 5%
regression should fail CI.** Neither is true today. Everything below is chosen to
make that sentence true and nothing more elaborate.

### 6.1 Layering

Split the 935-line `Common.lean` into five modules with one concern each. The
group registry, the `BenchTask`/`BenchGroup` shape, and the CLI stay essentially
as they are — they work.

```
bench/CompPolyBench/
  Harness/Timer.lean      -- sink, forcing discipline, one timed sample
  Harness/Sample.lean     -- warmup ramp, adaptive sizing, sample collection
  Harness/Stats.lean      -- median/MAD/CI, Tukey labels, ratio CI vs baseline
  Harness/Sink.lean       -- `Sink α` class: cheap α → UInt64 digest
  Harness/Emit.lean       -- radar JSONL + human Markdown
  Workloads/…             -- generators, per-group seeding
  Registry.lean           -- groups (was Setup.lean)
```

### 6.2 Timing core: cheap sink + explicit forcing + a canary

Three changes, all small, that together fix §3.1 and §3.10.

**(a) Replace the bignum checksum in the timed loop with a `UInt64` sink.**
Correctness validation already happens in a *separate, untimed* pass — that pass
should keep the strong `Nat` digest. The timed loop only needs a
dead-code barrier:

```lean
/-- Cheap, allocation-free digest of a benchmark result, used only as a
dead-code-elimination barrier inside the timed loop. Correctness is checked by
the untimed validation pass, which keeps the strong `Nat` digest. -/
class Sink (α : Type _) where
  toU64 : α → UInt64

@[noinline] def sinkStep (acc x : UInt64) : UInt64 :=
  (acc ^^^ x) * 0x9E3779B97F4A7C15 |>.rotateLeft 27
```

Measured cost of this shape: **~1.9 ns/iter including the array index**, versus
586 ns for `mixChecksum` (§4.1).

For aggregate results (arrays, `Fin n → α`) the sink must not walk the whole
structure inside the timed loop — that is the additive-NTT bug in §3.1. Sink a
**fixed-size sample** of the output (say elements `0`, `n/3`, `2n/3`, `n-1`) and
leave full-structure digesting to the validation pass.

**(b) Make forcing explicit and documented.** §4.2 shows a bare `let` can hoist
the entire loop out of the timed region. The harness should have exactly one place
that reads the clock, and it should force inside:

```lean
@[inline] def timeOne (iters : Nat) (body : Nat → UInt64 → UInt64) :
    IO (Nat × UInt64) := do
  let start ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for i in [0:iters] do
    acc := body i acc          -- `body` folds the result into `acc`
  let forced := acc            -- consumed below, before the clock is read again
  let stop ← IO.monoNanosNow
  pure (stop - start, forced)
```

The `body : Nat → UInt64 → UInt64` signature is the important part: it makes it
*type-impossible* to write a benchmark whose result is unused.

**(c) Add a canary and a loop-overhead floor.** Two synthetic groups that ship
with the harness:

- `harness/empty` — an empty body. Its measured time is the loop-overhead floor.
  Emit it as a metric every run, and **report every other benchmark's cost both
  raw and floor-subtracted**. This is what turns 3.60 ns into the honest 1.64 ns.
- `harness/canary` — a body with a known, deliberately non-eliminable cost. If it
  measures below a hard-coded threshold, **fail the run**: something has started
  optimising benchmark bodies away. This is the self-check §4.2 argues for.

### 6.3 Sampling and statistics

Replace the ~150 magic iteration counts (§3.3) with a two-stage adaptive scheme,
per benchmark:

1. **Warmup / calibration.** Geometric ramp (1, 2, 4, 8, … iterations) until
   accumulated time exceeds a warmup budget (default ~200 ms locally, ~50 ms in
   CI). Take the per-iteration cost estimate from the last ramp step.
2. **Sizing.** Choose `itersPerSample` so one sample takes a target duration
   (~1 ms is a good default: long enough to dwarf the ~30 ns clock overhead,
   short enough that many samples fit a budget).
3. **Collection.** Collect a fixed `sampleCount` (default 50; 20 in CI) samples.
   Fixed, not significance-triggered: optional stopping on significance inflates
   false positives, which is why I am *not* copying temci's early-stop rule (§5.3).

Report per benchmark: `median`, `mean`, `stddev`, `min`, `p95`, `MAD`,
`itersPerSample`, `sampleCount`, and Tukey mild/severe outlier counts — outliers
**labelled, not dropped**. Use **median** as the headline number.

Two independence points worth building in from the start:

- Samples within one process are not independent (allocator state, page tables,
  CPU frequency). Support `--processes k`: the driver invokes the binary *k* times
  and aggregates across invocations, with the CI computed **across per-invocation
  medians**. This is the Georges et al. structure adapted to AOT, and it is the
  only way to get an honest interval.
- Do not implement changepoint steady-state detection yet. It is data-hungry, not
  parameter-free, and its evidence base is JIT VMs (§5.5). Instead emit the raw
  per-sample vector into the JSONL so the question *"does AOT Lean even need it?"*
  can be answered offline from real data later. That is a cheap option to keep open.

### 6.4 Per-group seeding

Fix the order-coupling in §3.4 by deriving each group's generator from its key:

```lean
def genFor (groupKey : String) : StdGen :=
  mkStdGen (mixSeed seed (hashString groupKey))
```

Consequences, all of them wins: CI's subset measures the same inputs as a full
local run; adding a group perturbs nothing else; and **correctness digests become
committable fixtures**, so the validation pass turns into a real regression test
rather than an intra-run cross-check. That last point is what makes the multi-backend
work in §8 possible at all.

### 6.5 Two metric tracks

| Track | Metric | Where | Purpose |
|---|---|---|---|
| **Gate** | instructions/op | Radar Linux runner, `valgrind --tool=callgrind` over the benchmark binary | CI regression detection — stable under scheduling noise |
| **Claim** | ns/op, cycles/op | Radar dedicated runner, wall-clock | Absolute performance, size sweeps, external comparison |

Both tracks emit into the same radar JSONL. Rationale and the explicit caveat that
instruction counts are *not* cross-machine comparable are in §5.2. Wall-clock stays
the source of truth for anything cache-sensitive, i.e. every large NTT.

### 6.6 Coverage: close the gaps in §3.7 and §3.8

Restructure workloads as an explicit **operation × representation × size** matrix
rather than 66 hand-named groups, so a sweep is a parameter and not a copy-paste.

Priority additions, in the order I would add them:

1. **Base-field microbenchmarks** for every field with a `Fast` path —
   KoalaBear, BabyBear, Mersenne31, Goldilocks, Mont32, Mont64x8, binary towers —
   over `add`, `sub`, `mul`, `square`, `inv`, `batchInverse`, `sumOfProducts`.
   This is the layer everything else is built on and it is almost entirely
   unmeasured today.
2. **Standalone forward/inverse multiplicative NTT** over `log n = 8 … 22`,
   reported as ns per butterfly (`t / (n/2 · log n)`) so the size sweep is
   readable and cache cliffs show up as a curve rather than a number.
3. **Additive NTT at production sizes** — extend from ℓ = 2/4/7 to ℓ up to 20,
   subject to a wall-clock budget per preset.
4. **Reed–Solomon encode and Gao decode**, and the
   `LinearAlgebra/PolynomialMatrix` approximant/Mulders–Storjohann layer, neither
   of which has any group.
5. **Crossover reporting.** Fold the orphaned `tests/…/NTT/Benchmark.lean` sweep
   into the suite and emit the naive/NTT crossover degree as its own metric — it is
   a genuinely useful number to track over time, and it is currently measured by a
   file nothing runs.

Then **delete the three orphaned `#eval` benchmarks in `tests/`** (§1.3). They
measure interpreted elaboration-time code, nothing runs them, and keeping a second
methodologically-broken benchmark path invites someone to trust it.

**External yardstick (§3.9).** Since no published cycle baselines survived
verification (§5.5), do not cite numbers — *measure* them. Add
`bench/external/` holding a small Rust project pinning `plonky3` (and
optionally `arkworks`/`gnark-crypto`) with `cargo bench` over the *same*
operations at the *same* sizes, run on the *same* runner, emitted into the *same*
radar metrics under a `reference/` prefix. Then "CompPoly's KoalaBear mul is 3.2×
plonky3's" is a measured claim on identical hardware rather than a comparison
across two papers' machines. This is also the only honest way to state a
roadmap success criterion like "competitive performance with industry-standard
implementations".

### 6.7 Reporting and storage

- **Canonical output: radar JSONL** (§5.1), one record per metric per run, with
  metric names like `fields/koalabear/mul//ns_per_op`. Keep the richer per-sample
  vector in a sidecar file for offline analysis.
- **Keep the Markdown report** for humans and the CI step summary, but generate it
  from the structured records. Retire the ~90-entry
  `implementationNameLabels`/`implementationMethodLabels` lookup tables (§3.10) by
  putting the display label in the group definition where the benchmark is
  declared.
- **Fix `jsonString` to escape** (§3.10) — or emit via `Lean.Json`, which is
  already imported.
- **Make hardware probing cross-platform** — add `sysctl -n machdep.cpu.brand_string`,
  `hw.ncpu`, `hw.memsize` fallbacks so local darwin runs are not blank (§3.10).
- **Write to a single `bench/out/` directory** (gitignored) instead of accumulating
  timestamped files in `bench/`, and delete the stale `evaluation-*` generation.
- **Add `docs/wiki/benchmarking.md`** and link it from the wiki hub, per the
  `AGENTS.md` requirement that recurring repo guidance live in the wiki (§3.10).
---

## 7. Implementation plan

Ordered so that each phase is independently valuable and the highest-value,
lowest-risk work lands first. Estimates are rough and assume familiarity with the
existing `bench/` code.

### Phase 0 — Stop the bleeding (½ day, do this regardless)

The cheapest change with the largest effect on the numbers' meaning.

1. Swap `mixChecksum` for a `UInt64` sink **inside the timed loop only**; keep the
   `Nat` digest in the untimed validation pass (§6.2a).
2. Fix the aggregate sinks that fold over `List.finRange (2^n)` inside the timed
   loop to sample a fixed number of output positions instead.
3. Add `harness/empty` and report floor-subtracted cost (§6.2c).

**Do not skip step 3.** Steps 1–2 will make every number in the suite drop by
roughly two orders of magnitude, and the first question anyone asks will be
"is the benchmark still doing anything?". The canary and floor answer it.

Expected outcome: `fields-goldilocks-mul` reports ~1.6 ns and ~41 ns instead of
619 ns and 788 ns, and the group's speedup goes from 1.27× to ~25×.

### Phase 1 — Statistics and adaptive sizing (2–3 days)

1. The new Harness/Sample module: geometric warmup ramp, adaptive `itersPerSample`, fixed
   sample count (§6.3).
2. The new Harness/Stats module: median, mean, stddev, MAD, min, p95, Tukey mild/severe
   labels.
3. Delete the ~150 `selectNat` magic numbers; presets become
   *(warmup budget, sample count, size cap)* triples rather than per-benchmark
   iteration counts.
4. Emit the per-sample vector into the JSONL sidecar.
5. Add `--processes k` and aggregate across per-invocation medians.

This is where the "5% change is visible" goal is actually met, and it deletes more
code than it adds.

### Phase 2 — Radar integration and regression gating (1–2 days)

1. Add an executable `bench/run` matching the `radar-bench-generic` contract:
   builds `CompPolyBench`, runs it, writes `measurements.jsonl` (§5.1). Honour
   `IN_RADAR`, use `RADAR_CACHE` for `.lake`.
2. Emit radar-format metric records with stable hierarchical names. One record per
   metric per run — **radar sums repeats** (§5.1).
3. Ask the Lean FRO to register the repo with Radar and provision a runner. This
   is the request that unlocks dedicated-hardware measurement, history, the web
   UI, and `!bench` on PRs.
4. Implement the ratio-CI gate (§5.3): compare against the merge-base baseline,
   declare a regression only when the 95% CI on the ratio clears a practical
   threshold (start at 5%, tighten later). `scripts/build_timing_report.sh`
   already contains the merge-base-artifact retrieval logic to crib from if Radar
   provisioning takes time.

Fallback if Radar registration is slow: the same JSONL plus the existing
merge-base artifact machinery gives a self-hosted version of the gate, on noisy
runners. Worth doing as a stopgap, not as the destination.

### Phase 3 — Determinism and correctness fixtures (1 day)

1. Per-group seeding from the group key (§6.4).
2. Commit the validation digests as fixtures; the validation pass becomes a
   regression test that fails on a wrong answer, not just on intra-run
   disagreement.
3. Update `bench/README.md` to drop the "checksums are not comparable across runs"
   caveat, which per-group seeding removes.

### Phase 4 — Coverage (3–5 days, incremental)

Work the §6.6 priority list. Each item is independent, so this can land
group-by-group. I would do base-field microbenchmarks and the standalone NTT
sweep first — they are the two biggest holes relative to the stated goals.

Also in this phase: delete the three orphaned `tests/` `#eval` benchmarks, and add
`docs/wiki/benchmarking.md`.

### Phase 5 — Instruction-count track (2 days, Linux/CI only)

1. A second bench script that runs the binary under
   `valgrind --tool=callgrind` in one-shot mode and emits `instructions/op`.
2. Gate CI on instructions; keep wall-clock for absolute claims (§6.5).
3. Note the platform limit up front: Valgrind on macOS is x86_64-only, so this
   track never runs on the darwin dev machine.

### Phase 6 — External yardstick (2–3 days)

`bench/external/` with pinned `plonky3` (± `arkworks`) benchmarks over matching
operations and sizes, on the same runner, into `reference/` metrics (§6.6).

### Phase 7 — Multi-backend differential track

See §8. Gated behind a feasibility spike; do not schedule until that spike
reports.

### Cross-cutting: what to preserve

Worth writing down so a refactor does not throw it away: the group registry and
`BenchTask` shape, the CLI surface, the `ZMod`-vs-`Fast` pairing as the primary
comparison axis, the checksum-as-correctness-oracle idea, the fail-closed
`BENCH_CI_GROUPS` key checking, and the JSONL-plus-Markdown dual output. All of
that is good and none of it is what is broken.
---

## 8. Multi-backend track: Lean C backend vs Peregrine

You asked for a comparison of the stock Lean backend against Peregrine, valuing it
for **correctness as well as performance**. I think the correctness half is the
stronger argument of the two, and I have designed the hook for it — but the
Peregrine path itself has concrete blockers that should be tested before it is
scheduled.

### 8.1 What Peregrine actually is

[Peregrine](https://github.com/peregrine-project/peregrine-tool) is "a unified
middle-end for code generation from proof assistants". It takes **Agda, Lean, or
Rocq** frontends into the untyped λ□ (LambdaBox) intermediate language, and emits
**C, Rust, WebAssembly, OCaml, CakeML, or Elm**. The middle-end is verified in
Rocq; per its README, "some of the frontends and backends are".

The Lean frontend is
[`peregrine-project/lean-to-lambdabox`](https://github.com/peregrine-project/lean-to-lambdabox),
which adds an `#erase` command performing type and proof erasure from Lean's
`Expr`:

```lean
#erase val_at_false to "out.ast"
```

The `.ast` is then converted to Malfunction by the `peregrine` tool, compiled to
`.cmx`, and linked with `ocamlopt` — the same route as Rocq's verified extraction
pipeline.

So this is not a faster Lean code generator competing on raw throughput. It is an
**independent, largely verified code-generation path**. That is exactly why it is
interesting here.

### 8.2 Why the correctness payoff is the real prize

`AGENTS.md` forbids `native_decide` so that no *proof* depends on
`Lean.ofReduceBool` — the compiler is outside the trusted base. But the benchmark
suite runs compiled code, and CompPoly's whole value proposition is "verified
*and* fast". A miscompilation in the fast path would produce a result that is
wrong but passes every kernel-checked proof, because the proofs are about the Lean
definitions and the benchmark measures the emitted C.

Running the same source through two independent backends and requiring **identical
correctness digests** is direct evidence against that class of failure. It is
evidence, not proof — agreement could still hide a shared frontend bug, and the
Lean erasure frontend is not itself fully verified — but it is the cheapest
available check on the one link in the chain that the TCB policy deliberately
cannot cover.

That reframes the priority: **build the backend-agnostic hook now** (it is nearly
free and useful on its own), and treat the Peregrine backend as a spike.

### 8.3 The hook to build now (Phase 3, ~½ day on top of per-group seeding)

Two things, both of which are worth having even if Peregrine never lands:

1. **Make correctness digests backend-independent committed fixtures.** This falls
   out of per-group seeding (§6.4): once a group's inputs no longer depend on run
   order, its digest is a stable constant that can live in a JSON fixture file. Any
   executable, however built, either reproduces the fixture or fails.
2. **Add `backend` as a dimension of the metric namespace**, e.g.
   `fields/koalabear/mul//ns_per_op` tagged with `backend=lean-c` or
   `backend=peregrine-ocaml`. Radar's flat metric names accommodate this by
   convention; nothing in the harness needs to know how many backends exist.

The same hook also serves comparisons you are more likely to want sooner: different
Lean versions, `-O2` vs `-O3` on the C output, or LLVM bitcode output (`lean --bc`)
versus the C path.

### 8.4 The blockers, from reading the frontend source

I read the frontend's LeanToLambdaBox/Erasure.lean. Three concrete gates, in descending
severity:

1. **`Nat` literals are erased to a 63-bit signed λ□ primitive (`i63`)**, with an
   outright `panic! "Nat literal not representable as a 63-bit signed integer."`
   Consequences for CompPoly:
   - **Goldilocks (2^64 − 2^32 + 1), BN254, BLS12-381, BLS12-377 and the
     `Mont64x8` fields are immediately out** — their moduli exceed 2^63.
   - **KoalaBear, BabyBear and Mersenne31 are in** — all are just under 2^31 and
     fit comfortably.
   - The current `mixChecksum` modulus (18446744073709551557) also exceeds 2^63,
     which is a second reason to replace it (§6.2).
2. **`@[extern]` constants are emitted as axioms** (`Config.Extern.preferAxiom`),
   left for the backend to supply. In Lean, `UInt64`/`USize` arithmetic, `Array`
   primitives and `Nat` arithmetic are all `@[extern]`. So CompPoly's entire
   `Fast` layer — which is *precisely* the code worth benchmarking — becomes a
   wall of axioms unless the OCaml/Malfunction backend implements them. Their own
   benchmark suite exercises `Nat`, `List`, `RBMap`, `binarytrees`, `qsort`,
   `unionfind` (the *Counting Immutable Beans* workloads) — **no `UInt64` or
   `Array`-heavy numeric kernels at all**, so this is untested territory rather
   than known-broken.
3. **Toolchain gap.** `lean-to-lambdabox` pins `leanprover/lean4:v4.22.0`;
   CompPoly is on `v4.33.1` and uses the new module system (`module`,
   `public import`, module privacy). Erasure operating over `Expr` is probably
   robust to that, but it is untested and CompPoly is a large Mathlib-dependent
   library, not a self-contained benchmark file.

### 8.5 Proposed spike (1 day, before scheduling anything)

Answer the feasibility question cheaply, in this order — stop at the first failure:

1. Can `lean-to-lambdabox` be built against CompPoly's toolchain at all, or does
   it need a v4.22 shim project?
2. `#erase` the smallest genuinely-CompPoly definition that stays within i63 and
   avoids `@[extern]`: a `KoalaBear` or `Mersenne31` **canonical `ZMod`-model**
   arithmetic operation (values < 2^31, `Fin p` over `Nat`). Does it erase?
3. Does the resulting λ□ compile through `peregrine ocaml` → Malfunction →
   `ocamlopt` and run?
4. Does it produce the same digest as the Lean-C build?
5. Only then: what happens to an `Array`-based kernel (a small NTT), and how many
   axioms does the backend leave unimplemented?

Deliverable: a one-page note with a go/no-go and, if no-go, the specific missing
primitive support — which is useful upstream feedback to the Peregrine project
regardless.

### 8.6 What to expect on the performance side

Two predictions, stated so they can be checked rather than assumed:

- On the workloads that *do* pass, Peregrine's OCaml path will likely be **slower**
  than Lean's C backend for numeric kernels, because Lean's `UInt64`/`Array`
  primitives are hand-written C and OCaml's boxed-int and array semantics differ.
  A slower verified path is still a useful data point — it quantifies the cost of
  the extra assurance.
- Peregrine's own suite compares `via_lean` against several `malfunction-*`
  configurations using [hyperfine](https://github.com/sharkdp/hyperfine) under
  `isolcpus`/`taskset` CPU isolation. If the spike goes well, **reuse their
  harness shape for the backend comparison** rather than pushing the Peregrine
  path through CompPoly's in-process timer — whole-program timing is the right
  granularity for a backend comparison, and it sidesteps the question of whether
  `IO.monoNanosNow` even exists on that path.
---

## 9. Decisions needed from you

1. **Phase 0 now, separately?** It is half a day, it is confined to
   `runTimed` and the aggregate sinks, and it changes every published number in
   the repo by up to two orders of magnitude. I would land it as its own PR with
   the before/after table from §4.1 in the description, so the discontinuity in
   the history is explained rather than mysterious.
2. **Radar, or self-hosted?** Radar gives dedicated runners, history, a web UI and
   `!bench` on PRs for roughly a day of integration work, but it means asking the
   Lean FRO to register the repo and provision a runner. Self-hosting on top of
   the existing merge-base artifact machinery avoids that dependency but keeps
   measuring on shared `ubuntu-latest` VMs, which caps the whole effort's value.
   My recommendation is Radar, with the self-hosted gate as a stopgap.
3. **Regression-gate threshold.** I suggest starting at 5% on the ratio CI and
   tightening once the instruction-count track (Phase 5) shows what the real noise
   floor is. Worth deciding whether a gate failure blocks merge or only comments.
4. **Preset budget.** Adaptive sizing needs a wall-clock budget per preset instead
   of iteration counts. What is the acceptable CI benchmark step duration? That
   number determines how far the size sweeps in §6.6 can go.
5. **Scope of the coverage work.** §6.6 lists five priorities; items 1 and 2
   (base-field microbenchmarks, standalone NTT sweep) are the ones I would insist
   on. The rest can wait.
6. **Peregrine spike — do you want it scheduled?** One day, and it may well end in
   "not yet, needs `UInt64`/`Array` primitive support". The hook in §8.3 is worth
   building either way.

## 10. Sources

Verified in this session by direct inspection:

- [`leanprover/radar`](https://github.com/leanprover/radar) — README, bench-repo
  and measurement-format specification
- [`leanprover/radar-bench-generic`](https://github.com/leanprover/radar-bench-generic),
  [`radar-bench-lean4`](https://github.com/leanprover/radar-bench-lean4) — bench
  script contract
- [`leanprover/velcom`](https://github.com/leanprover/velcom) — predecessor
- [`peregrine-project/peregrine-tool`](https://github.com/peregrine-project/peregrine-tool) — README
- [`peregrine-project/lean-to-lambdabox`](https://github.com/peregrine-project/lean-to-lambdabox) —
  LeanToLambdaBox/Erasure.lean, benchmarks/README.md, benchmarks/TESTS, lean-toolchain

Verified in the research pass (3-voter adversarial verification):

- [`lean4/tests/bench/README.md`](https://github.com/leanprover/lean4/blob/master/tests/bench/README.md) —
  temci-based suites
- [temci](https://github.com/parttimenerd/temci) and
  [its docs](https://temci.readthedocs.io/en/latest/temci_exec.html) — runners,
  `usable` preset, stored sample format
- *Growing Mathlib: maintenance of a large scale mathematical library*,
  [arXiv:2508.21593](https://arxiv.org/html/2508.21593v1) — instruction counts as
  the stable metric
- [Mathlib Speedcenter Zulip thread](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/mathlib4.20speedcenter.html)
- Georges, Buytaert & Eeckhout, *Statistically Rigorous Java Performance
  Evaluation*, OOPSLA 2007 — [PDF](https://dri.es/files/oopsla07-georges.pdf)
- Barrett et al., *Virtual Machine Warmup Blows Hot and Cold*, OOPSLA 2017 —
  [arXiv:1602.00602](https://arxiv.org/abs/1602.00602),
  [ACM](https://dl.acm.org/doi/10.1145/3133876)
- Kalibera & Jones, *Quantifying Performance Changes with Effect Size Confidence
  Intervals* — [arXiv:2007.10899](https://arxiv.org/pdf/2007.10899)
- [Criterion.rs analysis documentation](https://bheisler.github.io/criterion.rs/book/analysis.html)
  — warmup ramp, Tukey outlier classification
- [gungraun](https://github.com/gungraun/gungraun) (formerly iai-callgrind) and
  [Callgrind manual](https://valgrind.org/docs/manual/cl-manual.html) — one-shot
  instruction counting
- [LLVM benchmarking guidance](https://llvm.org/docs/Benchmarking.html)
- [hyperfine](https://github.com/sharkdp/hyperfine)
- Beseda et al., [arXiv:2506.04204](https://arxiv.org/abs/2506.04204) and
  Traini et al., [arXiv:2209.15369](https://arxiv.org/abs/2209.15369) —
  steady-state detection follow-ups

**Not covered.** The research pass returned no surviving claims on zk/finite-field
benchmark methodology or published cycle baselines (arkworks, plonky3,
gnark-crypto, blst, zkalc, ZPrize), nor on Lean-4-specific measurement hazards,
and this session's web-search budget was exhausted before I could cover them
directly. §4 substitutes direct measurement for the second gap; §6.6 substitutes
measurement-on-identical-hardware for the first. No cycle-count figures are quoted
anywhere in this document.

### Repo locations referenced

| Thing | Path |
|---|---|
| Timing primitive | `bench/CompPolyBench/Common.lean:533` (`runTimed`) |
| Bignum checksum | `bench/CompPolyBench/Common.lean:471` (`mixChecksum`) |
| Unescaped JSON | `bench/CompPolyBench/Common.lean:577` (`jsonString`) |
| Linux-only hardware probe | `bench/CompPolyBench/Common.lean:364` |
| Label lookup tables | `bench/CompPolyBench/Common.lean:721`, `:744` |
| Registry / CLI | `bench/CompPolyBench/Setup.lean` |
| CI bench steps | `.github/workflows/lean_action_ci.yml:210` |
| CI group allowlist | `.github/workflows/lean_action_ci.yml:22` (`BENCH_CI_GROUPS`) |
| Build-time baseline logic | `scripts/build_timing_report.sh`, `lean_action_ci.yml:283` |
| Orphaned `#eval` benchmarks | `tests/CompPolyTests/Univariate/NTT/Benchmark.lean`, `tests/CompPolyTests/Bivariate/KroneckerBenchmark.lean` (a third, `CommonBench.lean`, was removed in 12.4) |

---

## 11. Review of this audit against the code and the run data

Status: added after §1-§10, by a second pass that read `bench/` in full and
re-analysed the 253-row `--small` run still sitting in
`bench/results-260804-125549.jsonl`. §1-§10 above are left as written; this
section records where they hold, where they overstate, and what they missed.
Where the two disagree, this section is the one to act on.

### 11.1 Confirmed

The bias mechanism, restated precisely: `mixChecksum` is `Nat` arithmetic modulo
18446744073709551557, the largest prime below `2^64`, so the accumulator is always
a GMP bignum and every mix is a heap-allocating multi-precision multiply-and-mod
inside the timed region. Also confirmed: the DCE hazard, absent dispersion,
order-coupled inputs, unescaped `jsonString`, the Linux-only hardware probe, the
missing wiki page, and the magic-number problem — though the count is **227
`selectNat` call sites**, not the ~150 of §0 and §3.3.

### 11.2 The headline in §0 and §4.1 is scoped too widely

The bias is a roughly **constant additive** offset of ~590 ns per checksum call.
It therefore only destroys rows whose per-iteration cost is of that order. Against
the real 253-row `--small` run:

| Per-iteration cost | Rows | Bias contribution |
|---|---:|---|
| `> 59 us` | 228 | `< 1%` |
| `5.9 - 59 us` | 21 | 1 - 10% |
| `0.9 - 5.9 us` | 4 | 10 - 60% |
| `< 880 ns` (harness-dominated) | **0** | — |

The cheapest row in that run is 1994 ns (`bivariate-full-eval-horner-xy-fast`).
`fields-goldilocks-mul` — the 603/800 ns exhibit of §4.1 — is not in the run at
all; it was measured in isolation, and it is one of only two groups anywhere near
the ns scale.

So §0's "the benchmark suite cannot currently observe the optimisations it exists
to guide" is true of ns-scale field arithmetic and false of the suite as it stands.
The value of the sink fix is **enabling** the base-field microbenchmarks that §3.7
correctly identifies as missing — not repairing 66 existing numbers.

The corollary contradicts §9.1's worry about an unexplained discontinuity in the
history: the figures published in `docs/wiki/field-extensions.md:281-307` (25 us,
3.5 ms, and the 3.1x - 7.9x spec-vs-`csimp` ratios) and `ROADMAP.md:77-79` carry
one checksum call per iteration at the 25 us - 15 ms scale, so they are within
about 2% of correct and survive the fix. There is no doc churn to schedule.

### 11.3 §3.1's additive-NTT claim does not hold in the data

_Settled by measurement in 12.1; see findings 6 and 7 there for the corrected
account, which supersedes the closing paragraph of this section._

§3.1 states that in the additive-NTT groups "the sink can cost more than the
transform being measured". At `l = 4, R_rate = 2` the reference row measures
1.82 s/iter, against 64 bignum mixes at ~37 us — 0.002%. The fast row measures
9.8 ms, so ~0.4%. The concern is sound in principle and unobservable in practice.

The real defect in those groups is sharper. In
`bench/CompPolyBench/Fields/Binary/AdditiveNTT/Impl.lean`:

- `checksumBtf3Output` (`:28-30`) folds over `List.finRange (2 ^ n)`, materialising
  a `2^n`-element list of `Fin` on **every** iteration before the bignum fold.
- `checksumConcreteBtfOutputArray` (`:37-42`) re-invokes
  `AdditiveNTT.arrayToFinFunction` **per index inside the fold** rather than
  hoisting it.

The reference row and the fast row of the same group therefore pay *different*
in-loop overheads, which makes the reference-vs-fast **ratio** unclean. That
matters more than the absolute offset, and it is the specific thing to fix.

### 11.4 What §1-§10 missed, in the order that matters

1. **Warmup does not work at all — at any preset.**
   `warmupIterations = preset.selectNat 100 10 0` (`Common.lean:56-57`), so warmup
   is **zero for every group at `--small`**; all 253 rows report
   `warmup_iterations: 0`. The batch, mod, mul and additive-NTT families use
   `preset.selectNat 1 1 0`, so they get **one** warmup iteration at `--medium`,
   which is the preset CI runs. And the warmup body is

   ```lean
   for i in [0:warmup] do
     let _ := run i
     pure ()
   ```

   a dead pure `let` — precisely the elimination pattern §4.2 documents — so it may
   warm nothing even where the count is nonzero. §3.2 notes the absence of
   repetition but never states that warmup is absent.

2. **The dominant statistical defect is `n = 1`, not "one sample of one total".**
   67 of 253 rows measure exactly **one** iteration; 107 measure three or fewer; 27
   of those spend over a second in the timed region. The expensive groups pin a
   large input shape and shrink the iteration count to 1, so the large-NTT and
   batch-eval numbers — the suite's most strategically important — are single
   unrepeated samples. Worst cases: `univariate-batch-large-naive-horner` at 22.25 s
   over one iteration, and `univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod`
   at 13.53 s over one iteration against a `-fast` sibling at 11.74 s over two. No
   change to the sink touches any of this.

3. **The untimed validation pass costs exactly as much as the measurement.**
   `checksumIterations := measured` is the default (`Common.lean:535`), so the full
   workload runs a second time for validation. Roughly half of the ~6.5 minutes a
   full `--small` run spends measuring buys no measurement. Cutting the validation
   pass to one iteration is a free 2x.

4. **Declaration ergonomics, which the coming per-benchmark pass will pay for.**
   The group key and title are written **three times** per group — the
   `*GroupInfos` list, the `*Tasks` list, and the returned `BenchGroup` literal (see
   `Fields/Goldilocks.lean:31-33`, `:53-54`, `:78-85`) — so a rename can silently
   drift. `runTimed` takes 11 positional parameters, five of them consecutive
   `String`s, across 226 call sites. §3.10 flags the label lookup tables but not this.

5. **`BenchTask`'s generality is entirely unexercised**, which makes the §6.4 fix
   far cheaper than §6.4 suggests. `BenchTask.runTask` has the shape
   `BenchPreset → BenchSelection → StdGen → IO (Array BenchGroup × StdGen)`, but all
   66 registered tasks go through `BenchTask.fromGroupRunner`, which discards the
   selection. Per-group seeding is therefore a change to **one function**
   (`Common.lean:180-185`), not a 24-module refactor, and it lets `StdGen` disappear
   from the task contract altogether.

6. **Confirmed dead code.** Zero non-definition references anywhere: the ten
   per-area `runX (preset) (selection) (gen)` wrappers (`runUnivariate`,
   `runUnivariateBasic`, `runUnivariateManyEval`, `runUnivariateBatchEval`,
   `runUnivariateNttFastMul`, `runUnivariateNttFastMulLow`, `runMultivariate`,
   `runMultilinear`, `runBivariate`, `runAdditiveNtt`) and seven `*GroupInfos`
   aggregate lists. The two live ones are reached only through fragile
   `.getD i ⟨"…", ""⟩` indexing (`Bivariate/GuruswamiSudan.lean:328-341`,
   `GuruswamiSudan/ReceivedWord.lean:439-446`).

7. **§6.6's "delete the three orphaned `tests/` benchmarks" would drop real
   coverage.** The since-removed `CommonBench.lean` also carried
   four `#guard` correctness checks and a retained baseline `clMul` implementation
   (the deleted `Finset.fold`-over-`Fin 256` version) used as a reference against
   the current one. Nothing imports the file, so CI never runs those guards. They
   must be migrated into a real test before the file goes.

8. **The checksum already gates CI.** The `Run evaluation benchmarks` step has no
   `continue-on-error` and no `if:`, so a checksum mismatch — which exits nonzero —
   already fails the job. §2.2 and §3.5 treat the digest as an intra-run
   cross-check only. Separately, the artifact step globs `bench/results-*.jsonl`
   and `bench/report-*.md`, which is correct on a fresh CI checkout but locally
   sweeps all 17 stale output files into the artifact.

### 11.5 Consequences for the plan in §7

- **§7's Phase 0 / Phase 1 split is the wrong cut.** Phase 0 alone moves a handful
  of ns-scale rows and leaves `n = 1` in place. The sink fix and the sampling layer
  are both cheap and belong in sequence, not staged behind each other by priority.
- **§6.1's up-front split of `Common.lean` is premature.** It has 12 direct
  importers, and Phases 0-3 rewrite most of what would be moved. Carving each
  module out of `Common.lean` as part of the PR that rewrites it gets the same
  Parnas separation without a big-bang refactor that is then rewritten.
- **The §6.3 adaptive scheme needs a defined behaviour for workloads where one
  iteration already exceeds the sample target.** §6.3 assumes `itersPerSample` can
  always be chosen; for 27 rows it cannot. The answer taken here is to collect as
  many samples as the budget allows, minimum one, and mark the row unreplicated.

### 11.6 Scope taken for the first push

Foundations only: the measurement core, the sampling and statistics layer, input
determinism, and declaration ergonomics. Explicitly deferred — Radar integration
and registration (§5.1, §7 Phase 2), the regression gate and threshold (§9.3),
coverage work (§6.6, §7 Phase 4), the instruction-count track (§6.5, §7 Phase 5),
the external yardstick (§6.6, §7 Phase 6), and the Peregrine track (§8) including
its hook.

Three decisions settled that §9 left open:

- **§9.4, preset budget: do not gate on CI benchmark wall-clock.** The benchmark
  step moves off the blocking CI job, so measurement quality stops trading against
  CI duration.
- **Input sizes are not retuned in this push.** Sample counts are reported honestly
  and thin rows flagged; sizes are revisited in a later systematic per-benchmark
  pass.
- **§9.1: no separate Phase 0 PR.** Per 11.2 there is no discontinuity to explain,
  so the sink fix does not need its own PR to carry a before/after table.

### 11.7 Method

The band table in 11.2 and every count in 11.4 come from
`bench/results-260804-125549.jsonl` — a full 253-row `--small` run, the only
full-suite result file present — read with `python3`, plus direct reading of
`bench/` (23 files, 4635 lines), `.github/workflows/lean_action_ci.yml`,
`scripts/build_timing_report.sh`, and `docs/wiki/`. No benchmarks were rebuilt or
re-run for this section; the ~586 ns and ~1.6 ns figures of §4.1 are taken as given
from the original probe, and 11.2 only re-scopes their consequences.

---

## 12. Change log

Work lands as a **stack**: each branch is cut from the previous one, so each PR
reviews as a small diff and the stack merges bottom-up. Base of the stack is
`dhsorens/benchmarking`.

| # | Branch | Scope | Status |
|---|---|---|---|
| 1 | `dhsorens/bench-measurement-core` | Cheap `UInt64` sink in the timed loop, forcing discipline, real warmup, floor + canary groups, `jsonString` escaping, symmetric additive-NTT digests | landed |
| 2 | `dhsorens/bench-sampling` | Multi-sample collection, median/MAD/Tukey stats, unreplicated flags, capped validation pass reused as warmup | landed |
| 3 | `dhsorens/bench-determinism` | Per-group seeding from the group key, registration made authoritative, dead-code removal | landed |
| 4 | `dhsorens/bench-reporting` | Cross-platform hardware probe, `bench/out/`, `docs/wiki/benchmarking.md`, `clMul` guard migration | landed |
| 5 | `dhsorens/bench-foundations` | `--validate-only`, correctness gate in main CI, on-demand `benchmarks.yml` | landed |

### 12.1 Measurement core (`dhsorens/bench-measurement-core`)

**New modules.** `bench/CompPolyBench/Harness/Sink.lean` (sink primitives),
`bench/CompPolyBench/Harness/Timer.lean` (the single place that reads the clock),
`bench/CompPolyBench/Harness/SelfCheck.lean` (`harness-floor`, `harness-canary`). `Common.lean`'s
`runTimed` now delegates to `Timer`; the checksum block stays where it is until
PR 3 moves the registry.

**Measured effect**, `--small`, darwin/arm64, Lean 4.33.1:

| | before | after |
|---|---:|---:|
| `harness-floor` (loop + sink, per iteration) | n/a | **1.89 ns** |
| `goldilocks-mul-fast` | 619 ns | **3 ns** |
| `goldilocks-mul-zmod` | 788 ns | **365 ns** |
| reported `ZMod : Fast` ratio | 1.27x | **~108x** |
| `harness-canary` margin over floor | n/a | 236x |

**Deviations from the plan, and why.**

1. *`sink` is an optional argument, not a `body : Nat → UInt64 → UInt64`
   signature.* The planned signature would have required editing all 226
   `runTimed` call sites, whose result types include partial applications over
   `DenseMatrix F`, `Option (CBivariate F)` and `Option (Array F)`. A
   default-valued `sink` removes the bignum `mixChecksum` from the timed loop at
   every call site with no churn, and lets a cheap sink be declared where it pays.
   The forcing guarantee comes from `Timer`'s accumulator plumbing plus the
   canary rather than from the type.
2. *`sinkStep` is `@[inline]` and `runTimed` is `@[specialize]`.* With
   `@[noinline]` and unspecialised closures the harness floor measured
   **22.4 ns/iter** — which would itself have dominated the 1.6 ns field multiply
   this work exists to expose. Inlining and specialising took the floor to
   1.89 ns. The elimination risk `@[noinline]` was guarding is now carried by the
   canary, at a 236x margin.
3. *Per-row floor subtraction deferred to PR 2.* The floor turns out to be
   **per representation**, not global: a `ZMod` element above `2 ^ 63` has no
   cheap word digest while its fast counterpart does, so subtracting a single
   global floor from a `ZMod` row would mislead. This needs the per-representation
   floor the stats layer can provide. §4.1 anticipated this ("any redesigned sink
   must be measured per representation, not assumed cheap"); it is a sharper
   constraint than §6.2c allows for.
4. *Preset iteration counts untouched.* PR 1 makes warmup *effective* — it was a
   dead `let` and may have warmed nothing at any preset (11.4.1). PR 2 makes it
   *sized*; warmup is still 0 at `--small`.

**Findings from doing the work.**

5. *§4.1 underestimates the `ZMod` Goldilocks multiply by about 8x.* Measured
   with a native sink over 200000 iterations with warmup, it is **325 ns/iter**,
   not the ~41 ns of §4.1. `ZMod n` is `Fin n`, so the multiply is
   `(a.val * b.val) % n` over `Nat` with both operands near `2 ^ 64` — a 128-bit
   bignum multiply and mod, with allocation. The group's corrected ratio is
   therefore ~108x, not the ~25x §4.1 predicts.
6. *§3.1's additive-NTT claim is refuted, and 11.3 was right to doubt it.*
   Replacing the bignum digest and the per-iteration `List.finRange (2 ^ n)`
   materialisation moves those rows by about **5%** (`additive-ntt-btf3-l4-r2`
   1736 ms → 1649 ms; `-fast` 9.15 ms → 8.81 ms). The digest was never close to
   costing more than the transform.
7. *The additive-NTT rows are asymmetric for a reason neither §3.1 nor 11.3
   identified.* The reference row returns `Fin (2 ^ n) → α`, a **function**: an
   output does not exist until an index is applied, so realising the whole result
   is part of that row's work and not part of the `Array`-returning fast row's.
   An intermediate version of this branch sampled four output positions in both
   sinks and the reference row appeared to get 16x faster, because it was then
   computing a sixteenth of what the fast row computed. Both sinks now fold over
   every output position. The lesson generalises: **a sink may only skip work the
   benchmark has already done.** Sampling is correct for a materialised array and
   wrong for a lazily-indexed function.
8. *Cross-commit checksum comparison is impossible today, confirmed empirically.*
   199 of 235 shared rows differ from the August baseline purely because 13 groups
   were added and 2 removed in between, shifting the shared `StdGen`. No point in
   the suite's history can serve as a regression baseline until PR 3 lands.
9. *`sink_digest` earns its place in the schema.* Emitting the timed loop's
   accumulator keeps it observably live (so an `@[inline]` timing loop cannot have
   its accumulation eliminated) and doubles as a determinism signal. It is what
   flagged finding 7: across two full runs it changed on exactly the five rows
   whose sink had changed and nowhere else.

**Also in this branch.** `jsonString` now escapes via `Lean.Json.renderString`;
`checksumConcreteBtfOutputArray` hoists `arrayToFinFunction` out of its fold
(digest-preserving — verified across two full runs, 250 named records, zero
mismatches); `harness-floor` and `harness-canary` added to `BENCH_CI_GROUPS`;
`bench/README.md` documents the validation/timed split and the sink contract.

**Not required:** `./scripts/update-lib.sh` globs `CompPoly/*.lean` only, so new
modules under `bench/` need no regeneration — the lakefile's
`Glob.submodules \`CompPolyBench` covers them.

### 12.2 Sampling and statistics (`dhsorens/bench-sampling`)

**New modules.** `bench/CompPolyBench/Harness/Stats.lean` (summary statistics),
`bench/CompPolyBench/Harness/Sample.lean` (sample collection). `runTimed` now
splits its iteration budget into samples instead of timing one region.

**Measured effect**, full 68-group `--small` run, 286 records:

| | before | after |
|---|---:|---:|
| rows with 5 or more samples | 0 | **172** |
| rows with 2-4 samples, flagged | 0 | 47 |
| rows with a single unrepeated sample | 253 of 253 | 67, each marked `n=1` |
| dispersion reported | none | median MAD **1.4%**, p90 3.0%, max 5.1% |
| rows with severe Tukey outliers | not detectable | 27 |
| timed-region total | 152.8 s | 152.0 s |
| full run wall clock | — | 277 s |

**The noise floor is now a measured quantity.** Across the 172 replicated rows
the median absolute deviation is 1.4% of the median, with p90 at 3.0% and a
maximum of 5.1%. §9.3 asks what the regression-gate threshold should be and
could not answer it without data; this is that data, on a *quiet local machine*.
A 5% gate sits at roughly the worst observed sample dispersion, so it is a
defensible starting point and anything tighter than about 3% would be
false-positive-prone even before a shared CI runner adds its own variance.

**Deviation from the plan.** The 227 `selectNat` sites are **not** retired here.
Retiring them requires a wall-clock budget per benchmark, which is precisely the
per-benchmark judgement deferred to the systematic pass; doing it now would mean
touching all 226 `runTimed` call sites twice. Instead each existing count is
reinterpreted as a total-work budget and split into up to `targetSampleCount`
samples. This fixes replication wherever the budget can pay for it and leaves the
counts to retire naturally when each benchmark gets a considered budget. The
geometric calibration ramp of §6.3 is deferred with them: with a total budget
supplied there is nothing for it to calibrate.

**Findings from doing the work.**

1. *A zero interquartile range makes Tukey label everything.* Where samples agree
   to the picosecond, both fences collapse onto the quartiles and every sample
   that differs at all is marked a severe outlier — the opposite of the intended
   signal. Labelling is now suppressed when the interquartile range is zero.
2. *An unspecialised function between `runTimed` and the timed loop costs 5x.*
   Interposing `collectSamples` re-introduced the closure indirection that
   `@[specialize] runTimed` had removed, and `goldilocks-mul-fast` went from 3 ns
   to 16 ns. `@[specialize]` on `collectSamples` restored it. Anything that sits
   between the specialisation boundary and the loop has to carry the attribute.
3. *11.4.3 was right about the validation pass but wrong about the fix.* On the
   original harness the validation pass cost **138 s against a 192 s timed
   region** — 72%, so it really did nearly double the suite. But capping it at
   `validationIterationCap` saves only ~0.8 s, because the cost is concentrated
   in rows whose validation already ran exactly *once* and whose single run takes
   up to 22 s. The cap is still right for the 19 cheap rows it touches; the
   saving on expensive rows comes instead from letting the validation pass count
   towards warmup, since it has already executed the body. An expensive workload
   validated once now runs twice per benchmark rather than three times.
4. *The capping change is exactly auditable.* 19 records had a validation pass
   above the cap; exactly those 19 digests changed and the other 267 did not,
   with no unexplained differences. Letting validation count as warmup changed no
   digest at all.

**Still unreplicated.** 67 rows remain at `n=1`. Every one is a workload whose
single iteration already exhausts its budget — `univariate-batch-large-*` at
degree 65536, the additive-NTT reference rows, `univariate-mod-by-monic-medium-*`.
No amount of harness work fixes these; they need smaller input shapes, which is a
per-benchmark judgement for the systematic pass. They are now visibly marked
rather than silently averaged.

### 12.3 Determinism (`dhsorens/bench-determinism`)

**The change.** `genFor` derives each group's `StdGen` from its key, applied
inside `BenchTask.fromGroupRunner`. Because all 66 registered tasks go through
that one function (11.4.5), this is a three-line change and no group runner's
signature moves. The shared generator is now passed through untouched.

**Verified.** `--group fields-goldilocks-mul`, `--groups fields-goldilocks-mul,additive-ntt-btf3-l2-r2`
and the same pair reversed all produce identical digests for every row. Running
the exact `BENCH_CI_GROUPS` subset reproduces the full run's digest on **all 184
comparable rows** — the property §3.4 says is unobtainable today. Full 68-group
run: exit 0, 286 records, 273 s.

**Registration is now authoritative.** `fromGroupRunner` stamps `groupKey` and
`title` from the `BenchGroupInfo` that `--list` and the CI allowlist validate
against, so a runner's own literals can no longer drift from its registration.
The literals inside the 66 group runners are now inert; removing them means
rewriting every runner's return expression and is left to the systematic pass,
which will touch each one anyway.

**Dead code removed.** 25 declarations with no references anywhere: the ten
per-area `runX` wrappers and fifteen `*GroupInfos` aggregate lists (seven dead
before this branch, eight more once the `runX` wrappers that consumed them
went). 175 lines deleted, 17 added.

**Digest fixtures deferred, deliberately.** Per-group seeding is the prerequisite
and it now holds, but committing 250 expected digests immediately before a
systematic pass that will deliberately change many benchmarks' input shapes would
produce a fixture file in near-permanent conflict. The mechanism is worth adding
once the benchmark set settles. Note also that digests remain preset-dependent,
since the validation pass length derives from the measured iteration count.

**Comparison keys need care.** Record `name` is not unique: `extension-mul` and
`extension-inv` are each emitted by the ext4, ext5 and ext6 groups. Any tool
diffing two result files must key on `(name, field, input_shape)` — keying on
`name` alone silently collapses those rows and reports false differences. Worth
knowing before the comparison tooling in §6.7 gets written.

### 12.4 Reporting, platform, and docs (`dhsorens/bench-reporting`)

**Darwin hardware probe.** `collectRunnerHardware` falls back to `sysctl` when
neither `lscpu` nor `nproc` exists, so a local run reports the machine that
produced a number instead of `unavailable outside GitHub Actions`. `df --output`
is GNU-only, so the darwin path parses the full `df -h` table where the size is
the second field. A local report now reads
`Apple M3 Max / 16 logical CPUs / 64 GiB`.

**Single output directory.** Reports and results go to `bench/out/`, created on
demand and ignored wholesale, replacing two ignore rules across two files. This
also closes 11.4.8's live hazard: CI's artifact glob was `bench/results-*.jsonl`,
correct on a fresh checkout but locally sweeping every stale file into the
artifact. The 17 accumulated output files, including the May 2026
`evaluation-*` generation, are gone.

**`clMul` guards rescued before deletion.** The `CommonBench.lean` file under
`tests/CompPolyTests/Fields/Binary/` carried four `#guard`
correctness checks and the removed `Finset.fold`-over-`Fin 256` baseline that
pins the current `clMul` to the behaviour it replaced — none of which CI ran,
because nothing imported the file. They now live in
`tests/CompPolyTests/Fields/Binary/Common.lean`, which `CompPolyTests.lean`
imports, and the benchmark file is deleted. Verified by breaking one guard and
confirming the build fails, then restoring it. This is the coverage §6.6 would
have deleted silently.

`tests/CompPolyTests/Univariate/NTT/Benchmark.lean` and
`KroneckerBenchmark.lean` are deliberately left in place: the former holds the
only NTT-vs-schoolbook crossover logic in the repo and is the specification for a
future crossover metric.

**`docs/wiki/benchmarking.md`** added and registered in both hand-maintained
lists in `docs/wiki/README.md`, since `check-docs-integrity.py` validates that
links resolve but not that a page is registered anywhere. It owns the two-pass
model, the sink rule, how to read a `Spread` column, the self-check, determinism,
how to add a group, and a known-gaps list. The duplicated line at
`docs/wiki/quickstart.md:111-112` is fixed and `generated-files.md` updated.

**Deviations from the plan.**

1. *The benchmark step was not moved off the blocking CI job.* The decision
   recorded in 11.6 was that measurement quality should not trade against CI
   duration, and it has not: nothing in PRs 1-3 caps sampling to fit a budget.
   But *structurally* moving benchmarks to their own job means a second
   Mathlib-dependent build, which trades a real and recurring CI cost for a
   scheduling benefit. That is a cost decision rather than an engineering one and
   is left open — see below. The `BENCH_CI_GROUPS` comment no longer claims
   wall-clock is the limiting criterion, and the step keeps its fail-closed
   behaviour: benchmark *timings* are informational, but a checksum mismatch or a
   canary failure is a correctness signal that should fail the run.
2. *A separate reporting module was not split out.* `Common.lean` is down from 935 to ~1020
   lines gross, but four concerns have already moved into `Harness/` (`Sink`,
   `Timer`, `Sample`, `Stats`) and the remaining reporting code is about to be
   rewritten anyway when per-representation floors and the label-table retirement
   land. Moving it now would mean moving it twice.

**Open decision** — resolved in 12.5, though not the way it was framed. The
question assumed the choice was *where the benchmark job runs*. The better cut
turned out to be *what it runs*: the step was doing correctness and timing at
once, and only the timing half needed to leave.

### 12.5 Splitting correctness from timing in CI (`--validate-only` and `benchmarks.yml`)

The question was whether benchmarks could run only when the code they touch
changes. Path filtering is available — `lean_release_tag.yml` already uses a
`paths:` filter — but it is the wrong instrument twice over. A group's
performance depends on whatever it transitively calls, and
`CompPoly/Fields/Montgomery/**` underpins nearly every group, so a filter honest
enough to be safe would fire on almost every substantive PR. And it reduces the
*cost* of a signal that is not actionable rather than taking it off the blocking
path — see finding 5 below for what the runner's noise actually looks like, which
is not what I assumed.

The step was doing two separable jobs — 41 groups cross-checking a canonical
`ZMod` model against its native-word implementation on random inputs plus the
harness canary, and a timing report. So the split is not "run benchmarks
sometimes" but **the correctness half always gates; the timing half never runs in
blocking CI**.

**`--validate-only`.** Runs the untimed digest pass and the agreement check and
collects no samples. Deterministic and machine-independent, which is what a gate
should be. Threaded through an `initialize IO.Ref Bool` in
`bench/CompPolyBench/Harness/Timer.lean` rather than a parameter, because every
alternative means editing all 226 `runTimed` call sites. Reports through a
compact `renderValidationMarkdown` — group, rows, agreement, digest — rather
than a timing table of zeros.

**Measured**, 41 curated groups at `--medium`, darwin/arm64:

| | wall clock |
|---|---:|
| timed run (what CI did) | **124 s** |
| `--validate-only` (what CI does now) | **32 s** |
| `--validate-only`, all 68 groups | 138 s |

So the gate got about 4x cheaper *and* kept the only part of it worth gating on.
The 41-group set is retained over all 68 because the extra 106 s buys coverage of
groups whose single iteration costs seconds; the numbers are recorded in
`bench/ci-groups.txt` so the trade can be revisited.

**Findings from doing the work.**

1. *The canary would have been silently disabled.* `runHarnessSelfCheck` compares
   timed totals, and with no samples collected `0 < 3 * 0` is false — the check
   would pass vacuously in exactly the mode CI runs, disabling the one guard
   against benchmark bodies being optimised away. `runTimed` therefore takes
   `forceTiming`, which the self-check sets; the canary costs ~50 ms and runs in
   both modes. Verified by stubbing `canaryRounds` to 0 and confirming a
   `--validate-only` run exits 1.
2. *`BENCH_CI_GROUPS` could not stay a workflow `env:` entry.* A second workflow
   cannot see it, and duplicating 41 keys invites drift. The list moved to
   `bench/ci-groups.txt`, one key per line with `#` comments, read by both
   workflows — and it now sits next to the benchmarks it names rather than buried
   in YAML.
3. *No required status checks exist on `main`.* The ruleset enforces only
   `deletion`, `non_fast_forward` and `pull_request`. The usual footgun — a
   workflow skipped by a `paths:` filter never reports its check and blocks the
   PR — therefore does not apply here, so both a separate workflow and a
   step-level skip were structurally safe. Worth re-checking if required checks
   are ever added.
4. *The new workflow must not save caches.* `lean_action_ci.yml` documents the
   Actions cache as already over quota (~10.3 GiB against 10 GB), which is why
   `.lake` is split into two entries. `benchmarks.yml` restores both and saves
   neither.

**Kept in main CI deliberately.** `lake build CompPolyBench` still runs on every
PR, because the correctness gate needs the binary. Only the timed *run* moved
out. Dropping the compile too would mean dropping the differential check, which
is the opposite of the priority.

5. *The shared runner is steadier than I assumed, and I had this backwards.* I
   wrote here and in the docs that CI-runner dispersion would be worse than the
   1.4% median MAD §12.2 measured locally. The first real CI run of the timing
   workflow says otherwise: **median MAD 0.2%, p90 0.5%, max 1.0%** across 172
   replicated rows, appreciably *tighter* than the local figures. A busy
   development laptop with frequency scaling and heterogeneous cores is a noisier
   place to measure than an idle VM slice.

   What is worse on CI is the tail: **56 of 172 rows carried severe Tukey
   outliers, against 27 of 286 locally** — the signature of a quiet baseline
   punctuated by preemption.

   The decision stands but the reason was wrong, and is corrected everywhere it
   appeared. Neither figure is what a gate needs: a gate compares *runs against
   each other*, on a runner whose CPU model varies between runs (§3.6), and one
   run cannot measure that variance. Timings are advisory because cross-run
   comparability is unvalidated, not because within-run noise is high.
   Establishing the run-to-run figure is the next measurement worth making, and
   is what any threshold should be set from.

**Verified on a real runner**, not only locally. The first push auto-triggered the
timing workflow through the `bench/**` filter, so both paths ran end to end:

| | duration |
|---|---:|
| main CI job, total | 3m29s |
| ... of which `Validate benchmark implementations` | **46s** |
| ... of which `Build evaluation benchmark executable` | 64s |
| timing workflow, total | 4m55s |
| ... of which `Run benchmarks` | 167s |

On the runner the correctness gate costs 46s where the timed run it replaced
cost about 167s. The workflow restored both caches, validated its group
selection, and upserted a PR comment carrying the advisory caveat.

**Not done.** No nightly schedule. Timings are produced when someone asks —
manual dispatch, a `/bench` comment from a repo member, or a PR touching
`bench/**`, which is the one place path filtering genuinely fits.
