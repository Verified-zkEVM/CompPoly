# Benchmarking

How the compiled benchmark suite measures, what its output means, what to do
when adding a benchmark, and where the best time recorded so far for every
operation it covers is kept. [`bench/README.md`](../../bench/README.md) is the operator's guide —
invocation, presets, group selection, the group inventory — and
[`autoresearch.md`](autoresearch.md) is the optimisation loop. This page owns
the recurring guidance; the record that loop writes into, one section per
benchmarked component with every row tied to the commit whose build produced
it, is [`benchmark-best-times.md`](benchmark-best-times.md). The audit and
change log that produced the suite are frozen in
[`docs/bench-audit-2026.md`](../bench-audit-2026.md).

## The suite

`lake exe CompPolyBench` is a compiled executable under `bench/`, built from the
same library the proofs are about. It is organised in **groups**: one group is
one operation at one input shape over one field, such as
`fields-koalabear-mul` or `ntt-koalabear-l12`, and `--list` prints the
authoritative set (about a hundred and ten at the time of writing). A group
holds one or more **rows**, one per implementation of that operation. Where the
library has both a canonical definition and a fast twin, the group carries both
as rows: `ZMod` against the Montgomery word, the `BitVec` specification against
the packed tower, the definitional Reed-Solomon encoder against the certified
NTT one. Where it has only the fast implementation, the group is a single row.
Every row is executed twice, once to validate and once to time; see
[The two passes](#the-two-passes).

## Commands

```bash
lake build CompPolyBench
lake exe CompPolyBench --small                       # every registered group, timed
lake exe CompPolyBench --medium --validate-only      # correctness only, no timings
lake exe CompPolyBench --groups fields-goldilocks-mul
lake exe CompPolyBench --list                        # authoritative group keys
lake exe CompPolyBench --out-dir bench/out/mine <key> # somewhere other than bench/out
lake exe CompPolyBench --compare --baseline <dir> --candidate <dir>   # judge two builds
./scripts/bench-ab.sh run fields-goldilocks-mul      # freeze, interleave, compare
```

Output lands in `bench/out/`, which is created on demand and ignored in its
entirety. A checksum mismatch inside a group makes the executable exit nonzero
after writing its artifacts, and CI's validation step has no
`continue-on-error`, so a mismatch fails the run.

Comparing two builds of the library on one machine is the job of `--compare`
and its driver `scripts/bench-ab.sh`; the loop that uses them is
[`autoresearch.md`](autoresearch.md).

## Two tracks, because only one of them is trustworthy

The suite does two separable jobs. Keeping them apart is the difference between a
gate you can believe and a gate that fails on noise.

| | Correctness | Timing |
|---|---|---|
| What | digest pass, group agreement, harness canary | median, dispersion, outlier labels |
| Where | `lean_action_ci.yml`, **every PR** | `benchmarks.yml`, **on demand** |
| How | `--validate-only` over `bench/ci-groups.txt` | `--small`/`--medium`/`--large` |
| Cost | ~29s of CPU over the curated set, ~174s over all groups | minutes |
| Gates? | **yes**, fails the run | no, advisory |

`--validate-only` runs the untimed digest pass and the agreement check and
collects no samples, so it is deterministic and machine-independent. That is
exactly what a gate should be. It is also the fast local answer to "is this
implementation still correct".

Timings stay out of the blocking path, but the measured reason is not the
obvious one. On `ubuntu-latest` *within-run* dispersion came out **tighter** than
on a quiet local machine — median MAD 0.2% against 1.4% — while severe Tukey
outliers were about twice as common (56 of 172 rows against 27 of 286). A mostly
idle VM slice punctuated by preemption looks exactly like that.

Neither number is what a gate needs. A regression gate compares **runs against
each other**, on a runner whose CPU model varies between runs, and a single run
cannot measure that variance. So the timings are advisory because cross-run
comparability is unvalidated, not because the runner is jittery.

Three ways to get timings: **Actions → Benchmarks → Run workflow** with a preset
and optional group list; a `/bench` comment on a PR from a repo member,
optionally followed by a group list; or automatically on a PR touching
`bench/**`, since a change to the harness itself should be measured. Results
arrive as a PR comment and an artifact.

One thing the canary needs: it compares timed totals, so under `--validate-only`
it would pass vacuously against a zero floor. `runTimed` therefore takes a
`forceTiming` flag that the self-check sets, and the canary keeps running (~50ms)
in both modes. If you touch that path, break the canary body deliberately and
confirm a `--validate-only` run still fails.

## The two passes

Every benchmark body is executed twice, for different purposes, and confusing
them is the main way benchmark numbers go wrong.

The **validation pass** is untimed. It folds a strong `Nat` digest over the full
result, and it is what the cross-implementation agreement check compares. This is
why a wrong-but-fast implementation cannot be benchmarked here. It runs for the
period of the body in its iteration index (`digestPeriod`, capped at
`digestIterationCap`), and counts towards warmup, since it has already executed
the body.

The **timed pass** folds each result through `sink : α → UInt64`. A sink exists
only to keep the result live so the body cannot be optimised away; its value is
never compared against anything.

**A sink may only skip work the benchmark has already done.** Sampling a few
positions of a materialised `Array` is correct — the transform already computed
every element. Sampling a few positions of a `Fin n → α` is *not*: nothing has
been computed until an index is applied, so sampling makes that row do a fraction
of the work its counterpart does, and the group's ratio becomes meaningless.

Pass an explicit `sink :=` whenever the default `Nat` digest would allocate —
carriers whose canonical value exceeds `2 ^ 63` are the usual case. Both rows of
a group should carry comparable sink cost; where a representation makes that
impossible, the group's ratio is a lower bound on the real speedup.

## Presets

There are no iteration counts written beside benchmarks. A preset is a
wall-clock budget, and the harness sizes each row from it
(`bench/CompPolyBench/Harness/Budget.lean`):

| Preset | Warmup ramp | One sample | Samples | Cap per row |
|---|---:|---:|---:|---:|
| `--small` | 20 ms | 1 ms | 10 | 0.2 s |
| `--medium` | 50 ms | 1 ms | 20 | 2 s |
| `--large` | 200 ms | 1 ms | 50 | 60 s |

The sample length is the same at every preset on purpose: a sample is a mean
over `itersPerSample` iterations, so varying it would make `--small` and
`--large` report structurally different spread for identical code. Sample
count is the quality axis a preset varies; the cap is what lets workloads
costing seconds per iteration be replicated at all. `--medium` is what CI and
the A/B loop use, and what the tables in
[`benchmark-best-times.md`](benchmark-best-times.md) are measured at.

## Reading a result

The headline number is the **median** sample, not the mean and not a total. The
`Spread` column carries the median absolute deviation as a percentage of the
median:

| Spread | Meaning |
|---|---|
| `±2.4%` | normal |
| `±1.1% (n=3)` | too few samples for the spread to mean much |
| `n=1` | one iteration exhausted the budget; a single unrepeated sample |
| `±0.4% !2` | two samples labelled severe Tukey outliers |

**Never read a ratio off an `n=1` row.** Those benchmarks pin an input shape
large enough that one iteration exhausts the budget; the fix is a smaller shape,
not more iterations.

Outliers are labelled, never dropped. The full per-sample vector is emitted as
`samples_picos` in the JSONL, with `min`, `median`, `mean`, `p95`, `stddev` and
`mad` in picoseconds per iteration.

On a quiet local machine the median absolute deviation across replicated rows is
around 1.4% of the median, with a maximum near 5%. Treat differences below that
as noise, and expect a shared CI runner to be worse.

`Warmup` and `Iterations` come from the preset's wall-clock budget, not from a
number written down beside the benchmark: a calibration ramp times 1, 2, 4, …
iterations until the warmup budget is met, and its last step estimates the
per-iteration cost that sizes the samples. So **`Iterations` is not comparable
between runs** — it depends on how fast the machine was when that row was
calibrated. Compare `Median` and `Spread`. `manifest-<runId>.json` records the
commit, dirty flag, toolchain, budgets, seed and host for exactly this reason.

## The harness self-check

`harness-floor` times an empty body: the per-iteration cost of the loop and the
sink, which every other benchmark sits on top of. `harness-canary` times a body
with a known non-eliminable cost and **fails the run** if it does not clear the
floor by `canaryFloorRatio`.

The canary is not ceremony. A benchmark that has been optimised away looks
exactly like a benchmark that got very fast, and the difference is invisible in
the output. Anything that changes the timing path — inlining attributes,
specialisation, a new indirection between `runTimed` and the loop — should be
checked against the floor before and after.

Note that a function interposed between the specialisation boundary and the timed
loop must carry `@[specialize]`, or the closure indirection returns and the floor
rises by an order of magnitude.

## Determinism

Each group derives its generator from its key, so a group's inputs do not depend
on which other groups ran or in what order. `--group X` and `--groups X,Y` agree,
the CI subset agrees with a full local run, and digests are comparable across
runs and commits.

Digests remain preset-dependent, because the validation pass length derives from
the measured iteration count.

Record `name` is **not** unique, in two ways: `extension-mul` is emitted by the
ext4, ext5 and ext6 groups, and a chained group emits a latency row and a
throughput row under one name. Any tool comparing two result files must key on
`(group_key, name, digest_class, method)`, which is what `--compare` does.

## Comparing two builds

`CompPolyBench --compare` judges a candidate build against a baseline build
from the results files each wrote, one file per invocation, and
`scripts/bench-ab.sh` is its driver:

```bash
./scripts/bench-ab.sh freeze                     # build and keep the baseline binary
# ... edit the fast implementation, lake build ...
./scripts/bench-ab.sh run fields-koalabear-mul   # both binaries, turn about, then --compare
```

The driver runs the two binaries alternately for five rounds a side, appends
the harness groups so machine drift is measured alongside, and the comparison
reasons about the five invocation medians per side. A row is **`faster`** only
when the ratio of medians clears a threshold (5% by default) *and* every
candidate invocation beat every baseline invocation; `slower` is the mirror
image; everything else is `same`. A digest that differs between the builds is a
**`mismatch`** and exits 3: the candidate computes something else, and no ratio
is read. A candidate implausibly fast against the harness floor is flagged
**`SUSPECT`**. Harness drift outside ±10% means the machine was not steady and
the run is repeated rather than read.

The loop built on this is [`autoresearch.md`](autoresearch.md): one change per
iteration; the kernel's tests and the digest gate first, `bench-ab.sh run` as
the measurement second, and the refinement proof last, paid only for a change
that is `faster` without `SUSPECT`; revert otherwise. The trusted
code base does not move during it: a fast implementation is swapped in by
`@[csimp]` with an equality theorem, or by a twin definition with an `_eq_`
theorem, never by `@[implemented_by]` or `native_decide`.

## Adding a benchmark

1. Write a group runner returning a `BenchGroup`, and register it with
   `BenchTask.fromGroupRunner`. The `BenchGroupInfo` you pass is authoritative
   for the key and title.
2. Call `runTimedSpec` with a `BenchSpec` record. There is no iteration count to
   choose — the preset's budget and the calibration ramp size the row.
3. Give the row a `workUnits` if it performs its operation more than once —
   see "Chained bodies" below — and a `digestClass` if the group carries more
   than one comparison. Every row of a group must agree on `workUnits`, and
   must agree on a digest *within* each class; either disagreement fails the
   run.
4. Set `digestIterations` to the **period of the body in its iteration index**,
   via `digestPeriod`: 1 for a `fun _ ↦ …` body, the pool size for a body that
   cycles one. It must never depend on the preset or on anything the machine
   decides, or the digest stops being comparable across runs and fixtures become
   impossible. Truncating to the period is not a weaker check — iterations past
   one full cycle recompute a bit-identical result.
5. Make the body depend on `i`, through a value built at run time. There are
   two ways to lose this and both have happened here. A body that is a *closed
   term* is evaluated once and cached, and the row then reports its true cost
   divided by `itersPerSample` — see finding 2 in `docs/bench-audit-2026.md` §12.6, and
   the plan-construction group, which reported 32 ns for two sizes that differ
   by 14x. A body that is merely *loop-invariant* can be shared with a value
   computed outside the loop: the NTT forward group precomputed its spectrum
   with the same expression the reference row then timed, and that row reported
   6 ns for a `2^12` transform. Indexing a small pool by `i` closes both.
6. Give every implementation in a digest class the same `checksum`, so the
   agreement check is meaningful.
7. Supply a `sink` if the default would allocate, and make the group's rows
   symmetric under the rule above.
8. Add the key to `bench/ci-groups.txt` to have it covered by the correctness
   gate and by the default selection of the on-demand timing workflow. An
   unknown key fails the run, so a rename is caught rather than dropped.
9. New modules under `bench/` need no `./scripts/update-lib.sh` run; that script
   globs `CompPoly/*.lean` only, and the lakefile globs `CompPolyBench`
   submodules.

## Chained bodies

A field operation is one or two nanoseconds and the harness floor is about
1.8 ns, so a body that performs it once per iteration reports the harness. The
combinators in `bench/CompPolyBench/Harness/Chain.lean` perform it `workUnits` times
per iteration instead, and the report divides, giving the **per-unit** cost.
Two chain shapes are reported, named as Plonky3 names them: *latency*, where
each operation depends on the last, and *throughput*, with ten independent
accumulators the pipeline can overlap.

Three properties of those combinators are load-bearing, and the obvious
alternative is measurably wrong in each case:

- **No array.** `Subtype` erases to its payload but `Array` does not inherit
  that: every element is a `lean_object*`, and `lean_box_uint64` allocates. A
  one-cycle dependent chain cannot be fed from a pointer array.
- **No `for` with `let mut`.** `ForIn` threads one state value, so ten mutable
  locals become a nested `Prod`, which does not erase — nine allocations per
  round.
- **The operation is a direct argument of an `@[specialize]` runner**, never a
  structure field and never a `[Field F]` projection. Through a closure it is
  an indirect call per operation, which is more than the operation.

Two consequences for a call site. Bind a captured constant to a local before
building the operation lambda: a projection inside it is lifted into the
operation and costs a load and an unbox per round. And take `workUnits` from
`latencyUnits` / `throughputUnitsOf` rather than from the depth you asked for,
since the chains run whole unrolled blocks and round a bad depth down.

**Read the emitted IR when adding a chain.** `.lake/build/ir/**.c` should show
the specialised loop taking unboxed scalar parameters with no `lean_alloc_*`
in the body. `harness-chain-linearity` catches a chain that is not executed at
all; it does not catch one that is partly folded, and a chain of a
`GF(2)`-linear operation folds completely — see the note on `chainFloorStep`
in `bench/CompPolyBench/Harness/SelfCheck.lean`.

## Where things live

| What | Where |
|---|---|
| Harness (timing, budgets, statistics, chains, self-check) | `bench/CompPolyBench/Harness/` |
| Group definitions, by library layer | `bench/CompPolyBench/{Fields,Univariate,Multivariate,Multilinear,Bivariate}/` |
| CLI, group registry, report and JSONL writers | `bench/CompPolyBench/Setup.lean`, `bench/CompPolyBench/Common.lean` |
| `--compare` (reader, verdicts, rendering) | `bench/CompPolyBench/Compare/` |
| A/B driver | `scripts/bench-ab.sh` |
| Curated CI set | `bench/ci-groups.txt` |
| CI workflows | `.github/workflows/lean_action_ci.yml`, `.github/workflows/benchmarks.yml` |
| Run output (ignored by git) | `bench/out/` |

## External comparison targets

There is no public cycle-count to cite. "Competitive with industry" means
**same operation, same size, same CPU** against a pinned peer, SIMD off.
The full argument is [`docs/bench-audit-2026.md` §13](../bench-audit-2026.md#13-external-comparison-targets).

| Layer | Peer | "On par" |
|---|---|---|
| BabyBear / KoalaBear / Goldilocks / Mersenne31 field ops, multiplicative NTT, RS encode | Plonky3 (scalar kernel) | within ~2–5× |
| Binary towers, `clMul` / BF64, additive NTT | Binius (scalar / packed-off) | within ~2–5×, at `log n` ≈ 13–16 |
| BN254 / BLS12-381 / Pasta `mul` / `inv` | arkworks or gnark-crypto | within ~2–5× |
| Gao decode, Guruswami–Sudan | none | no production peer; do not invent one |

Do not compare against packed AVX-512 numbers, whole-prover benches,
zkalc, ZPrize, or ePrint cycle tables. Beat-`ZMod` is necessary and not
SOTA.

## Known gaps

Recorded so they are not rediscovered. The audit and plan live in
`docs/bench-audit-2026.md`.

- A handful of rows are still `n=1`, all of them workloads whose single iteration
  exhausts its budget. They need smaller input shapes, decided per benchmark; no
  harness change reaches that.
- No result storage or CI regression gate for run-time benchmarks; only build
  timing gets that treatment. What exists is a same-machine comparison of two
  builds, `--compare` driven by `scripts/bench-ab.sh`, which needs no stored
  history because it runs both binaries turn about.
- Per-row floor subtraction is not reported, because the floor is
  per-representation rather than global.
- No polynomial-matrix groups, and no `batchInverse` / `sumOfProducts` /
  `dot_array` — Plonky3 benchmarks those and CompPoly does not have them yet,
  so the feature comes before the measurement. No prime-field `square` group
  either, deliberately: `square` is `mul x x` on every prime carrier here, and
  Plonky3 has no field-level `square` benchmark for the same reason.
- The polynomial-basis `GF(2^64)` of `CompPoly/Fields/Binary/BF64/` and its
  cubic extension have no group, and **cannot have one until a library bug is
  fixed**. `BF64.instFintype` (`CompPoly/Fields/Binary/BF64/Impl.lean:391`) is
  a closed constant whose value is a `Finset` of all `2 ^ 64` elements, and
  Lean evaluates closed constants at module initialisation — so any executable
  importing that module hangs before `main` runs. Elaboration never notices,
  because the interpreter forces constants on demand, which is why the tests
  build. Marking the instance `noncomputable` is not the fix: `Extension.Ext`
  takes `[Fintype F]` and its operations then stop compiling, so the repair is
  to `CompPoly/Fields/Extension/` rather than to the instance.
- No external yardstick yet. Peers and the "on par" bar live in
  [`docs/bench-audit-2026.md` §13](../bench-audit-2026.md#13-external-comparison-targets):
  measure Plonky3 (scalar, SIMD off) for the small fields and multiplicative
  NTT, Binius for towers and the additive NTT, arkworks / gnark-crypto for
  pairing scalars. "On par" means within ~2–5× of those *scalar* kernels on
  the same CPU, not packed AVX-512 or a whole-prover bench. Do not cite
  published cycle tables.
