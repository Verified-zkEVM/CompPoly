# Benchmarking

How the compiled benchmark suite measures, what its output means, and what to do
when adding a benchmark. [`bench/README.md`](../../bench/README.md) is the
operator's guide — invocation, presets, group selection, the group inventory.
This page owns the recurring guidance.

## Commands

```bash
lake build CompPolyBench
lake exe CompPolyBench --small                       # every registered group, timed
lake exe CompPolyBench --medium --validate-only      # correctness only, no timings
lake exe CompPolyBench --groups fields-goldilocks-mul
lake exe CompPolyBench --list                        # authoritative group keys
```

Output lands in `bench/out/`, which is created on demand and ignored in its
entirety. A checksum mismatch inside a group makes the executable exit nonzero
after writing its artifacts, and CI's validation step has no
`continue-on-error`, so a mismatch fails the run.

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

Record `name` is **not** unique — `extension-mul` is emitted by the ext4, ext5
and ext6 groups. Any tool comparing two result files must key on
`(name, field, input_shape)`.

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
   divided by `itersPerSample` — see finding 2 in `BENCHMARKING.md` §12.6, and
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
per iteration instead, and the report divides.

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

## Known gaps

Recorded so they are not rediscovered. The audit and plan live in
`BENCHMARKING.md` at the repo root.

- A handful of rows are still `n=1`, all of them workloads whose single iteration
  exhausts its budget. They need smaller input shapes, decided per benchmark; no
  harness change reaches that.
- No result storage, baseline comparison, or regression gate for run-time
  benchmarks; only build timing gets that treatment.
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
