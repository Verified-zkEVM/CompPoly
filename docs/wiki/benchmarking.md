# Benchmarking

How the compiled benchmark suite measures, what its output means, and what to do
when adding a benchmark. [`bench/README.md`](../../bench/README.md) is the
operator's guide — invocation, presets, group selection, the group inventory.
This page owns the recurring guidance.

## Commands

```bash
lake build CompPolyBench
lake exe CompPolyBench --small                       # every registered group
lake exe CompPolyBench --groups fields-goldilocks-mul
lake exe CompPolyBench --list                        # authoritative group keys
```

Output lands in `bench/out/`, which is created on demand and ignored in its
entirety. A checksum mismatch inside a group makes the executable exit nonzero
after writing its artifacts, and CI's benchmark step has no `continue-on-error`,
so a mismatch fails the run.

## The two passes

Every benchmark body is executed twice, for different purposes, and confusing
them is the main way benchmark numbers go wrong.

The **validation pass** is untimed. It folds a strong `Nat` digest over the full
result, and it is what the cross-implementation agreement check compares. This is
why a wrong-but-fast implementation cannot be benchmarked here. It is capped at
`validationIterationCap` iterations and counts towards warmup, since it has
already executed the body.

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
2. Give every implementation in the group the same `checksum`, so the agreement
   check is meaningful.
3. Supply a `sink` if the default would allocate, and make the group's rows
   symmetric under the rule above.
4. Add the key to `BENCH_CI_GROUPS` in
   [`.github/workflows/lean_action_ci.yml`](../../.github/workflows/lean_action_ci.yml)
   if CI should run it. An unknown key fails the run, so a rename is caught.
5. New modules under `bench/` need no `./scripts/update-lib.sh` run; that script
   globs `CompPoly/*.lean` only, and the lakefile globs `CompPolyBench`
   submodules.

## Known gaps

Recorded so they are not rediscovered. The audit and plan live in
`BENCHMARKING.md` at the repo root.

- 67 rows are still `n=1`, all of them workloads whose single iteration exhausts
  its budget. They need smaller input shapes, decided per benchmark.
- Iteration counts are still hand-tuned `selectNat` triples rather than wall-clock
  budgets, so `Total` is not comparable between rows of one table.
- No result storage, baseline comparison, or regression gate for run-time
  benchmarks; only build timing gets that treatment.
- Per-row floor subtraction is not reported, because the floor is
  per-representation rather than global.
- Coverage gaps against the roadmap: no standalone multiplicative NTT/iNTT group,
  no base-field microbenchmarks outside Goldilocks, no `add`/`square`/batch-inverse,
  no Reed-Solomon or polynomial-matrix groups.
