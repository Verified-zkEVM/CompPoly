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
arrive as a PR comment and an artifact. Fork PR runs publish the report in the Actions summary and artifact without attempting a comment with their read-only token. Ordinary PR comments do not cancel active benchmark jobs; concurrency applies only after the benchmark job's comment filter.

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
iteration; the implementation's tests and the digest gate first, `bench-ab.sh run` as
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
each operation depends on the last, and *throughput*, with parallel accumulators (two for BN254, ten for other fields).

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
- External comparisons beyond the small-field suite below remain to be added. Peers and the "on par" bar live in
  [`docs/bench-audit-2026.md` §13](../bench-audit-2026.md#13-external-comparison-targets):
  measure Plonky3 (scalar, SIMD off) for the small fields and multiplicative
  NTT, Binius for towers and the additive NTT, arkworks / gnark-crypto for
  pairing scalars. "On par" means within ~2–5× of those *scalar* kernels on
  the same CPU, not packed AVX-512 or a whole-prover bench. Do not cite
  published cycle tables.

## Fields against Rust

`python3 scripts/bench-fields.py --suite all --cpu 0` compares selected Lean groups with pinned Rust libraries. `--suite small-prime` covers KoalaBear, Mersenne31, and Goldilocks against Plonky3; `--suite large-prime` covers BN254 scalar add/mul latency and throughput, plus inv/exp latency, against arkworks. `--suite binary` covers 8-, 64-, and 128-bit Fan–Paar tower mul latency/throughput and square/inv latency against pinned Binius. `all` selects the 36 scalar cases and the one-polynomial evaluation suite. The default suite is `small-prime`. Choose an available logical CPU with `--cpu` for scalar workloads; use `--cpus` for polynomial workloads. Lean and Rust are measured sequentially.

The driver exports fixed-width little-endian coordinate byte inputs with an explicit basis from Lean and checks cross-language result digests and operation counts before timing. BN254 is explicitly matched to arkworks `Fr` by its modulus. Input decoding and canonical result checks are outside timing. See [the benchmark README](../../bench/README.md#rust-field-comparison) for field correspondence, pinned versions, and workload details.

Five paired runs alternate executable order. The output directory under `bench/out/` contains two compact tables in `report.md`, raw samples, exact inputs, and machine/toolchain metadata. Tables report the median of run medians and the median absolute deviation between runs. These are same-machine library comparisons, not historical regression comparisons; other workloads on the host can affect them.

`--validate-only` skips timing, and CI uses it with `--suite all` on every PR. `--skip-build` requires a matching build record from a previous driver run.

BN254 add/mul throughput uses two independent chains with the same fixed second operand as latency, 160 steps per lane (320 operations total), four rounds unrolled per loop, and one final combining operation excluded from the divisor. This avoids the ten-lane ring’s excessive live state for multi-limb values. Small-prime throughput retains its ten-lane ring.

The BN254 throughput configuration was selected manually on Rust, then fixed identically in Lean. It is not selected independently per language or tuned during benchmark runs. Rust screening covered 1, 2, 3, 4, 6, and 8 lanes with 1, 4, and 8 rounds unrolled; two lanes avoided the spill overhead of wider configurations. Shortlisted unroll factors were checked again in the production Rust runner.

### Eight-limb BN254 kernel optimization

The checked binary-GCD inverse uses native `Int64` transition coefficients inside each divstep chunk, converting to `Int` at the chunk boundary. The integer kernel remains available for the coefficient-bound proofs and regression comparisons. The native candidate still passes the same boundedness, canonicality, and multiplication checks before use; the proved Fermat fallback handles a rejected candidate.

On the Ryzen 7 3700X, pinned to CPU 11, five interleaved `--small` A/B rounds against `76f4a91` measured inversion at 0.915× baseline time (8.14 → 7.44 μs per chain step), with matching digests and no `SUSPECT`. All 4,096 inversion inputs in the comparison workload accepted the native candidate. These host-specific observations do not update the separate M3 reference-machine best-time tables.

Conditional reduction compares bounded limbs from the most significant end and stops at the first difference. The five-pair BN254 A/B run against the signed-word-inversion baseline measured multiplication throughput at 0.883× baseline time (65.64 → 57.95 ns/op), with no judged regressions in the other BN254 rows.

Binary exponentiation calls the inline `square` directly, exposing equal operands to code generation while retaining the definitionally equal binary-recursion algorithm. Five interleaved A/B rounds against `7c0bcd7` measured exponentiation at 0.916× baseline time (2.74 → 2.51 μs per chain step), with no `SUSPECT` or other row classified as slower.

Compact eight-`UInt32` storage, branch-free reduction, reversed multiplication operands, and borrowed-operand kernels were also screened. None was retained: compact storage improved addition but slowed multiplication, branch-free reduction regressed other operations, and the operand variants offered no reliable improvement.

### Four-limb BN254 kernel optimization

The Rust-comparison branch incorporates PR #391's four-limb, radix-`2^64` carrier. The benchmark workloads, lane counts, and cross-language operation counts remain unchanged. The eight-limb measurements above describe the preceding implementation, not the current carrier.

The four-limb checked inverse reuses the native `Int64` divstep kernel. Five interleaved A/B rounds against merge commit `856f88e` measured inversion at 0.896× baseline time (6.75 → 6.05 μs per chain step), with no `SUSPECT` or other row classified as slower. The canonicality and multiplication checks and the proved Fermat fallback remain in place.

Standalone multiplication screening compared swapped high-product operands, balanced partial-product sums, reordered carry accumulation, reassociated high-word additions, lexicographic final reduction, and reconstruction of a carry from the low product. Every variant checked 1,024 input pairs against the original kernel before timing. None showed a sufficient improvement to adopt; the reassociation gave only about 2–3%, while reconstructing the carry lengthened the dependency chain and slowed multiplication. These screening results do not replace the matched Lean/Rust measurements.

The previous explicit-squaring exponentiation change was ported and tested in two forms. Inlining `square` regressed the exponentiation row to 1.164× baseline time; a separately specialized `square` measured 1.013× and was classified as unchanged. Neither was retained. The four-limb implementation keeps its original binary-exponentiation definition.

### Addition ownership

The four-limb BN254 addition chain originally tried to reuse its shared fixed operand. Generated code allocated a new result and released the old accumulator at every step. Specializing `FastField.add` while explicitly borrowing its second operand makes the first operand available for reuse. The benchmark loop then passes the accumulator onward without per-step reference-count increments or releases; only a shared input requires allocation.

Five interleaved A/B rounds against `4502b00` measured addition latency at 0.382× baseline time (13.13 → 5.01 ns/op) and the two-lane row at 0.445× (12.27 → 5.46 ns/op), with no `SUSPECT` or other BN254 row classified as slower. This changes ownership and code generation, not field arithmetic or the matched benchmark workloads. The field carrier still lives in a heap object; reusing it does not give the register-only representation available to Rust.

### One-bit carry encoding

The four-limb `adc` and `sbb` helpers combine their overflow flags with bitwise OR. With a one-bit incoming carry or borrow, at most one flag can be set; the word-level specifications prove the same exact sum/difference identities and one-bit output bounds. OR makes the output bit range visible to native code generation, avoiding the extra arithmetic needed when the two flags are added. The multiply-accumulate helper keeps addition because both of its overflow flags may be set.

Five interleaved A/B rounds against `17a1eb9`, on the same Ryzen 7 3700X pinned to CPU 11, measured addition latency at 0.773× baseline time (5.06 → 3.91 ns/op) and the two-lane row at 0.780× (5.50 → 4.29 ns/op). All digests matched, with no `SUSPECT` or other BN254 row classified as slower. The benchmark harness and matched Rust workloads are unchanged.

Additional `inline`, `always_inline`, and `macro_inline` variants were screened but not retained: none reliably improved the borrowed, specialized addition boundary, and inlining the original operand order brought back per-step allocations. A standalone scalar-state control removed per-step calls and allocations but still took about 4.4 ns with the old carry encoding, versus about 5 ns for the ordinary chain. This isolates a substantial arithmetic/code-generation cost beyond object handling; it is a diagnostic, not a replacement benchmark result.

### Spare-bit addition and scalar diagnostics

For moduli below `2^255`, the four-limb addition now omits the impossible carry out of the top limb. The modulus's top bit selects the path; specialization resolves it for concrete fields. The correctness proof uses canonical input bounds to establish that the carry is zero. Full-width moduli retain the carry-aware path.

Five interleaved A/B rounds against `b69a497` measured BN254 addition latency at 0.904× baseline time (3.86 → 3.49 ns/op) and the two-lane row at 0.897× (4.23 → 3.80 ns/op). All digests matched, with no `SUSPECT` or other BN254 row classified as slower. No benchmark workload changed.

Assembly inspection identified a further difference from arkworks: arkworks compares against the modulus before subtracting, whereas the retained Lean addition calculates the difference before choosing the result. An ignored scalar-state diagnostic using the same 320 additions and fixture inputs reached approximately 1.77 ns/op by combining the spare-bit optimization with comparison before subtraction. It keeps limbs in scalar loop parameters and has no per-addition calls or field objects. This is a screening result, not the ordinary field API or a replacement row in the Lean/Rust report.

The corresponding ordinary-API variants were not retained. Conditional subtraction introduced allocation on the reduction branch; moving construction after a tuple-valued branch, changing operand order, masking the modulus, and extracting subtraction into a separate function failed to beat the retained implementation. Thus the scalar diagnostic demonstrates arithmetic close to Rust, while obtaining it through the boxed field API remains open.

### Scalar limb API for specialized hot loops

`Montgomery.Native64x4.Scalar` in `CompPoly/Fields/Montgomery/Native64x4Defs.lean` exposes `add`, `sub`, `mul`, and `square` with separate `UInt64` limb arguments. These are inline entry points to the existing verified arithmetic, with the same input bounds and Montgomery representation. The first four arguments are the modulus limbs; multiplication and squaring also take the Montgomery negative inverse. Results are four-word tuples.

Immediately destructure each result and carry its words as separate loop parameters. Construct a `Limbs4` or field value at the boundary. For example, a multiplication step inside such a loop is:

```lean
let (r0, r1, r2, r3) := Montgomery.Native64x4.Scalar.mul
  q0 q1 q2 q3 negInv a0 a1 a2 a3 b0 b1 b2 b3
-- Continue with r0, r1, r2, r3 as separate scalar parameters.
```

The arguments are little-endian Montgomery residues, not canonical integers. Obtain the modulus limbs and negative inverse from `Mont64x4Field`; unpack existing fast field values through their `.val` limbs. Reconstructing a field value also requires the usual proof that the residue is below the modulus. The wrappers unfold directly to the existing operations, so their bounds and refinement lemmas remain applicable.

Inlining and immediate destructuring allow the compiler to eliminate the intermediate tuples and limb objects. Storing the tuple as the loop state, passing it through a non-inlined function, or calling through an unspecialized function argument can reintroduce boxing. Inspect generated code and measure the actual loop: eliminating allocations can still lose to register spills or code layout, particularly for multiplication.

A complete repeated-squaring loop illustrates the state layout:

```lean
open Montgomery.Native64x4

def repeatedSquare (q : Limbs4) (negInv : UInt64) (n : Nat) (x : Limbs4) : Limbs4 :=
  let rec go (n : Nat) (x0 x1 x2 x3 : UInt64) : Limbs4 :=
    match n with
    | 0 => ⟨x0, x1, x2, x3⟩
    | n + 1 =>
      let (s0, s1, s2, s3) := Scalar.square q.l0 q.l1 q.l2 q.l3 negInv x0 x1 x2 x3
      go n s0 s1 s2 s3
  go n x.l0 x.l1 x.l2 x.l3
```

Exponentiation was tested as a possible production example, with three scalar-state variants. Against `7912071`, five interleaved A/B rounds per variant measured the binary-recursion version at 1.079× baseline time (1.85 → 2.00 μs), explicit right-to-left tail recursion at 1.042× (1.88 → 1.96 μs), and left-to-right recursion with a fixed base at 1.077× (1.87 → 2.01 μs). All BN254 digests matched. None was retained: the existing `FastField.pow` remains the production implementation. The scalar API makes unboxed loops expressible, but the multiplication-heavy exponentiation experiments did not establish a speedup.

### Dedicated four-limb squaring for exponentiation

The next BN254 pass screened dedicated squaring, scalar loop layouts, native-word exponents, and windowed exponentiation. Sharing the ten distinct limb products across the original four CIOS rounds was the winning square implementation. A full-product Comba square also helped in isolation, but less; special diagonal-product formulas regressed relative to ordinary `mulHi`. The retained `squareCached_eq_mul` theorem proves exact equality to the original multiplication for arbitrary limb inputs, and the field-level compiler rewrite preserves the original binary-exponentiation specification.

Five interleaved production A/B rounds against `a4dd24a` measured BN254 exponentiation at 0.928× baseline time (1.863 → 1.729 μs per chain step), classified `faster` without `SUSPECT`. The fast add, multiply, and inversion rows were classified unchanged. Inputs, exponent, chain length, and benchmark code stayed unchanged.

Four additional scalar loop layouts varied whether multiplication and squaring were inlined or outlined. All lost to the boxed control in the standalone screening. The fully inlined loop had a 280-byte stack frame, compared with 120 bytes in the boxed multiplication routine, consistent with register pressure from keeping both four-word states live. These are static assembly observations, not a measured attribution of cycles: hardware performance counters were unavailable to this user. Array-based windows of widths two through five and a width-three version with explicit table entries also lost. A native-word exponent alone gave only a small screening improvement. Screening results were used to choose production candidates, not as replacements for the matched Lean/Rust benchmark.

A second retained change skips the initial multiply-by-one and the last unused square, without narrowing the natural-number exponent. Against the dedicated-square baseline, five production A/B pairs measured 0.922× time (1.757 → 1.619 μs), again `faster` without `SUSPECT`. Both loops are proved against field exponentiation through `toField` for every natural-number exponent. The two A/B ratios compound to about 14% less exponentiation time.

### Parameter boundaries for canonical four-limb arithmetic

The BN254 lazy-evaluation investigation also exposed an issue in ordinary canonical multiplication: embedding modulus words prevented Clang from recognizing widening products in Montgomery reduction. `FastField.mulKernel` and `FastField.squareKernel` keep those words dynamic across `@[noinline]` boundaries. The underlying `Native64x4` and `Scalar` APIs remain inlineable for custom loops. Arithmetic, canonical reduction, and the existing correctness theorems are unchanged; the field proofs unfold the new wrappers.

Five alternating A/B pairs against `45d6384` on CPU 9 of the Ryzen 7 3700X, using the medium preset and unchanged benchmark workloads, measured:

| BN254 operation | Before | After | Time reduction |
| --- | ---: | ---: | ---: |
| Multiplication latency | 35.01 ns/op | 20.86 ns/op | 40.4% |
| Multiplication throughput workload | 35.10 ns/op | 22.52 ns/op | 35.9% |
| Exponentiation chain step | 1.617 μs | 0.985 μs | 39.1% |
| Inversion chain step | 5.763 μs | 5.713 μs | Classified unchanged |

Both multiplication rows and exponentiation were classified `faster`. Across BN254 and multiplication in BLS12-381 scalar, BLS12-377 scalar, secp256k1 scalar and secp256k1 base, the comparison judged 30 rows: 11 faster, 19 unchanged, none slower, no digest mismatch or `SUSPECT`. Harness drift stayed within 3%. The other fields' fast multiplication rows all improved. These are measurements on this Linux host, not replacements for the Apple reference-machine best-times table.

The final multiplication kernel contains 32 widening multiplies and four low-word multiplies; the symmetric square contains 26 widening multiplies and four low-word multiplies. Neither contains partial-product shifts. An isolated earlier experiment changing multiplication alone reduced exponentiation time by 12.5%; adding the squaring boundary then reduced it by another 30%. Final figures above compare both boundaries directly against the original executable. No compiler flags, external functions, benchmark schedules or lazy-reduction rules changed.

### Goldilocks kernels from PR #392

The benchmark branch incorporates [PR #392](https://github.com/Verified-zkEVM/CompPoly/pull/392). Goldilocks uses a revised wide-product expression, a separate cold borrow path in reduction, shift/subtract for the reduction's middle term, and subtraction-based canonical addition. Inversion and exponentiation keep congruent, potentially noncanonical words inside the chain and canonicalize once at the end. The carrier and public field operations remain canonical. The PR's KoalaBear/BabyBear `conditionalSubtract` inlining was already present on this branch.

Five interleaved A/B pairs on CPU 11 of the Ryzen 7 3700X compared `79a3ea0` with merge `770f992`, using the unchanged field-operation workloads:

| Goldilocks operation | Before (ns/op) | After (ns/op) | After / before |
| --- | ---: | ---: | ---: |
| Add latency | 1.268 | 0.747 | 0.589 |
| Add throughput | 0.667 | 0.341 | 0.512 |
| Mul latency | 3.771 | 3.154 | 0.836 |
| Mul throughput | 1.200 | 1.262 | 1.052 |
| Inversion | 432.806 | 183.945 | 0.425 |
| Exponentiation | 146.258 | 89.556 | 0.612 |

Multiplication throughput regressed; a second five-pair run confirmed 1.180 → 1.239 ns (1.050×). The other Goldilocks rows were classified faster. Addition throughput also received `SUSPECT: below chain floor`: the current comparer selects the latency chain floor for every row, including throughput. KoalaBear addition throughput, whose implementation was unchanged, received the same flag. This flag remains a limitation of that A/B result; the harness was not changed to remove it.

A separate five-pair Lean/Rust run on clean `770f992` passed all 24 result checks. Goldilocks measured 0.99× Rust's time for add latency, 1.28× for mul latency, 0.44× for inversion, and 0.87× for exponentiation; throughput ratios were 0.59× for add and 1.45× for mul. All timings include the same operations and use the same inputs in both languages. Local artifacts are in `bench/out/goldilocks-pr392-20260930/` and A/B runs `bench/out/ab/260930-135904/` and `bench/out/ab/260930-140026/`.

## Parallel evaluation at one point

`python3 scripts/bench-fields.py --suite poly-eval --cpus 1,2,3,4` compares single-core `CPolynomial.evalHorner` and multicore `CPolynomial.evalFast` against matched Rust algorithms, for one polynomial at one point. The suite uses 2^12, 2^16 and 2^20 coefficients over KoalaBear, Goldilocks, BN254 scalar and the 128-bit binary tower. It is included in `--suite all` and its validation-only CI gate. The benchmark defaults to sixteen workers, capped by available logical CPUs (physical cores first, then SMT siblings); `--cpus` overrides the selection. `evalFast` defaults to sixteen blocks (`logWorkers = 4`).

`CompPoly/Univariate/EvalFast.lean` implements a task dependency tree over zero-copy array ranges. A semiring-level proof equates it to `evalHorner` and `eval`. All leaf arithmetic, partition boundaries and power schedules match Rust. See [the benchmark operator guide](../../bench/README.md#one-polynomial-at-one-point) for timing boundaries, worker selection and fixture format. This suite does not measure many-polynomial evaluation, multipoint evaluation or FFTs.

### Lazy polynomial-evaluation leaves

`CompPoly.Univariate.EvalFastFields` installs proved `EvalKernel` instances for KoalaBear, Goldilocks and BN254 scalar. Parallel leaves defer normalization using field-specific bounds, then return canonical values for the shared power/join tree. Both languages implement the same leaf arithmetic; Rust's parallel evaluator uses custom lazy kernels with Plonky3/arkworks carriers. The sequential `evalHorner` baseline and binary-field leaves are unchanged. See the [polynomial benchmark instructions](../../bench/README.md#one-polynomial-at-one-point) for the execution model and timing boundaries.

BN254's lazy leaf uses scalar accumulator parameters and machine-word indices. Its modulus stays a parameter across a `@[noinline]` loop boundary so Clang can recognize the widening-product pattern in Montgomery reduction. Keep this boundary when refactoring; check generated machine code and paired measurements before embedding constants or inlining the loop. This changes code generation, not the arithmetic schedule shared with Rust.

### Optimized Plonky3 NTT comparison

`python3 scripts/bench-fields.py --suite ntt` compares the proved KoalaBear `NTTFast.NaturalPlan` forward/inverse transforms against the existing optimized `p3_dft::Radix2DFTSmallBatch` API, at 2^12, 2^16 and 2^20 elements. Plonky3 uses native packed arithmetic and its parallel feature. The default budget is sixteen workers, capped by available logical CPUs (`--cpus` overrides it; `--cpu` selects one worker). Both sides receive the same CPU allocation; the existing Lean plan remains sequential. Plans are outside timing. Input copying, ordering conversions and inverse normalization are timed. Both APIs use natural-order arrays and the same root; Lean's bit-reversal adapter is therefore part of the measured cost. Different algorithms and arithmetic schedules are allowed in this library comparison, replacing the original custom scalar Rust baseline. This suite is included in `--suite all` and CI validation. See [the operator guide](../../bench/README.md#koalabear-ntt-against-optimized-plonky3) for fixtures, validation and timing boundaries.

### Lean natural-order NTT plans

Import `CompPoly.Univariate.NTTFast.Natural` and construct `NTTFast.NaturalPlan.ofDomain domain` once, then call `plan.forward input` or `plan.inverse input`. The plan caches bit-reversal indices as well as the existing twiddle tables. Its forward path reuses correctly sized inputs until the first copy-on-write update; shorter inputs are zero-padded and longer ones truncated. Bit reversal swaps each pair once in the working array instead of gathering a second array; a shared input still receives the required copy-on-write copy. Normalization uses a specialized scalar loop. Both operations are proved equal to the existing natural-order pipelines for every input array.

The optimized loops are selected explicitly through the new plan. Importing it does not register `csimp` replacements for the existing `NTTFast.Plan.forwardImpl` or `NTTFast.Plan.inverseImpl` entry points; their equivalence theorems remain ordinary proofs.

The butterfly modules expose bounds-proved loops selected by the natural-order plan. Array ranges are checked once per complete radix-four stage, and the hot traversal uses `USize` indices. The quarter-one stage checks its unit twiddles once and omits their multiplications; these fast entry points require `DecidableEq R` for that check. The original total functions cover invalid ranges, and natural-number indexing covers ranges exceeding the machine-word limit. No new external functions or compiler changes are used. The NTT benchmark executable targets the native CPU, matching Rust's native targeting; the library retains portable build settings.

The retained Lean implementation is sequential. Experiments with per-stage parallel gathering, recursive task splitting, byte-packed storage, two-lane software arithmetic, and sixteen-element blocks did not close the large-transform gap. The block prototype generated AVX2 instructions, but packing, allocation and sharing costs limited the gain; it is not part of the verified implementation. Plonky3 combines packed arithmetic with cache-local groups of layers and parallel mutable slices. A competitive Lean parallel version needs to address the storage and data-movement costs together with the butterfly schedule.

### NTT storage and compiler investigation (2026-10-02)

Follow-up experiments on Lean 4.34.0 separated storage costs from field arithmetic. These are engineering diagnostics, not new verified library implementations. The first experiment below used the verified `51bb43a` implementation as its control; the Rust executable remains frozen from `8a34661`. The subsequent in-place permutation improvement and further experiments are recorded below.

**Generic arrays do not allocate one object per KoalaBear value on this 64-bit host.** The subtype proof is erased and `UInt32` is a tagged immediate in an eight-byte array slot. Rust stores four-byte field values contiguously. The sixteen-lane prototype instead puts sixteen native `UInt32` fields in a heap record; this enables vectorization but introduces record allocation and sharing costs. See Lean's [`lean_box_uint32`, array accessors and exclusivity check](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/include/lean/lean.h).

The blocked prototype spent approximately 8–11 ms unpacking a million-element result in phase screens. Borrowed reads, compact permutation tables, fixed-lane gathers, parallel unpacking, local conversion before task joins, and cached leaf twiddles did not produce a decisive improvement. Whole-transform screens remained around 31–35 ms. These phase measurements include memory traffic and indexing; they do not isolate a single instruction cost.

A separate byte-buffer prototype tested native 32-bit reads, batch stores, and appends while keeping all field arithmetic in Lean. The table below isolates the append change: both experimental variants use the same word reads, bounds handling, sixteen-way unrolled butterflies, batch stores and sixteen-task schedule. Only one appends each word with four existing byte pushes; the other appends a word with one capacity/ownership check and a four-byte store, falling back to the byte pushes when necessary.

Million-element complete transforms, milliseconds; median of five alternating run rounds ± between-run MAD. Ryzen 7 3700X, 8 physical cores / 16 logical CPUs, same CPU allocation and fixtures for all variants; shared host. Full output digests matched the frozen Rust executable before and during timing. Conversion, copying, output ordering and inverse normalization are included; plans are excluded.

| Implementation | Forward | Inverse |
|---|---:|---:|
| Retained verified Lean | 43.860 ± 0.151 | 48.450 ± 0.208 |
| Experimental native storage, four byte appends | 49.498 ± 0.816 | 51.128 ± 1.714 |
| Experimental native storage, one word append | 31.233 ± 0.215 | 30.711 ± 0.726 |
| Frozen parallel SIMD Plonky3 | 3.355 ± 0.016 | 3.299 ± 0.017 |

The word append reduces this prototype's time by 37–40%, but leaves it roughly nine times slower than Plonky3. The native prototype has no full FFT refinement proof, and its word-copy implementation was only tested on this little-endian host. It is not installed in the library or the default benchmark. In that first experiment, native storage alone did not establish vectorized arithmetic: the sixteen-way byte-buffer inner loop did not emit the AVX2 arithmetic seen in the scalar-record prototype. A scalar byte-buffer screen with the word append also took about 31 ms.

Two compiler/runtime findings guide further work:

- **Record reuse depends on code shape.** A small scalar-record update reuses its allocation, while the large butterfly's generated C allocated new records. Splitting the update into smaller non-inlined record-update helpers enabled reuse, but the extra calls, moves and private copies made the complete transform slower. Better scalar replacement and reuse across larger expressions are compiler investigation targets; no minimal compiler fix or Rust-parity result has been established. The relevant compiler passes are [`ResetReuse`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Compiler/LCNF/ResetReuse.lean) and [`InferBorrow`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Compiler/LCNF/InferBorrow.lean).
- **Multithreaded objects are not considered exclusive.** `lean_is_exclusive` returns false for objects marked multithreaded, even when a later reference count might suggest a sole owner. This matters for mutation/reuse of records crossing task boundaries. An ownership-preserving task handoff could help, but shared reachable objects make it a runtime design problem; clearing the flag is not a safe shortcut.

There was also a source-level specialization trap: placing `@[specialize]` on a concrete unpacking wrapper with no higher-order parameters left a generic callback in its element loop. Removing that annotation allowed the inner array builder to specialize and removed a large experimental regression. The [`Specialize` pass](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Compiler/LCNF/Specialize.lean) explains that annotated bodies defer specialization to their call sites. Use the attribute on the higher-order builder, and inspect the resulting loop; it is not a blanket request to optimize any function.

The most concrete small runtime extension is a packed UInt32 buffer API with proof-bounded reads, word appends and batch updates that check ownership once. It would remove repeated byte operations without moving field arithmetic into C. Achieving Plonky3-like performance still needs vectorizable kernels, cache-local layers and cheap partitioning of work; none of the measurements establishes that a single extern or compiler patch solves the full gap.

### In-place permutation and vectorized storage follow-up

The verified natural-order plan now swaps each bit-reversed pair once in its working array. A generic `Array.permuteInvolution_eq_map` theorem proves agreement with gathering for bounded involutive index tables; bit-reversal involution instantiates it. Inputs of other lengths retain the previous padding/truncation behavior. The arithmetic and Rust implementation are unchanged, and this improvement uses existing Lean primitives only.

Five alternating single-worker rounds on CPU 9 compared the swap implementation against `51bb43a`. Complete-transform medians in milliseconds:

| Elements | Direction | Previous gather | Pair swaps | New / old |
|---:|---|---:|---:|---:|
| 4,096 | forward | 0.0941 | 0.0929 | 0.988 |
| 4,096 | inverse | 0.1102 | 0.1116 | 1.013 |
| 65,536 | forward | 1.9714 | 1.8191 | 0.923 |
| 65,536 | inverse | 2.2476 | 2.1392 | 0.952 |
| 1,048,576 | forward | 44.6186 | 37.6438 | 0.844 |
| 1,048,576 | inverse | 48.4924 | 43.3625 | 0.894 |

The repository comparer classified three rows faster and three unchanged, with no slower, mismatched or suspect rows. These transform records do not include harness floor/drift rows, so those checks were unavailable. After proving and integrating the change into `NaturalPlan`, a separate three-pair check reproduced the gains (million-point new/old ratios 0.825 forward and 0.923 inverse on the shared host).

The native-storage experiment also advanced beyond the earlier 31 ms prototype. Moving `Nat`→`USize` conversions outside the sixteen-lane butterfly kernel enabled AVX2 arithmetic: the earlier machine code had 116 big-Nat conversion call sites and no vector multiplies; the machine-index kernel had 42 vector-multiply instructions. Batched sixteen-word partition appends and a 4×16 tiled output permutation reduced data-movement costs. All field arithmetic still comes from Lean; the experimental externs provide word storage operations and batched array output writes.

A separate five-round interleaved comparison, sixteen workers on the same host, gave these million-point complete-transform medians ± between-run MAD:

| Implementation | Forward (ms) | Inverse (ms) |
|---|---:|---:|
| Verified `51bb43a` control | 43.872 ± 0.289 | 48.018 ± 0.458 |
| Experimental vector kernel and batched partitioning | 21.903 ± 0.159 | 22.155 ± 0.084 |
| Same experiment with 4×16 tiled output permutation | 15.976 ± 0.303 | 17.592 ± 0.598 |
| Frozen Plonky3 | 3.341 ± 0.026 | 3.314 ± 0.008 |

All full-output digests matched. These native prototypes remain outside the library and default benchmark: they lack a complete FFT refinement proof, and their word-copy externs were only exercised on the little-endian host. They narrow the measured gap to about 4.8–5.3×, without establishing Rust parity. A larger 16×16 output tile and an eight-lane kernel did worse in their screens; replacing conditional normalization with unsigned minimum did not improve the paired timings. Constant-twiddle transform variants were inconclusive because host contention rose during their screens.

A bounds-proved packed-buffer read can avoid the conversion problem without a compiler change: its byte-size bound implies that the `Nat` index is a tagged immediate, allowing direct unboxing as in existing bounded array accessors. This version also generated vector multiplies and was within 2–4% of the explicit `USize` prototype in a three-pair single-worker check. The bound is essential; directly unboxing an arbitrary `Nat` would be incorrect.

A separate diagnostic copied the Lean runtime header into a temporary compiler overlay. Marking the read-only big-Nat conversion `pure` alone did not change code generation. Also outlining its small-Nat wrapper enabled vectorization and reduced the Nat-indexed prototype's time by about 8–10%, but remained slower than using `USize` in the source. This is not a validated general-purpose runtime patch. Neither the installed toolchain nor the committed build settings were modified. The most direct extension remains proof-bounded packed UInt32 storage with batched ownership checks, paired with vectorizable Lean kernels and cache-conscious data movement.

### Four/eight-core follow-up and fused final layers

Further native-storage experiments used four physical cores (CPUs 2–5) or eight (CPUs 0–7), without SMT siblings. Sixteen leaf tasks stayed fixed. Four cores gave a steady final run of the verified library, but did not eliminate contention in every prototype run; the eight-core inverse comparison became substantially noisier as other work increased.

The strongest new prototype fuses the last four FFT layers into a sixteen-coefficient kernel. Values stay in scalar locals between layers, and multiplications by unit twiddles are omitted. The previous prototype reread and rewrote the buffer between those small layers. All field arithmetic is still Lean; storage uses the earlier experimental word primitives. Full-output digests matched Plonky3 and the previous implementation at all eight validation sizes, in both directions.

Five alternating rounds per core allocation, million-element complete transforms, milliseconds ± between-run MAD:

| Physical cores | Direction | Previous native prototype | Fused final layers | Frozen Plonky3 | Fused / Rust |
|---:|---|---:|---:|---:|---:|
| 4 | forward | 30.290 ± 2.386 | 20.769 ± 1.897 | 6.618 ± 0.176 | 3.14× |
| 4 | inverse | 36.738 ± 2.443 | 25.196 ± 1.736 | 7.136 ± 0.923 | 3.53× |
| 8 | forward | 24.684 ± 1.027 | 15.164 ± 1.348 | 4.143 ± 0.052 | 3.66× |
| 8 | inverse | 42.291 ± 7.754 | 37.584 ± 4.611 | 5.347 ± 1.221 | 7.03× |

The four-core repository comparison classified both rows faster, with strict separation of all five baseline/candidate runs, matching digests and no suspect rows. Its harness floor/drift checks were unavailable. The eight-core forward runs also separated strictly; inverse runs overlapped across changing host load. The four- and eight-core measurements were separate runs, so their absolute differences are not an isolated scaling experiment. The native FFT still lacks a complete refinement proof and is not installed in the library or default runner.

Several narrower experiments did not earn a retained change. Keeping task outputs as separate leaf buffers removed concatenation copies, but its forward results were inconsistent. Batched input conversion improved forward by only about 1%. Reading each word using four bounds-proved `ByteArray.uget` calls produced expensive vector byte shuffles and was 3–4× slower than the word-read prototype in its three-pair screen; delaying Lean inlining did not recover the word-read performance. This gives a concrete reason to investigate a dedicated word-read primitive rather than assuming the byte operations will combine efficiently in the vectorized kernel.

Precomputed [Shoup-style multiplication](https://www.libntl.shoup.net/doc/ZZ.cpp.html) for fixed twiddles reduced wide vector-multiply instructions in the large kernel from 48 to 16, but did not improve complete-transform performance. It enlarged the twiddle tables and changed the kernel's register demands; those costs were not isolated. An eight-lane Shoup kernel also regressed forward in its screen. Using Shoup only in the fused small kernel improved forward by about 9% in three pairs, while inverse was unchanged; this was not taken through a five-round gate. The selected prototype keeps Montgomery arithmetic.

A fresh standard-driver run on clean `58d39a7`, four physical cores, measured the verified library at 36.851 ± 0.132 ms forward and 43.037 ± 0.121 ms inverse for a million points; Plonky3 measured 7.003 ± 0.278 and 6.770 ± 0.151 ms respectively. These verified results are separate from the native prototypes. Reproduce with `python3 scripts/bench-fields.py --suite ntt --cpus 2,3,4,5`. No Rust source, build flags or executable changed during the experiments. The next implementation work is a packed storage API with explicit word reads and batched updates, and refinement proofs for the fused transform.


### NTT extern minimization (2026-10-02)

The selected packed-storage prototype now uses two new externs, totaling 774 bytes of inline C, down from eight and 7,414 bytes. One reads a UInt32 word with checked or proof-bounded indexing; the other writes or appends up to sixteen words, checking bounds, ownership and capacity once. Nat-indexed fallback reads/writes use Lean definitions, and a bounds-proved Lean output-store loop replaces the field-array extern. Its guard uses unsigned comparisons with a kernel-checked no-wrap lemma, avoiding big-Nat bounds checks in the common path. The remaining arithmetic and transform logic are Lean.

A four-physical-core comparison gave the following million-point times, milliseconds; medians of seven alternating rounds. Both parallel implementations had four workers, and the native prototype kept sixteen leaf tasks. The verified implementation remains sequential.

| Elements | Direction | Plonky3 | Verified Lean, no new externs | Lean prototype, 2 externs |
|---:|---|---:|---:|---:|
| 1,048,576 | forward | 6.273 ms | 37.012 ms (5.90×) | 14.847 ms (2.37×) |
| 1,048,576 | inverse | 6.186 ms | 42.908 ms (6.94×) | 16.540 ms (2.67×) |

The repository comparer classified all six prototype rows at log sizes 12, 16 and 20 as unchanged, with no slower, missing, mismatched or suspect rows; the practical threshold is 5% and requires strict separation to judge a change. Small rows had five rounds, million-point rows seven; harness floor/drift groups were absent. Million-point new/old median ratios were 0.978 forward and 0.951 inverse. This establishes no detected regression, not a proof of identical performance. The new prototype also passed 1,408 compiled storage agreement checks covering shared input preservation, capacity growth, partial batches and invalid ranges; all FFT output digests matched across eight validation sizes in both directions.

Further removal did sacrifice performance in the tested replacements. Replacing native word reads with four proof-bounded Lean byte reads increased million-point time by roughly 6×. A direct, unrolled Lean writer using the existing byte primitives was about 3–3.5× slower; the generic Lean storage fallback was slower still. Moving only copy/growth fallback handling into Lean reduced C to 648 bytes but regressed small transforms and was rejected. These screens do not prove that a different storage representation or compiler implementation could never avoid the remaining externs.

The prototype is not fully refined or installed in the default runner; native word copies were tested on the little-endian host. No Rust code or build settings changed. Selected source and runtime checks are saved in ignored `bench/out/ntt-storage-investigation-oct2/sources/NTTBench-two-unsigned-checked.lean`, with executable `bench/out/ntt-frozen-plonky3/lean-two-unsigned-oct2`. `bench/out/ntt-storage-investigation-oct2/sources/ntt-two-unsigned-final.py` reproduces the three-way comparison with the frozen verified Lean and Plonky3 executables, while retaining the old prototype as the minimization control. Measurements are in `bench/out/ntt-two-unsigned-final-oct2.json`. The normal verified runner was restored and rebuilt afterward.


### Input fusion and kernel normalization (2026-10-02)

The selected native-storage prototype fuses public field-array reads with the first butterfly split, removing its separate serial packing pass. A bounds-proved, inlined accessor reads the sixteen input lanes; the generated right-split kernel has vector multiplies and no reference-count call sites. Inverse scaling is folded into a separate sixteen-coefficient final-layer kernel, so it runs within the parallel FFT tasks before their final packed stores. The decoder then only reorders and converts those already-normalized values. Both changes are Lean; the two storage externs and their 774 bytes of inline C are unchanged.

Kernel normalization is used when the leaf transform has an even log size of at least four. Other sizes retain normalization in the decoder. A zero task depth uses the existing packing path. The final source includes no `sorry`, but still lacks a complete FFT refinement theorem; it remains outside the verified library and default benchmark.

The final comparison froze both prototypes, the verified no-new-extern implementation and the unchanged Plonky3 executable before timing. It used four physical cores (CPUs 2–5), four workers, sixteen leaf tasks, seven alternating rounds for million-point transforms and five for smaller sizes. Complete-transform medians, with conversion and normalization included:

| Elements | Direction | Previous prototype | Combined prototype | New / old |
|---:|---|---:|---:|---:|
| 4,096 | forward | 0.2228 ms | 0.2009 ms | 0.902 |
| 4,096 | inverse | 0.2124 ms | 0.1999 ms | 0.941 |
| 65,536 | forward | 0.9522 ms | 0.8447 ms | 0.887 |
| 65,536 | inverse | 1.1092 ms | 0.8323 ms | 0.750 |
| 1,048,576 | forward | 14.9700 ms | 13.8785 ms | 0.927 |
| 1,048,576 | inverse | 17.3561 ms | 14.1433 ms | 0.815 |

The repository comparer classified all three inverse rows faster and all three forward rows unchanged, with no slower, missing, mismatched or suspect rows. The million-point inverse gain was 18.5%, with strict separation of the seven baseline/candidate runs; the forward median fell 7.3%, but overlapping runs did not establish a gain under the comparer. Harness floor/drift groups were absent. Rust measured 7.729 / 6.601 ms and verified Lean 37.300 / 42.655 ms at one million points, forward/inverse. The shared host remained busy, so those Rust figures should not be compared with older runs to infer a Rust implementation change; its executable SHA256 stayed `83479b757394874fc7304c974b13f48461176691ca9711a144876648ccc18229`.

All output digests agreed with verified Lean and Plonky3 at log sizes 0, 1, 3, 4, 5, 12, 14, 15, 16, 17 and 20 in both directions. Additional agreement checks used task depths 0, 1, 2, 4 and 5 at log size 5; 0, 1, 2, 3, 4, 8 and 10 at log size 12; and 0, 1, 2, 3 and 5 at log size 20. These exercise unfused input paths, odd-sized leaves and leaves too small for kernel normalization. The unchanged externs also passed 1,408 compiled agreement checks against their Lean storage specifications.

Independent screens informed the final choice. Input fusion alone improved the 65,536-point rows but did not establish a million-point forward gain. Kernel normalization alone lowered the million-point inverse median by about 11% in three rounds. Building four natural-order field arrays and concatenating them regressed; replacing the concatenation tree with a single bounds-proved assembly loop also regressed. Returning packed natural-order chunks avoided the field-array joins but added a complete output pass and did not improve the screen. The selected version keeps the existing tiled output conversion and performs inverse normalization before the output stage, rather than adding output tasks.

Selected local source: `bench/out/ntt-storage-investigation-oct2/sources/NTTBench-fused-input-normalize.lean`; frozen executable: `bench/out/ntt-frozen-plonky3/lean-fused-input-normalize-oct2`. `bench/out/ntt-storage-investigation-oct2/sources/ntt-input-output-final.py` reproduces the final comparison, recorded in `bench/out/ntt-fused-input-normalize-final-oct2.json`. Comparer inputs and verdicts are under `bench/out/ntt-input-output-ab/`. The same ignored source directory retains the separate experiments and their screen drivers. The normal verified runner was restored exactly and rebuilt afterward. The externless implementation was not changed in this pass; parallelizing and optimizing it is the next implementation pass.

### Externless NTT loop optimization (2026-10-02)

The retained natural-order plan now checks ranges once per stage, advances block bases with machine-word arithmetic, and specializes the quarter-one radix-four stage to remove three unit-twiddle multiplications per butterfly. Inverse normalization reuses its working array with one bounds-proved write per coefficient. Separate size, coefficient and traversal lemmas prove these loops equal to the original total functions, including malformed tables and padding/truncation cases. There are no new externs, compiler changes, `implemented_by` routes or `csimp` registrations.

Each retained optimization passed compiled digest validation against the frozen Plonky3 executable and an interleaved timing comparison. Seven-round gates require a median improvement of at least 5% and every candidate invocation faster than every baseline invocation for a `faster` verdict. No row was marked `SUSPECT`; these dedicated NTT rows do not include harness drift or timing-floor canaries. Measurements use four physical Ryzen 7 3700X cores as the allowed CPU set; this verified implementation still executes sequentially.

Rejected variants included batched four-output stores, four-lane arithmetic batches, 32-bit permutation caches, bounds-proved direct gathers, moving normalization into the input gather and four-layer scalar fusion. The fused kernel improved the larger transforms by only 3–5%, below the retention gate. Parallel array prototypes remain research: splitting, gathering and joining must be considered together, and any retained parallel implementation still needs a complete refinement proof. Sources, frozen binaries and paired measurements from this pass are under the ignored local `bench/out/ntt-externless-investigation-oct2/` directory. Reproduce the retained library path with `python3 scripts/bench-fields.py --suite ntt --cpus 2,3,4,5`.

### Proved parallel natural-order NTT

`NTTFast.NaturalPlan.forwardParallel` and `inverseParallel` use up to `2 ^ logWorkers` independent array segments (default `logWorkers = 4`). Forward runs the largest fused stages before splitting; inverse runs the independent smaller stages before joining and finishing the largest stages. Tasks have separate mutable arrays and use dependency joins rather than blocking worker threads. The complete forward and inverse functions are proved equal to the existing scalar natural-order APIs, with no compiler substitutions or new externs.

The NTT comparison runner sets `logWorkers` from `LEAN_NUM_THREADS`, which the driver sets to the selected CPU count. Transforms below 2^18 elements use the scalar loop to avoid task and copy costs; aligned segments stop splitting below 16,384 elements. All selected CPU counts remain configurable with `--cpus`.

On the Ryzen 7 3700X (eight physical cores / sixteen hardware threads), seven alternating million-point rounds on CPUs 0–15 measured 28.581 ms forward and 29.785 ms inverse for the proved parallel implementation, versus 31.087 ms and 34.621 ms for the scalar control. Both large rows passed the 5% retention gate with strict separation; four smaller scalar rows were unchanged. The comparison copies aligned the old/new method labels; original samples, checksums and work-unit counts were preserved. Harness drift and timing-floor canaries were absent from these dedicated NTT rows.

The unchanged native-storage prototype measured 12.468 / 12.385 ms, and frozen stock Plonky3 measured 3.377 / 3.338 ms, forward/inverse. All complete output digests matched at log sizes 0, 1, 3, 4, 5, 12, 14, 15, 16, 17, 18, 19 and 20. The large odd size exercises the parallel path and the final radix-two stage together. The measured source was clean `8ad5024`; raw local measurements and executable hashes are in ignored `bench/out/ntt-externless-investigation-oct2/proved-parallel-sixteen-workers.json`.

Reproduce the verified comparison with `python3 scripts/bench-fields.py --suite ntt --cpus 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15`. Input copying, ordering, output disposal and inverse normalization are included; plans and decoding are outside timing. Sharing, copies, joins and the larger sequential stages still limit scaling. This pass adds no externs or compiler changes.
