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

`python3 scripts/bench-fields.py --suite all --cpu 0` compares selected Lean groups with pinned Rust libraries. `--suite small-prime` covers KoalaBear, Mersenne31, and Goldilocks against Plonky3; `--suite large-prime` covers BN254 scalar add/mul latency and throughput, plus inv/exp latency, against arkworks. `--suite binary` covers 8-, 64-, and 128-bit Fan–Paar tower mul latency/throughput and square/inv latency against pinned Binius. `all` selects 36 cases. The default suite is `small-prime`. Choose an available logical CPU; both executables run sequentially on it.

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

`Native64x4.mulUnreduced` exposes the shared four-round product before normalization, retaining all five intermediate limbs. Its `mulUnreduced_spec` theorem gives the range bound and Montgomery congruence with a canonical first operand and an arbitrary four-limb second operand. Canonical multiplication applies `condSubWide`; specialized lazy loops can use the same core and defer normalization, proving that the carry limb vanishes when the modulus bound permits it. The primitive stays inline, while the canonical `mulKernel` and `squareKernel` parameter boundaries remain out of line.

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
