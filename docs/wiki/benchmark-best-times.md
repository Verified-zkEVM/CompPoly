# Benchmark best times

The current best time of every operation the benchmark suite covers, one
section per component, every row tied to the commit whose build produced it.
This page is the record the optimisation loop in
[`autoresearch.md`](autoresearch.md) writes into; how the suite measures and
how to read a row is [`benchmarking.md`](benchmarking.md). A kept pass
overwrites the rows it improved and adds a line to the pass log; nothing else
here should need to change between passes.

## Pass log

One line per kept pass, newest last. `Rows` names the groups whose rows were
overwritten.

| Date | Commit | PR | Component | Rows | Note |
|---|---|---|---|---|---|
| 2026-09-21 | `1247810` | #371 | all | every group | first baseline: one full run at `--medium` |

## How to read and how to update the tables

Every number below was measured on the **reference machine** under the same
conditions, and only numbers measured that way belong in these tables:

| | |
|---|---|
| Machine | Apple M3 Max, 16 cores, 64 GiB, macOS; nothing else running |
| Preset | `--medium` (the preset the A/B loop uses) |
| Toolchain | `leanprover/lean4:v4.34.0` |
| Invocation | `.lake/build/bin/CompPolyBench --medium --out-dir <dir> --groups <section's groups>` on a clean tree |

Columns: **Row** is the implementation (`name` · method · representation, as
the JSONL names them); **Median** is the median sample per iteration;
**Per unit** is that median divided by `workUnits` for chained rows, the number
to compare between field operations; **Spread** is the median absolute deviation as
a percentage of the median, with `(n=k)` for under-replicated rows, `n=1` for
single-sample rows and `!k` for `k` severe outliers; **Best at** is the short
commit of the build that produced the number.

Two rows in one group differ by implementation, not by problem, so their ratio
is the speedup of one over the other on this machine. Two rows in different
groups are different problems and are not compared. Neither is a per-unit
number compared with `harness-floor`, which is per iteration; the chain floor
in the harness section below is its reference.

**Updating a row.** A number is overwritten when, and only when, all of the
following hold:

1. the change was taken through the loop in
   [`autoresearch.md`](autoresearch.md) and its A/B run
   returned `faster` on that row without `SUSPECT`, with harness drift inside
   ±10%;
2. the change is merged, and the affected groups were re-run on the reference
   machine at `--medium` from a clean checkout of the merge commit;
3. the new row's digest equals the old row's digest, which the `mismatch`
   verdict already enforced.

Then replace the row's Median, Per unit and Spread with the re-run's values,
set Best at to the merge commit, and add a line to the pass log above. Rows the change did not improve keep their
older commit, so a table may cite several commits at once; that is the intended
reading, since each row's provenance is its own. A change that makes a row
*slower* but is kept for another reason (a compile-time fix, a correctness
repair) also overwrites the row, so that the table never claims a time the
current code cannot reproduce. Reset every row of a section from one run when
the reference machine or the toolchain changes, and say so in the section.

The first baseline, at commit `1247810` on 2026-09-21, was one run over every
group at `--medium`, and the tables here are it; the `n=1` rows are workloads whose single iteration
exhausts the budget and are listed for completeness, not for comparison.

## Harness self-check

*What it is.* The harness measuring itself: `harness-floor` is an empty body,
so the per-iteration cost of the loop and the sink; `harness-canary` is a body
of known, non-eliminable cost; `harness-chain-floor` is the cheapest honest
operation in both chain shapes, the reference for every per-unit number in the
field sections; `harness-chain-linearity` checks that eight times the chain
costs at least four times as much. Source: `bench/CompPolyBench/Harness/SelfCheck.lean`.

*Not an optimisation target.* These rows define the floor the others are read
against. They change only when the harness changes, and then every other table
should be re-baselined.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `harness-floor` | `harness-floor` · empty body · UInt64 | no input | 1.99 ns | - | ±0.8% !4 | `1247810` |
| `harness-canary` | `harness-canary` · 256 mixing rounds · UInt64 | no input | 443 ns | - | ±0.9% !1 | `1247810` |
| `harness-chain-floor` | `harness-chain-floor` · 1280x shift-add, dependent · UInt64 | no input | 660 ns | 0.52 ns | ±3.3% | `1247810` |
| `harness-chain-floor` | `harness-chain-floor` · 1280x shift-add, 10-wide · UInt64 | no input | 133 ns | 0.10 ns | ±3.2% | `1247810` |
| `harness-chain-linearity` | `harness-chain-linearity-short` · 1280 rounds · UInt64 | no input | 599 ns | - | ±1.9% | `1247810` |
| `harness-chain-linearity` | `harness-chain-linearity-long` · 10240 rounds · UInt64 | no input | 5.16 µs | - | ±2.8% | `1247810` |

## Base-field arithmetic

*What it is.* `mul`, `add`, `inv` and `pow` on the four small prime fields,
each group carrying the canonical `ZMod` row and the native-word row. The fast
implementations are the 32-bit Montgomery field for KoalaBear and BabyBear
(`CompPoly/Fields/Montgomery/Native32Field.lean`), the specialised reductions
for Goldilocks (`CompPoly/Fields/Goldilocks/Fast.lean`) and Mersenne31
(`CompPoly/Fields/Mersenne31/Fast.lean`). `mul` and `add` are reported in both
chain shapes; `inv` and `pow` in the dependent shape only.

*Gate.* The `toField_*` and `ringEquiv` bridges tie each fast carrier to
`ZMod p`; the `ZMod` row in every group is the differential check. Two to four
digest-cross-checked rows per group make these the best-behaved targets in the
suite. *Peer:* Plonky3's scalar kernels for the same four fields, SIMD off;
"on par" is within two to five times.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `fields-koalabear-mul` | `koalabear-mul-zmod` · mul (latency) · ZMod | 64 seeds, 1280-operation chains | 7.79 µs | 6.08 ns | ±2.0% | `1247810` |
| `fields-koalabear-mul` | `koalabear-mul-fast` · mul (latency) · UInt32 | 64 seeds, 1280-operation chains | 4.15 µs | 3.25 ns | ±1.5% | `1247810` |
| `fields-koalabear-mul` | `koalabear-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 1280-operation chains | 8.24 µs | 6.44 ns | ±3.2% | `1247810` |
| `fields-koalabear-mul` | `koalabear-mul-fast` · mul (throughput) · UInt32 | 64 seeds, 1280-operation chains | 654 ns | 0.51 ns | ±1.1% | `1247810` |
| `fields-koalabear-add` | `koalabear-add-zmod` · add (latency) · ZMod | 64 seeds, 1280-operation chains | 6.75 µs | 5.27 ns | ±1.9% | `1247810` |
| `fields-koalabear-add` | `koalabear-add-fast` · add (latency) · UInt32 | 64 seeds, 1280-operation chains | 1.47 µs | 1.15 ns | ±1.1% | `1247810` |
| `fields-koalabear-add` | `koalabear-add-zmod` · add (throughput) · ZMod | 64 seeds, 1280-operation chains | 7.58 µs | 5.92 ns | ±1.3% !1 | `1247810` |
| `fields-koalabear-add` | `koalabear-add-fast` · add (throughput) · UInt32 | 64 seeds, 1280-operation chains | 765 ns | 0.60 ns | ±2.4% | `1247810` |
| `fields-koalabear-inv` | `koalabear-inv-zmod` · inv (ZMod.inv) | 64 seeds, 64-operation chains | 66.0 µs | 1.03 µs | ±2.2% | `1247810` |
| `fields-koalabear-inv` | `koalabear-inv-fast` · inv (Fermat chain) · UInt32 | 64 seeds, 64-operation chains | 8.94 µs | 140 ns | ±2.6% | `1247810` |
| `fields-koalabear-pow` | `koalabear-pow-zmod` · pow (binary ladder) · ZMod | 64 seeds, 64-operation chains | 72.7 µs | 1.14 µs | ±1.8% | `1247810` |
| `fields-koalabear-pow` | `koalabear-pow-fast` · pow (binary ladder) · UInt32 | 64 seeds, 64-operation chains | 9.30 µs | 145 ns | ±2.4% | `1247810` |
| `fields-babybear-mul` | `babybear-mul-zmod` · mul (latency) · ZMod | 64 seeds, 1280-operation chains | 8.04 µs | 6.28 ns | ±2.9% | `1247810` |
| `fields-babybear-mul` | `babybear-mul-fast` · mul (latency) · UInt32 | 64 seeds, 1280-operation chains | 4.27 µs | 3.33 ns | ±0.7% | `1247810` |
| `fields-babybear-mul` | `babybear-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 1280-operation chains | 8.42 µs | 6.58 ns | ±2.2% | `1247810` |
| `fields-babybear-mul` | `babybear-mul-fast` · mul (throughput) · UInt32 | 64 seeds, 1280-operation chains | 672 ns | 0.52 ns | ±2.5% | `1247810` |
| `fields-babybear-add` | `babybear-add-zmod` · add (latency) · ZMod | 64 seeds, 1280-operation chains | 7.02 µs | 5.49 ns | ±0.8% !1 | `1247810` |
| `fields-babybear-add` | `babybear-add-fast` · add (latency) · UInt32 | 64 seeds, 1280-operation chains | 1.38 µs | 1.07 ns | ±1.8% | `1247810` |
| `fields-babybear-add` | `babybear-add-zmod` · add (throughput) · ZMod | 64 seeds, 1280-operation chains | 7.42 µs | 5.80 ns | ±1.3% | `1247810` |
| `fields-babybear-add` | `babybear-add-fast` · add (throughput) · UInt32 | 64 seeds, 1280-operation chains | 751 ns | 0.59 ns | ±1.7% | `1247810` |
| `fields-babybear-inv` | `babybear-inv-zmod` · inv (ZMod.inv) | 64 seeds, 64-operation chains | 65.4 µs | 1.02 µs | ±3.0% | `1247810` |
| `fields-babybear-inv` | `babybear-inv-fast` · inv (Fermat chain) · UInt32 | 64 seeds, 64-operation chains | 9.26 µs | 145 ns | ±1.9% | `1247810` |
| `fields-babybear-pow` | `babybear-pow-zmod` · pow (binary ladder) · ZMod | 64 seeds, 64-operation chains | 73.3 µs | 1.14 µs | ±1.8% | `1247810` |
| `fields-babybear-pow` | `babybear-pow-fast` · pow (binary ladder) · UInt32 | 64 seeds, 64-operation chains | 8.81 µs | 138 ns | ±2.1% | `1247810` |
| `fields-mersenne31-mul` | `mersenne31-mul-zmod` · mul (latency) · ZMod | 64 seeds, 1280-operation chains | 7.60 µs | 5.94 ns | ±1.2% | `1247810` |
| `fields-mersenne31-mul` | `mersenne31-mul-fast` · mul (latency) · UInt32 | 64 seeds, 1280-operation chains | 2.80 µs | 2.18 ns | ±1.4% !1 | `1247810` |
| `fields-mersenne31-mul` | `mersenne31-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 1280-operation chains | 8.24 µs | 6.44 ns | ±1.7% | `1247810` |
| `fields-mersenne31-mul` | `mersenne31-mul-fast` · mul (throughput) · UInt32 | 64 seeds, 1280-operation chains | 503 ns | 0.39 ns | ±0.2% !2 | `1247810` |
| `fields-mersenne31-add` | `mersenne31-add-zmod` · add (latency) · ZMod | 64 seeds, 1280-operation chains | 6.74 µs | 5.26 ns | ±1.6% | `1247810` |
| `fields-mersenne31-add` | `mersenne31-add-fast` · add (latency) · UInt32 | 64 seeds, 1280-operation chains | 1.03 µs | 0.81 ns | ±1.9% | `1247810` |
| `fields-mersenne31-add` | `mersenne31-add-zmod` · add (throughput) · ZMod | 64 seeds, 1280-operation chains | 7.40 µs | 5.78 ns | ±1.5% | `1247810` |
| `fields-mersenne31-add` | `mersenne31-add-fast` · add (throughput) · UInt32 | 64 seeds, 1280-operation chains | 626 ns | 0.49 ns | ±1.7% | `1247810` |
| `fields-mersenne31-inv` | `mersenne31-inv-zmod` · inv (ZMod.inv) | 64 seeds, 64-operation chains | 65.2 µs | 1.02 µs | ±4.8% | `1247810` |
| `fields-mersenne31-inv` | `mersenne31-inv-fast` · inv (Fermat chain) · UInt32 | 64 seeds, 64-operation chains | 5.48 µs | 85.6 ns | ±0.9% | `1247810` |
| `fields-mersenne31-pow` | `mersenne31-pow-zmod` · pow (binary ladder) · ZMod | 64 seeds, 64-operation chains | 72.6 µs | 1.13 µs | ±1.7% | `1247810` |
| `fields-mersenne31-pow` | `mersenne31-pow-fast` · pow (binary ladder) · UInt32 | 64 seeds, 64-operation chains | 4.89 µs | 76.4 ns | ±0.7% | `1247810` |
| `fields-goldilocks-mul` | `goldilocks-mul-zmod` · mul (latency) · ZMod | 64 seeds, 1280-operation chains | 328 µs | 257 ns | ±1.1% | `1247810` |
| `fields-goldilocks-mul` | `goldilocks-mul-fast` · mul (latency) · UInt64 | 64 seeds, 1280-operation chains | 4.15 µs | 3.24 ns | ±0.5% | `1247810` |
| `fields-goldilocks-mul` | `goldilocks-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 1280-operation chains | 287 µs | 224 ns | ±1.4% | `1247810` |
| `fields-goldilocks-mul` | `goldilocks-mul-fast` · mul (throughput) · UInt64 | 64 seeds, 1280-operation chains | 843 ns | 0.66 ns | ±1.0% !3 | `1247810` |
| `fields-goldilocks-add` | `goldilocks-add-zmod` · add (latency) · ZMod | 64 seeds, 1280-operation chains | 178 µs | 139 ns | ±1.2% | `1247810` |
| `fields-goldilocks-add` | `goldilocks-add-fast` · add (latency) · UInt64 | 64 seeds, 1280-operation chains | 1.70 µs | 1.33 ns | ±0.0% !1 | `1247810` |
| `fields-goldilocks-add` | `goldilocks-add-zmod` · add (throughput) · ZMod | 64 seeds, 1280-operation chains | 236 µs | 184 ns | ±1.9% | `1247810` |
| `fields-goldilocks-add` | `goldilocks-add-fast` · add (throughput) · UInt64 | 64 seeds, 1280-operation chains | 599 ns | 0.47 ns | ±0.7% !2 | `1247810` |
| `fields-goldilocks-inv` | `goldilocks-inv-zmod` · inv (ZMod.inv) | 64 seeds, 64-operation chains | 629 µs | 9.83 µs | ±2.4% !1 | `1247810` |
| `fields-goldilocks-inv` | `goldilocks-inv-fast` · inv (Fermat chain) · UInt64 | 64 seeds, 64-operation chains | 25.4 µs | 397 ns | ±1.3% | `1247810` |
| `fields-goldilocks-pow` | `goldilocks-pow-zmod` · pow (binary ladder) · ZMod | 64 seeds, 64-operation chains | 742 µs | 11.6 µs | ±2.1% !1 | `1247810` |
| `fields-goldilocks-pow` | `goldilocks-pow-fast` · pow (binary ladder) · UInt64 | 64 seeds, 64-operation chains | 7.31 µs | 114 ns | ±2.0% | `1247810` |

## Pairing scalar fields

*What it is.* The eight-limb Montgomery representation of the BN254, BLS12-381
and BLS12-377 scalar fields: `mul` in both chain shapes against `ZMod`
(`CompPoly/Fields/Montgomery/Native64x8Mul.lean`), and `inv` as three
algorithms in one group, `ZMod`'s extended Euclid, the checked binary GCD and
Fermat (`CompPoly/Fields/Montgomery/Native64x8InvDefs.lean`).

*Gate.* `invGcdRaw_eq_inv` and its bounds chain in
`CompPoly/Fields/Montgomery/Native64x8Inv.lean`; one digest class per group.
*Peer:* arkworks or gnark-crypto over the same `mul` and `inv`.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `fields-mont64x8-bn254-inv` | `scalar-inv-xgcd` · inv (xgcd) · ZMod | 256 random elements | 86.0 µs | - | ±2.0% !1 | `1247810` |
| `fields-mont64x8-bn254-inv` | `scalar-inv-gcd` · inv (binary GCD) · Mont64x8 | 256 random elements | 6.81 µs | - | ±2.6% | `1247810` |
| `fields-mont64x8-bn254-inv` | `scalar-inv-fermat` · inv (Fermat) · Mont64x8 | 256 random elements | 48.4 µs | - | ±1.7% | `1247810` |
| `fields-mont64x8-bls12-381-inv` | `scalar-inv-xgcd` · inv (xgcd) · ZMod | 256 random elements | 90.3 µs | - | ±1.4% | `1247810` |
| `fields-mont64x8-bls12-381-inv` | `scalar-inv-gcd` · inv (binary GCD) · Mont64x8 | 256 random elements | 6.63 µs | - | ±2.1% | `1247810` |
| `fields-mont64x8-bls12-381-inv` | `scalar-inv-fermat` · inv (Fermat) · Mont64x8 | 256 random elements | 48.2 µs | - | ±1.5% !1 | `1247810` |
| `fields-mont64x8-bls12-377-inv` | `scalar-inv-xgcd` · inv (xgcd) · ZMod | 256 random elements | 93.5 µs | - | ±2.7% !1 | `1247810` |
| `fields-mont64x8-bls12-377-inv` | `scalar-inv-gcd` · inv (binary GCD) · Mont64x8 | 256 random elements | 6.66 µs | - | ±1.9% | `1247810` |
| `fields-mont64x8-bls12-377-inv` | `scalar-inv-fermat` · inv (Fermat) · Mont64x8 | 256 random elements | 46.2 µs | - | ±2.4% | `1247810` |
| `fields-bn254-mul` | `bn254-mul-zmod` · mul (latency) · ZMod | 64 seeds, 320-operation chains | 75.9 µs | 237 ns | ±1.9% | `1247810` |
| `fields-bn254-mul` | `bn254-mul-fast` · mul (latency) · Limbs8 | 64 seeds, 320-operation chains | 12.1 µs | 37.7 ns | ±2.0% | `1247810` |
| `fields-bn254-mul` | `bn254-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 320-operation chains | 78.3 µs | 245 ns | ±1.9% | `1247810` |
| `fields-bn254-mul` | `bn254-mul-fast` · mul (throughput) · Limbs8 | 64 seeds, 320-operation chains | 11.5 µs | 35.8 ns | ±1.7% | `1247810` |
| `fields-bls12-381-mul` | `bls12-381-mul-zmod` · mul (latency) · ZMod | 64 seeds, 320-operation chains | 74.3 µs | 232 ns | ±0.7% !3 | `1247810` |
| `fields-bls12-381-mul` | `bls12-381-mul-fast` · mul (latency) · Limbs8 | 64 seeds, 320-operation chains | 12.8 µs | 39.9 ns | ±1.2% | `1247810` |
| `fields-bls12-381-mul` | `bls12-381-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 320-operation chains | 78.6 µs | 246 ns | ±2.4% | `1247810` |
| `fields-bls12-381-mul` | `bls12-381-mul-fast` · mul (throughput) · Limbs8 | 64 seeds, 320-operation chains | 11.7 µs | 36.5 ns | ±0.7% | `1247810` |
| `fields-bls12-377-mul` | `bls12-377-mul-zmod` · mul (latency) · ZMod | 64 seeds, 320-operation chains | 74.5 µs | 233 ns | ±1.9% !1 | `1247810` |
| `fields-bls12-377-mul` | `bls12-377-mul-fast` · mul (latency) · Limbs8 | 64 seeds, 320-operation chains | 11.9 µs | 37.3 ns | ±1.3% !1 | `1247810` |
| `fields-bls12-377-mul` | `bls12-377-mul-zmod` · mul (throughput) · ZMod | 64 seeds, 320-operation chains | 78.3 µs | 245 ns | ±1.9% | `1247810` |
| `fields-bls12-377-mul` | `bls12-377-mul-fast` · mul (throughput) · Limbs8 | 64 seeds, 320-operation chains | 10.8 µs | 33.7 ns | ±0.2% !2 | `1247810` |

## Extension fields

*What it is.* Multiplication and inversion in `F[X]/f` for the degree-4
BabyBear and KoalaBear extensions and the degree-5 and degree-6 KoalaBear
extensions (`CompPoly/Fields/Extension/Arithmetic.lean`). `mul` is the
table-driven `mulTbl`, swapped in for the specification `mul` by `@[csimp]`;
`inv` is Fermat, so it is a chain of multiplications through `npowBinRec`.
Single-row groups: the digest across builds and the build itself are the gates.

*State.* The first optimisation pass (`docs/bench-audit-2026.md` §12.9) took
`mul` from `Finset.sum` to `Fin.foldl` loops and the reduction table from
`O(d³)` to `O(d²)`, roughly halving `mul` and taking `inv` to two fifths, then
gave a fifth of that back by dropping `@[inline]` so the test suite compiles.
Documented headroom: the remaining cost at `d = 4` is runtime typeclass
dictionary construction on the generic path rather than arithmetic, and the
`O(d²)` convolution that lost at `d = 4` already wins at `d = 6`. *Peer:*
Plonky3's BabyBear and KoalaBear quartic extensions.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `fields-extension-koalabear-ext4-mul` | `extension-mul` · mul · Extension.Ext | 64 random degree-4 elements, pairwise | 9.22 µs | - | ±1.7% | `1247810` |
| `fields-extension-koalabear-ext4-inv` | `extension-inv` · inv (Fermat) · Extension.Ext | 64 random degree-4 elements, pairwise | 1.02 ms | - | ±1.9% | `1247810` |
| `fields-extension-babybear-ext4-mul` | `extension-mul` · mul · Extension.Ext | 64 random degree-4 elements, pairwise | 9.18 µs | - | ±1.6% | `1247810` |
| `fields-extension-babybear-ext4-inv` | `extension-inv` · inv (Fermat) · Extension.Ext | 64 random degree-4 elements, pairwise | 954 µs | - | ±2.4% | `1247810` |
| `fields-extension-koalabear-ext5-mul` | `extension-mul` · mul · Extension.Ext | 64 random degree-5 elements, pairwise | 13.2 µs | - | ±1.6% | `1247810` |
| `fields-extension-koalabear-ext5-inv` | `extension-inv` · inv (Fermat) · Extension.Ext | 64 random degree-5 elements, pairwise | 2.11 ms | - | ±1.2% | `1247810` |
| `fields-extension-koalabear-ext6-mul` | `extension-mul` · mul · Extension.Ext | 64 random degree-6 elements, pairwise | 19.4 µs | - | ±2.8% | `1247810` |
| `fields-extension-koalabear-ext6-inv` | `extension-inv` · inv (Fermat) · Extension.Ext | 64 random degree-6 elements, pairwise | 4.03 ms | - | ±1.2% | `1247810` |

## Binary tower fields

*What it is.* The binary tower built by iterated quadratic extension: the packed-word `GF(2^128)`
implementation against its `BitVec` specification for `mul`, `inv` and
multilinear coefficient evaluation (`CompPoly/Fields/Binary/Tower/Fast*.lean`),
and the scalar operations underneath, `GF(2^8)` and `GF(2^64)` table-driven
against recursive (`CompPoly/Fields/Binary/Tower/FastDefs.lean`).

*Gate.* `mul64T_eq_mul64`, `inv64T_eq_inv64` and the `toConcrete_*` lemmas in
`CompPoly/Fields/Binary/Tower/Fast.lean`. The table twins are already close to
the recursive definitions' floor, so the documented headroom is low. *Peer:*
Binius, packed off.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `fields-tower-bt128-mul` | `tower-bt128` · mul (ConcreteBTField) | 64 random 128-bit elements, pairwise | 5.81 ms | - | ±0.5% | `1247810` |
| `fields-tower-bt128-mul` | `tower-bt128-fast` · mul (FastBT128) | 64 random 128-bit elements, pairwise | 298 ns | - | ±2.1% | `1247810` |
| `fields-tower-bt128-inv` | `tower-bt128` · inv (ConcreteBTField) | 64 random 128-bit elements, pairwise | 9.96 ms | - | ±1.0% | `1247810` |
| `fields-tower-bt128-inv` | `tower-bt128-fast` · inv (FastBT128) | 64 random 128-bit elements, pairwise | 340 ns | - | ±0.9% !1 | `1247810` |
| `fields-tower-bt128-coeff-eval` | `tower-bt128-coeff-eval` · coefficient evaluation · ConcreteBTField | 16 coefficients, 4 variables, 8 points; random 128-bit words | 449 ms | - | ±0.3% (n=4) | `1247810` |
| `fields-tower-bt128-coeff-eval` | `tower-bt128-fast-coeff-eval` · eager product accumulation · FastBT128 | 16 coefficients, 4 variables, 8 points; random 128-bit words | 8.85 µs | - | ±1.1% !1 | `1247810` |
| `fields-tower-bt8-mul` | `tower-bt8-mul-rec` · mul (latency) · UInt64 | 64 seeds, 1280-operation chains | 23.9 µs | 18.7 ns | ±1.2% | `1247810` |
| `fields-tower-bt8-mul` | `tower-bt8-mul-table` · mul (latency) · UInt64 | 64 seeds, 1280-operation chains | 3.51 µs | 2.74 ns | ±2.5% | `1247810` |
| `fields-tower-bt8-mul` | `tower-bt8-mul-rec` · mul (throughput) · UInt64 | 64 seeds, 1280-operation chains | 7.63 µs | 5.96 ns | ±1.4% | `1247810` |
| `fields-tower-bt8-mul` | `tower-bt8-mul-table` · mul (throughput) · UInt64 | 64 seeds, 1280-operation chains | 408 ns | 0.32 ns | ±2.3% | `1247810` |
| `fields-tower-bt64-mul` | `tower-bt64-mul-rec` · mul (latency) · UInt64 | 64 seeds, 1280-operation chains | 223 µs | 174 ns | ±1.7% | `1247810` |
| `fields-tower-bt64-mul` | `tower-bt64-mul-table` · mul (latency) · UInt64 | 64 seeds, 1280-operation chains | 20.6 µs | 16.1 ns | ±1.8% | `1247810` |
| `fields-tower-bt64-mul` | `tower-bt64-mul-rec` · mul (throughput) · UInt64 | 64 seeds, 1280-operation chains | 211 µs | 165 ns | ±1.6% | `1247810` |
| `fields-tower-bt64-mul` | `tower-bt64-mul-table` · mul (throughput) · UInt64 | 64 seeds, 1280-operation chains | 18.1 µs | 14.2 ns | ±1.9% | `1247810` |
| `fields-tower-bt64-inv-word` | `tower-bt64-inv-rec` · inv (recursive) · UInt64 | 64 seeds, 64-operation chains | 19.8 µs | 309 ns | ±1.4% | `1247810` |
| `fields-tower-bt64-inv-word` | `tower-bt64-inv-table` · inv (table) · UInt64 | 64 seeds, 64-operation chains | 2.87 µs | 44.9 ns | ±1.7% | `1247810` |

## Additive NTT

*What it is.* The additive (Lin-Chung-Han) NTT over the binary tower at three
shapes, fast implementation against the reference definition where the group
has one (`CompPoly/Fields/Binary/AdditiveNTT/`). The reference row returns a
function and the fast row an array, so both sinks fold every output position,
which is part of what each row costs.

*Gate.* `computableAdditiveNTTFast_eq_computableAdditiveNTT`; the `btf4` group
is fast-only and relies on the build. *Peer:* Binius's additive NTT at
`log n` 13 to 16, a size this suite does not yet reach.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `additive-ntt-btf3-l2-r2` | `additive-ntt-btf3` · computableAdditiveNTT | 4 input coeffs, 16 output evals | 18.3 ms | - | ±1.4% !1 | `1247810` |
| `additive-ntt-btf3-l2-r2` | `additive-ntt-btf3-fast` · computableAdditiveNTTFast | 4 input coeffs, 16 output evals | 1.45 ms | - | ±2.1% | `1247810` |
| `additive-ntt-btf3-l4-r2` | `additive-ntt-btf3-l4-r2` · computableAdditiveNTT | 16 input coeffs, 64 output evals | 1.71 s | - | n=1 | `1247810` |
| `additive-ntt-btf3-l4-r2` | `additive-ntt-btf3-l4-r2-fast` · computableAdditiveNTTFast | 16 input coeffs, 64 output evals | 8.74 ms | - | ±1.2% | `1247810` |
| `additive-ntt-btf4-l7-r2` | `additive-ntt-btf4-l7-r2-fast` · computableAdditiveNTTFast | 128 input coeffs, 512 output evals | 372 ms | - | ±0.1% | `1247810` |

## Univariate evaluation and remainder

*What it is.* Evaluation of dense polynomials over six fields, sum-of-powers
against Horner and, where the field has one, the canonical `ZMod` carrier
against the fast one (`CompPoly/Univariate/Raw/Ops.lean`, gate
`eval₂_horner_eq_eval₂`); sparse evaluation; the monic remainder at two sizes;
batch evaluation of one polynomial at many points at three sizes
(`CompPoly/Univariate/BatchEval.lean`); and evaluation of many polynomials at
one point (`CompPoly/Univariate/ManyEval/Basic.lean`, gates
`evalManyHorner_eq_map_eval` and `evalManySharedPowers_eq_map_eval`).

*State.* Plain array loops with short refinement proofs, so the proof cost of
an iteration is low. The `medium` remainder and `large` batch groups are `n=1`
at this preset. *Peer:* none at this granularity; the base-field rows above bound
what a coefficient can cost.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `univariate-dense-koalabear` | `univariate-dense-sum` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 171 µs | - | ±2.0% | `1247810` |
| `univariate-dense-koalabear` | `univariate-dense-horner` · evalHorner · CPolynomial | degree<512, dense, 32 points | 18.6 µs | - | ±2.4% | `1247810` |
| `univariate-dense-koalabear` | `univariate-dense-sum-fast` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 14.9 µs | - | ±2.2% | `1247810` |
| `univariate-dense-koalabear` | `univariate-dense-horner-fast` · evalHorner · CPolynomial | degree<512, dense, 32 points | 2.09 µs | - | ±3.0% | `1247810` |
| `univariate-sparse-koalabear` | `univariate-sparse-sum` · eval sum-of-powers · CPolynomial | degree<512, one nonzero per 4 coeffs, 32 points | 168 µs | - | ±3.0% | `1247810` |
| `univariate-sparse-koalabear` | `univariate-sparse-horner` · evalHorner · CPolynomial | degree<512, one nonzero per 4 coeffs, 32 points | 19.0 µs | - | ±3.4% | `1247810` |
| `univariate-sparse-koalabear` | `univariate-sparse-sum-fast` · eval sum-of-powers · CPolynomial | degree<512, one nonzero per 4 coeffs, 32 points | 14.8 µs | - | ±2.2% | `1247810` |
| `univariate-sparse-koalabear` | `univariate-sparse-horner-fast` · evalHorner · CPolynomial | degree<512, one nonzero per 4 coeffs, 32 points | 2.12 µs | - | ±4.0% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-naive` · modByMonic · CPolynomial | degree<128 dividend, degree=16 monic divisor | 81.6 ms | - | ±0.5% !1 | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-remainder-only` · modByMonicRemainderOnly · CPolynomial | degree<128 dividend, degree=16 monic divisor | 477 µs | - | ±2.0% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-reversal-convolution-low-mul` · modByMonicByReversal, MulLowContext.convolution · CPolynomial | degree<128 dividend, degree=16 monic divisor | 2.87 ms | - | ±1.0% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-reversal-ntt-low-mul` · modByMonicByReversal, FastMulLow.withFallback · CPolynomial | degree<128 dividend, degree=16 monic divisor | 3.52 ms | - | ±1.0% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-reversal-ntt-fast-low-mul` · modByMonicByReversal, NTTFast.FastMulLow.withFallback · CPolynomial | degree<128 dividend, degree=16 monic divisor | 736 µs | - | ±1.5% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-naive-fast` · modByMonic · CPolynomial | degree<128 dividend, degree=16 monic divisor | 14.9 ms | - | ±0.5% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-remainder-only-fast` · modByMonicRemainderOnly · CPolynomial | degree<128 dividend, degree=16 monic divisor | 108 µs | - | ±1.5% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-reversal-convolution-low-mul-fast` · modByMonicByReversal, MulLowContext.convolution · CPolynomial | degree<128 dividend, degree=16 monic divisor | 1.34 ms | - | ±1.2% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-reversal-ntt-low-mul-fast` · modByMonicByReversal, FastMulLow.withFallback · CPolynomial | degree<128 dividend, degree=16 monic divisor | 1.39 ms | - | ±1.8% | `1247810` |
| `univariate-monic-remainder-small-koalabear` | `univariate-mod-by-monic-reversal-ntt-fast-low-mul-fast` · modByMonicByReversal, NTTFast.FastMulLow.withFallback · CPolynomial | degree<128 dividend, degree=16 monic divisor | 183 µs | - | ±3.2% | `1247810` |
| `univariate-dense-goldilocks` | `univariate-dense-sum-goldilocks` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 1.67 ms | - | ±1.4% | `1247810` |
| `univariate-dense-goldilocks` | `univariate-dense-horner-goldilocks` · evalHorner · CPolynomial | degree<512, dense, 32 points | 216 µs | - | ±1.8% | `1247810` |
| `univariate-dense-bn254` | `univariate-dense-sum` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 1.93 ms | - | ±1.0% | `1247810` |
| `univariate-dense-bn254` | `univariate-dense-horner` · evalHorner · CPolynomial | degree<512, dense, 32 points | 259 µs | - | ±1.1% | `1247810` |
| `univariate-dense-bn254` | `univariate-dense-sum-fast` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 265 µs | - | ±0.8% | `1247810` |
| `univariate-dense-bn254` | `univariate-dense-horner-fast` · evalHorner · CPolynomial | degree<512, dense, 32 points | 26.4 µs | - | ±0.9% | `1247810` |
| `univariate-dense-bls12-381` | `univariate-dense-sum` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 2.01 ms | - | ±0.8% !2 | `1247810` |
| `univariate-dense-bls12-381` | `univariate-dense-horner` · evalHorner · CPolynomial | degree<512, dense, 32 points | 264 µs | - | ±1.7% | `1247810` |
| `univariate-dense-bls12-381` | `univariate-dense-sum-fast` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 281 µs | - | ±1.9% | `1247810` |
| `univariate-dense-bls12-381` | `univariate-dense-horner-fast` · evalHorner · CPolynomial | degree<512, dense, 32 points | 26.9 µs | - | ±2.2% | `1247810` |
| `univariate-dense-bls12-377` | `univariate-dense-sum` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 1.96 ms | - | ±1.8% | `1247810` |
| `univariate-dense-bls12-377` | `univariate-dense-horner` · evalHorner · CPolynomial | degree<512, dense, 32 points | 263 µs | - | ±2.2% !1 | `1247810` |
| `univariate-dense-bls12-377` | `univariate-dense-sum-fast` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 260 µs | - | ±1.0% | `1247810` |
| `univariate-dense-bls12-377` | `univariate-dense-horner-fast` · evalHorner · CPolynomial | degree<512, dense, 32 points | 26.8 µs | - | ±3.1% | `1247810` |
| `univariate-dense-babybear` | `univariate-dense-sum` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 155 µs | - | ±1.4% | `1247810` |
| `univariate-dense-babybear` | `univariate-dense-horner` · evalHorner · CPolynomial | degree<512, dense, 32 points | 19.7 µs | - | ±6.2% | `1247810` |
| `univariate-dense-babybear` | `univariate-dense-sum-fast` · eval sum-of-powers · CPolynomial | degree<512, dense, 32 points | 15.0 µs | - | ±1.9% | `1247810` |
| `univariate-dense-babybear` | `univariate-dense-horner-fast` · evalHorner · CPolynomial | degree<512, dense, 32 points | 2.08 µs | - | ±3.7% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-naive-sum` · evalBatch · CPolynomial | degree<128, dense, 16 points | 543 µs | - | ±1.5% !1 | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-naive-horner` · evalBatchHorner · CPolynomial | degree<128, dense, 16 points | 90.1 µs | - | ±3.1% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-naive-mul-naive-mod` · evalBatchSubproduct naive mul/mod · CPolynomial | degree<128, dense, 16 points | 190 ms | - | ±0.2% !2 | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-naive-mul-remainder-only-mod` · evalBatchSubproduct naive mul/remainder-only mod · CPolynomial | degree<128, dense, 16 points | 934 µs | - | ±1.2% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-mul-remainder-only-mod` · evalBatchSubproduct ntt mul/remainder-only mod · CPolynomial | degree<128, dense, 16 points | 1.25 ms | - | ±1.4% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod` · evalBatchSubproduct ntt-fast mul/remainder-only mod · CPolynomial | degree<128, dense, 16 points | 1.08 ms | - | ±2.4% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod` · evalBatchSubproduct naive mul/reversal-convolution-low mod · CPolynomial | degree<128, dense, 16 points | 6.61 ms | - | ±0.9% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod` · evalBatchSubproduct ntt mul/reversal-ntt-low mod · CPolynomial | degree<128, dense, 16 points | 8.00 ms | - | ±0.5% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod` · evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod · CPolynomial | degree<128, dense, 16 points | 2.11 ms | - | ±1.1% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-naive-sum-fast` · evalBatch · CPolynomial | degree<128, dense, 16 points | 57.7 µs | - | ±2.0% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-naive-horner-fast` · evalBatchHorner · CPolynomial | degree<128, dense, 16 points | 16.1 µs | - | ±1.1% !1 | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-naive-mul-naive-mod-fast` · evalBatchSubproduct naive mul/mod · CPolynomial | degree<128, dense, 16 points | 35.3 ms | - | ±1.6% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-naive-mul-remainder-only-mod-fast` · evalBatchSubproduct naive mul/remainder-only mod · CPolynomial | degree<128, dense, 16 points | 244 µs | - | ±2.3% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-mul-remainder-only-mod-fast` · evalBatchSubproduct ntt mul/remainder-only mod · CPolynomial | degree<128, dense, 16 points | 377 µs | - | ±2.0% !1 | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-fast-mul-remainder-only-mod-fast` · evalBatchSubproduct ntt-fast mul/remainder-only mod · CPolynomial | degree<128, dense, 16 points | 299 µs | - | ±3.1% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-naive-mul-reversal-convolution-low-mod-fast` · evalBatchSubproduct naive mul/reversal-convolution-low mod · CPolynomial | degree<128, dense, 16 points | 3.02 ms | - | ±1.6% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-mul-reversal-ntt-low-mod-fast` · evalBatchSubproduct ntt mul/reversal-ntt-low mod · CPolynomial | degree<128, dense, 16 points | 3.24 ms | - | ±0.7% | `1247810` |
| `univariate-batch-small-koalabear` | `univariate-batch-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast` · evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod · CPolynomial | degree<128, dense, 16 points | 611 µs | - | ±1.5% | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-naive-sum` · evalBatch · CPolynomial | degree<8192, dense, 1024 points | 3.34 s | - | n=1 | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-naive-horner` · evalBatchHorner · CPolynomial | degree<8192, dense, 1024 points | 328 ms | - | ±0.5% | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-naive-mul-remainder-only-mod` · evalBatchSubproduct naive mul/remainder-only mod · CPolynomial | degree<8192, dense, 1024 points | 3.41 s | - | n=1 | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod` · evalBatchSubproduct ntt mul/remainder-only mod · CPolynomial | degree<8192, dense, 1024 points | 3.35 s | - | n=1 | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod` · evalBatchSubproduct ntt-fast mul/remainder-only mod · CPolynomial | degree<8192, dense, 1024 points | 3.29 s | - | n=1 | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod` · evalBatchSubproduct ntt mul/reversal-ntt-low mod · CPolynomial | degree<8192, dense, 1024 points | 1.02 s | - | n=1 | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod` · evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod · CPolynomial | degree<8192, dense, 1024 points | 221 ms | - | ±0.5% !1 | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-naive-sum-fast` · evalBatch · CPolynomial | degree<8192, dense, 1024 points | 435 ms | - | ±0.4% (n=4) | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-naive-horner-fast` · evalBatchHorner · CPolynomial | degree<8192, dense, 1024 points | 37.3 ms | - | ±0.8% | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-naive-mul-remainder-only-mod-fast` · evalBatchSubproduct naive mul/remainder-only mod · CPolynomial | degree<8192, dense, 1024 points | 770 ms | - | ±0.0% (n=2) | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-mul-remainder-only-mod-fast` · evalBatchSubproduct ntt mul/remainder-only mod · CPolynomial | degree<8192, dense, 1024 points | 794 ms | - | ±0.0% (n=2) | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-fast-mul-remainder-only-mod-fast` · evalBatchSubproduct ntt-fast mul/remainder-only mod · CPolynomial | degree<8192, dense, 1024 points | 767 ms | - | ±0.4% (n=2) | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-mul-reversal-ntt-low-mod-fast` · evalBatchSubproduct ntt mul/reversal-ntt-low mod · CPolynomial | degree<8192, dense, 1024 points | 418 ms | - | ±0.4% (n=4) | `1247810` |
| `univariate-batch-medium-koalabear` | `univariate-batch-medium-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast` · evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod · CPolynomial | degree<8192, dense, 1024 points | 49.3 ms | - | ±0.5% | `1247810` |
| `univariate-many-one-point-koalabear` | `univariate-many-one-point-horner` · evalManyHorner · Array CPolynomial | 512 dense polys, degree<4096, one shared point | 80.3 ms | - | ±0.6% | `1247810` |
| `univariate-many-one-point-koalabear` | `univariate-many-one-point-shared-powers-row-major` · evalManySharedPowers · Array CPolynomial | 512 dense polys, degree<4096, one shared point | 75.8 ms | - | ±0.3% !1 | `1247810` |
| `univariate-many-one-point-koalabear` | `univariate-many-one-point-horner-fast` · evalManyHorner · Array CPolynomial | 512 dense polys, degree<4096, one shared point | 9.70 ms | - | ±3.0% | `1247810` |
| `univariate-many-one-point-koalabear` | `univariate-many-one-point-shared-powers-row-major-fast` · evalManySharedPowers · Array CPolynomial | 512 dense polys, degree<4096, one shared point | 3.76 ms | - | ±3.2% | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-remainder-only` · modByMonicRemainderOnly · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 1.76 s | - | n=1 | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-reversal-convolution-low-mul` · modByMonicByReversal, MulLowContext.convolution · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 12.1 s | - | n=1 | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-reversal-ntt-low-mul` · modByMonicByReversal, FastMulLow.withFallback · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 343 ms | - | ±0.2% !1 | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul` · modByMonicByReversal, NTTFast.FastMulLow.withFallback · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 61.2 ms | - | ±0.7% | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-remainder-only-fast` · modByMonicRemainderOnly · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 355 ms | - | ±0.3% | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-reversal-convolution-low-mul-fast` · modByMonicByReversal, MulLowContext.convolution · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 5.79 s | - | n=1 | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-reversal-ntt-low-mul-fast` · modByMonicByReversal, FastMulLow.withFallback · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 141 ms | - | ±0.2% !1 | `1247810` |
| `univariate-monic-remainder-medium-koalabear` | `univariate-mod-by-monic-medium-reversal-ntt-fast-low-mul-fast` · modByMonicByReversal, NTTFast.FastMulLow.withFallback · CPolynomial | degree<8192 dividend, degree=1024 monic divisor | 7.64 ms | - | ±0.5% | `1247810` |
| `univariate-batch-large-koalabear` | `univariate-batch-large-naive-horner` · evalBatchHorner · CPolynomial | degree<65536, dense, 8192 points | 19.7 s | - | n=1 | `1247810` |
| `univariate-batch-large-koalabear` | `univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod` · evalBatchSubproduct ntt mul/reversal-ntt-low mod · CPolynomial | degree<65536, dense, 8192 points | 10.6 s | - | n=1 | `1247810` |
| `univariate-batch-large-koalabear` | `univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod` · evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod · CPolynomial | degree<65536, dense, 8192 points | 2.25 s | - | n=1 | `1247810` |
| `univariate-batch-large-koalabear` | `univariate-batch-large-naive-horner-fast` · evalBatchHorner · CPolynomial | degree<65536, dense, 8192 points | 2.34 s | - | n=1 | `1247810` |
| `univariate-batch-large-koalabear` | `univariate-batch-large-subproduct-ntt-mul-reversal-ntt-low-mod-fast` · evalBatchSubproduct ntt mul/reversal-ntt-low mod · CPolynomial | degree<65536, dense, 8192 points | 4.39 s | - | n=1 | `1247810` |
| `univariate-batch-large-koalabear` | `univariate-batch-large-subproduct-ntt-fast-mul-reversal-ntt-fast-low-mod-fast` · evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod · CPolynomial | degree<65536, dense, 8192 points | 451 ms | - | ±0.8% (n=4) | `1247810` |

## Univariate multiplication

*What it is.* Full product and low product over KoalaBear and BabyBear, the
schoolbook and NTT-backed multipliers side by side
(`CompPoly/Univariate/NTT/FastMul*.lean`, `CompPoly/Univariate/NTTFast/`), and
the crossover sweep from degree 4 to degree 1024 that locates where the NTT
path overtakes schoolbook on this machine.

*Reading the sweep.* Each crossover group holds both multipliers at one size;
the size at which the NTT row first wins is the crossover, and it is a property
of this machine and this commit, so it is expected to move as either side is
optimised.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `univariate-mul-koalabear` | `univariate-mul-naive` · mul · CPolynomial | degree<1024 dense lhs/rhs | 86.2 ms | - | ±0.3% | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-ntt` · FastMul.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 10.1 ms | - | ±0.6% | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-ntt-fast` · NTTFast.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 2.74 ms | - | ±1.0% | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-ntt-fast-plan` · NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 2.59 ms | - | ±1.5% | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-naive-fast` · mul · CPolynomial | degree<1024 dense lhs/rhs | 10.5 ms | - | ±0.6% !1 | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-ntt-koalabear-fast` · FastMul.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 4.80 ms | - | ±0.9% | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-ntt-fast-koalabear-fast` · NTTFast.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 1.34 ms | - | ±1.7% | `1247810` |
| `univariate-mul-koalabear` | `univariate-mul-ntt-fast-plan-fast` · NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 1.33 ms | - | ±1.4% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-naive` · mul · CPolynomial | degree<1024 dense lhs/rhs | 86.1 ms | - | ±0.2% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-ntt` · FastMul.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 10.1 ms | - | ±0.8% !1 | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-ntt-fast` · NTTFast.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 2.73 ms | - | ±0.6% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-ntt-fast-plan` · NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 2.63 ms | - | ±1.7% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-naive-fast` · mul · CPolynomial | degree<1024 dense lhs/rhs | 10.4 ms | - | ±1.3% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-ntt-babybear-fast` · FastMul.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 4.74 ms | - | ±0.3% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-ntt-fast-babybear-fast` · NTTFast.fastMulImpl, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 1.34 ms | - | ±2.1% | `1247810` |
| `univariate-mul-babybear` | `univariate-mul-ntt-fast-plan-fast` · NTTFast.Plan.fastMulImpl, cached twiddles, mixed radix-4 DIF/DIT, dual forward, domain n=2048 · CPolynomial | degree<1024 dense lhs/rhs | 1.30 ms | - | ±2.1% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-naive` · MulLowContext.naive · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 21.7 ms | - | ±0.7% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-convolution` · MulLowContext.convolution · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 15.6 ms | - | ±0.5% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-ntt-with-fallback` · FastMulLow.withFallback · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 4.46 ms | - | ±1.0% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-ntt-fast-with-fallback` · NTTFast.FastMulLow.withFallback · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 988 µs | - | ±2.6% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-naive-fast` · MulLowContext.naive · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 2.78 ms | - | ±1.6% !2 | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-convolution-fast` · MulLowContext.convolution · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 7.59 ms | - | ±1.0% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-ntt-with-fallback-fast` · FastMulLow.withFallback · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 1.96 ms | - | ±2.0% | `1247810` |
| `univariate-low-product-koalabear` | `univariate-mul-low-ntt-fast-with-fallback-fast` · NTTFast.FastMulLow.withFallback · CPolynomial.Raw | degree<512 dense lhs/rhs, low<512 | 376 µs | - | ±2.2% !1 | `1247810` |
| `univariate-mul-crossover-4` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<4 dense lhs/rhs, two orderings | 3.52 µs | 880 ns | ±1.5% !1 | `1247810` |
| `univariate-mul-crossover-4` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<4 dense lhs/rhs, two orderings | 4.70 µs | 1.17 µs | ±1.9% !1 | `1247810` |
| `univariate-mul-crossover-8` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<8 dense lhs/rhs, two orderings | 8.92 µs | 1.12 µs | ±2.4% | `1247810` |
| `univariate-mul-crossover-8` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<8 dense lhs/rhs, two orderings | 9.40 µs | 1.17 µs | ±1.6% | `1247810` |
| `univariate-mul-crossover-16` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<16 dense lhs/rhs, two orderings | 20.7 µs | 1.29 µs | ±1.7% | `1247810` |
| `univariate-mul-crossover-16` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<16 dense lhs/rhs, two orderings | 20.6 µs | 1.29 µs | ±4.4% | `1247810` |
| `univariate-mul-crossover-32` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<32 dense lhs/rhs, two orderings | 49.3 µs | 1.54 µs | ±4.1% | `1247810` |
| `univariate-mul-crossover-32` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<32 dense lhs/rhs, two orderings | 40.2 µs | 1.26 µs | ±1.8% !2 | `1247810` |
| `univariate-mul-crossover-64` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<64 dense lhs/rhs, two orderings | 118 µs | 1.85 µs | ±2.2% | `1247810` |
| `univariate-mul-crossover-64` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<64 dense lhs/rhs, two orderings | 80.6 µs | 1.26 µs | ±2.4% | `1247810` |
| `univariate-mul-crossover-128` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<128 dense lhs/rhs, two orderings | 314 µs | 2.45 µs | ±1.7% !1 | `1247810` |
| `univariate-mul-crossover-128` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<128 dense lhs/rhs, two orderings | 159 µs | 1.24 µs | ±2.8% | `1247810` |
| `univariate-mul-crossover-256` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<256 dense lhs/rhs, two orderings | 927 µs | 3.62 µs | ±4.5% | `1247810` |
| `univariate-mul-crossover-256` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<256 dense lhs/rhs, two orderings | 323 µs | 1.26 µs | ±2.1% | `1247810` |
| `univariate-mul-crossover-512` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<512 dense lhs/rhs, two orderings | 2.90 ms | 5.66 µs | ±1.9% | `1247810` |
| `univariate-mul-crossover-512` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<512 dense lhs/rhs, two orderings | 630 µs | 1.23 µs | ±1.0% | `1247810` |
| `univariate-mul-crossover-1024` | `univariate-mul-crossover-schoolbook` · mul · CPolynomial | degree<1024 dense lhs/rhs, two orderings | 10.1 ms | 9.90 µs | ±1.1% | `1247810` |
| `univariate-mul-crossover-1024` | `univariate-mul-crossover-ntt` · NTTFast.Plan.fastMulImpl · CPolynomial | degree<1024 dense lhs/rhs, two orderings | 1.28 ms | 1.25 µs | ±1.6% | `1247810` |

## Multiplicative NTT and Reed-Solomon encoding

*What it is.* The forward and inverse multiplicative NTT over KoalaBear and
BabyBear at `n = 2^8 … 2^16`, the radix-2 reference against the planned radix-4
pipeline (`CompPoly/Univariate/NTTFast/Plan.lean`, correctness in
`CompPoly/Univariate/NTTFast/Correctness/Pipeline.lean`); plan construction as
its own group, since a prover builds it once and reuses it; and Reed-Solomon
encoding as the NTT of a message at three sizes, the definitional encoder
(Horner at every evaluation point) against the certified NTT one
(`CompPoly/Univariate/ReedSolomon/`).

*State.* The largest surface and the largest proof burden in the suite; the
target table in `docs/wiki/autoresearch.md` puts it last for that reason.
*Peer:* Plonky3's NTT and RS encode at the same `n`, SIMD off.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `ntt-koalabear-l8` | `ntt-forward-koalabear` · radix-2 · Array | n = 2^8, two inputs | 105 µs | 103 ns | ±1.8% | `1247810` |
| `ntt-koalabear-l8` | `ntt-forward-koalabear-plan` · radix-4 DIF (plan) · Array | n = 2^8, two inputs | 5.48 µs | 5.35 ns | ±1.7% !1 | `1247810` |
| `ntt-koalabear-l8` | `ntt-inverse-koalabear` · radix-2 · Array | n = 2^8, two inputs | 139 µs | 136 ns | ±1.1% !1 | `1247810` |
| `ntt-koalabear-l8` | `ntt-inverse-koalabear-plan` · radix-4 DIT (plan) · Array | n = 2^8, two inputs | 5.69 µs | 5.55 ns | ±1.6% | `1247810` |
| `ntt-koalabear-l10` | `ntt-forward-koalabear` · radix-2 · Array | n = 2^10, two inputs | 499 µs | 97.5 ns | ±1.9% | `1247810` |
| `ntt-koalabear-l10` | `ntt-forward-koalabear-plan` · radix-4 DIF (plan) · Array | n = 2^10, two inputs | 20.4 µs | 3.98 ns | ±1.5% | `1247810` |
| `ntt-koalabear-l10` | `ntt-inverse-koalabear` · radix-2 · Array | n = 2^10, two inputs | 642 µs | 125 ns | ±1.6% | `1247810` |
| `ntt-koalabear-l10` | `ntt-inverse-koalabear-plan` · radix-4 DIT (plan) · Array | n = 2^10, two inputs | 21.8 µs | 4.26 ns | ±1.5% | `1247810` |
| `ntt-koalabear-l12` | `ntt-forward-koalabear` · radix-2 · Array | n = 2^12, two inputs | 2.39 ms | 97.3 ns | ±1.4% | `1247810` |
| `ntt-koalabear-l12` | `ntt-forward-koalabear-plan` · radix-4 DIF (plan) · Array | n = 2^12, two inputs | 89.5 µs | 3.64 ns | ±0.8% !1 | `1247810` |
| `ntt-koalabear-l12` | `ntt-inverse-koalabear` · radix-2 · Array | n = 2^12, two inputs | 2.93 ms | 119 ns | ±1.1% | `1247810` |
| `ntt-koalabear-l12` | `ntt-inverse-koalabear-plan` · radix-4 DIT (plan) · Array | n = 2^12, two inputs | 93.7 µs | 3.81 ns | ±1.7% | `1247810` |
| `ntt-koalabear-l14` | `ntt-forward-koalabear-plan` · radix-4 DIF (plan) · Array | n = 2^14, two inputs | 399 µs | 3.48 ns | ±2.4% | `1247810` |
| `ntt-koalabear-l14` | `ntt-inverse-koalabear-plan` · radix-4 DIT (plan) · Array | n = 2^14, two inputs | 421 µs | 3.67 ns | ±2.1% | `1247810` |
| `ntt-koalabear-l16` | `ntt-forward-koalabear-plan` · radix-4 DIF (plan) · Array | n = 2^16, two inputs | 1.74 ms | 3.32 ns | ±1.1% | `1247810` |
| `ntt-koalabear-l16` | `ntt-inverse-koalabear-plan` · radix-4 DIT (plan) · Array | n = 2^16, two inputs | 1.84 ms | 3.50 ns | ±1.4% | `1247810` |
| `ntt-babybear-l8` | `ntt-forward-babybear` · radix-2 · Array | n = 2^8, two inputs | 107 µs | 104 ns | ±2.4% | `1247810` |
| `ntt-babybear-l8` | `ntt-forward-babybear-plan` · radix-4 DIF (plan) · Array | n = 2^8, two inputs | 5.62 µs | 5.49 ns | ±1.5% !1 | `1247810` |
| `ntt-babybear-l8` | `ntt-inverse-babybear` · radix-2 · Array | n = 2^8, two inputs | 141 µs | 137 ns | ±1.5% | `1247810` |
| `ntt-babybear-l8` | `ntt-inverse-babybear-plan` · radix-4 DIT (plan) · Array | n = 2^8, two inputs | 5.87 µs | 5.74 ns | ±2.4% | `1247810` |
| `ntt-babybear-l10` | `ntt-forward-babybear` · radix-2 · Array | n = 2^10, two inputs | 499 µs | 97.4 ns | ±1.2% !3 | `1247810` |
| `ntt-babybear-l10` | `ntt-forward-babybear-plan` · radix-4 DIF (plan) · Array | n = 2^10, two inputs | 21.7 µs | 4.23 ns | ±2.3% | `1247810` |
| `ntt-babybear-l10` | `ntt-inverse-babybear` · radix-2 · Array | n = 2^10, two inputs | 632 µs | 123 ns | ±1.3% | `1247810` |
| `ntt-babybear-l10` | `ntt-inverse-babybear-plan` · radix-4 DIT (plan) · Array | n = 2^10, two inputs | 23.0 µs | 4.48 ns | ±3.3% | `1247810` |
| `ntt-babybear-l12` | `ntt-forward-babybear` · radix-2 · Array | n = 2^12, two inputs | 2.40 ms | 97.7 ns | ±1.1% | `1247810` |
| `ntt-babybear-l12` | `ntt-forward-babybear-plan` · radix-4 DIF (plan) · Array | n = 2^12, two inputs | 90.8 µs | 3.69 ns | ±1.2% | `1247810` |
| `ntt-babybear-l12` | `ntt-inverse-babybear` · radix-2 · Array | n = 2^12, two inputs | 2.92 ms | 119 ns | ±1.2% | `1247810` |
| `ntt-babybear-l12` | `ntt-inverse-babybear-plan` · radix-4 DIT (plan) · Array | n = 2^12, two inputs | 92.6 µs | 3.77 ns | ±2.0% | `1247810` |
| `ntt-babybear-l14` | `ntt-forward-babybear-plan` · radix-4 DIF (plan) · Array | n = 2^14, two inputs | 389 µs | 3.39 ns | ±1.1% | `1247810` |
| `ntt-babybear-l14` | `ntt-inverse-babybear-plan` · radix-4 DIT (plan) · Array | n = 2^14, two inputs | 411 µs | 3.58 ns | ±2.4% | `1247810` |
| `ntt-babybear-l16` | `ntt-forward-babybear-plan` · radix-4 DIF (plan) · Array | n = 2^16, two inputs | 1.75 ms | 3.34 ns | ±1.6% | `1247810` |
| `ntt-babybear-l16` | `ntt-inverse-babybear-plan` · radix-4 DIT (plan) · Array | n = 2^16, two inputs | 1.83 ms | 3.50 ns | ±1.9% | `1247810` |
| `ntt-plan-koalabear` | `ntt-plan-koalabear` · ofDomain · Plan | n = 2^12 | 60.9 µs | - | ±0.7% | `1247810` |
| `ntt-plan-koalabear` | `ntt-plan-koalabear` · ofDomain · Plan | n = 2^16 | 846 µs | - | ±2.4% | `1247810` |
| `rs-encode-koalabear-l8` | `rs-encode-koalabear` · encode (Horner per node) · Vector | n = 2^8, rate 1/2, two messages | 832 µs | 3.25 µs | ±0.9% !2 | `1247810` |
| `rs-encode-koalabear-l8` | `rs-encode-koalabear-ntt` · nttCodeword · Vector | n = 2^8, rate 1/2, two messages | 110 µs | 428 ns | ±2.3% | `1247810` |
| `rs-encode-koalabear-l10` | `rs-encode-koalabear` · encode (Horner per node) · Vector | n = 2^10, rate 1/2, two messages | 16.1 ms | 15.8 µs | ±0.4% | `1247810` |
| `rs-encode-koalabear-l10` | `rs-encode-koalabear-ntt` · nttCodeword · Vector | n = 2^10, rate 1/2, two messages | 494 µs | 483 ns | ±0.6% !1 | `1247810` |
| `rs-encode-koalabear-l14` | `rs-encode-koalabear-ntt` · nttCodeword · Vector | n = 2^14, rate 1/2, two messages | 11.1 ms | 678 ns | ±0.7% | `1247810` |

## Univariate root finding

*What it is.* Root search of a univariate polynomial over KoalaBear by the
smooth-subgroup method: the canonical evaluation against the NTT and NTTFast
evaluations of the subgroup, each on the canonical and the fast carrier
(`CompPoly/Univariate/Roots/`, the KoalaBear instance under
`CompPoly/Bivariate/GuruswamiSudan/Root/FieldRoots/`). This is the root oracle
the list decoder below calls.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `univariate-roots-finite-field-koalabear` | `univariate-roots-finite-field-naive` · smooth cyclic, canonical · CPolynomial | degree=66, 65 distinct roots, one of them repeated | 2.35 s | - | n=1 | `1247810` |
| `univariate-roots-finite-field-koalabear` | `univariate-roots-finite-field-ntt` · smooth cyclic, NTT · CPolynomial | degree=66, 65 distinct roots, one of them repeated | 716 ms | - | ±0.5% (n=2) | `1247810` |
| `univariate-roots-finite-field-koalabear` | `univariate-roots-finite-field-nttfast` · smooth cyclic, NTTFast · CPolynomial | degree=66, 65 distinct roots, one of them repeated | 231 ms | - | ±0.4% | `1247810` |
| `univariate-roots-finite-field-koalabear` | `univariate-roots-finite-field-fast-naive` · smooth cyclic, canonical · CPolynomial | degree=66, 65 distinct roots, one of them repeated | 443 ms | - | ±0.0% (n=4) | `1247810` |
| `univariate-roots-finite-field-koalabear` | `univariate-roots-finite-field-fast-ntt` · smooth cyclic, NTT · CPolynomial | degree=66, 65 distinct roots, one of them repeated | 283 ms | - | ±0.2% | `1247810` |
| `univariate-roots-finite-field-koalabear` | `univariate-roots-finite-field-fast-nttfast` · smooth cyclic, NTTFast · CPolynomial | degree=66, 65 distinct roots, one of them repeated | 76.8 ms | - | ±0.8% | `1247810` |

## Multivariate and multilinear evaluation

*What it is.* Dense and sparse evaluation of computable multivariate
polynomials over KoalaBear and Goldilocks (`CompPoly/Multivariate/`), and the
multilinear forms (`CompPoly/Multilinear/`): coefficient-form evaluation,
Boolean-hypercube-form evaluation, and many multilinear extensions at one
point.

*Rows.* Each group compares evaluation strategies, direct against Horner (or
scalar-loop against by-layers for the many-MLE group), and over KoalaBear the
canonical `ZMod` carrier against the fast one. There is no fast twin of the
data structures themselves; the multivariate carrier is an `ExtTreeMap`
quotient, so headroom here is in the structure rather than the field.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `multivariate-dense-koalabear` | `multivariate-dense-eval` · eval · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, dense coeffs, 32 points | 588 µs | - | ±1.6% | `1247810` |
| `multivariate-dense-koalabear` | `multivariate-dense-horner` · evalHorner · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, dense coeffs, 32 points | 284 µs | - | ±1.6% | `1247810` |
| `multivariate-dense-koalabear` | `multivariate-dense-eval-fast` · eval · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, dense coeffs, 32 points | 211 µs | - | ±1.6% | `1247810` |
| `multivariate-dense-koalabear` | `multivariate-dense-horner-fast` · evalHorner · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, dense coeffs, 32 points | 79.9 µs | - | ±1.7% | `1247810` |
| `multivariate-sparse-koalabear` | `multivariate-sparse-eval` · eval · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, one nonzero per 16 coeffs, 32 points | 32.6 µs | - | ±1.1% | `1247810` |
| `multivariate-sparse-koalabear` | `multivariate-sparse-horner` · evalHorner · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, one nonzero per 16 coeffs, 32 points | 17.0 µs | - | ±1.7% | `1247810` |
| `multivariate-sparse-koalabear` | `multivariate-sparse-eval-fast` · eval · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, one nonzero per 16 coeffs, 32 points | 13.1 µs | - | ±2.7% | `1247810` |
| `multivariate-sparse-koalabear` | `multivariate-sparse-horner-fast` · evalHorner · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, one nonzero per 16 coeffs, 32 points | 4.53 µs | - | ±1.6% | `1247810` |
| `multivariate-dense-goldilocks` | `multivariate-dense-eval-goldilocks` · eval · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, dense coeffs, 32 points | 3.90 ms | - | ±0.6% | `1247810` |
| `multivariate-dense-goldilocks` | `multivariate-dense-horner-goldilocks` · evalHorner · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, dense coeffs, 32 points | 1.33 ms | - | ±1.8% | `1247810` |
| `multivariate-sparse-goldilocks` | `multivariate-sparse-eval-goldilocks` · eval · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, one nonzero per 16 coeffs, 32 points | 151 µs | - | ±0.7% !1 | `1247810` |
| `multivariate-sparse-goldilocks` | `multivariate-sparse-horner-goldilocks` · evalHorner · CMvPolynomial | 5 vars, 512 generated terms, exponent<16, one nonzero per 16 coeffs, 32 points | 71.0 µs | - | ±1.2% | `1247810` |
| `multilinear-coeff-koalabear` | `multilinear-coeff-eval` · eval · CMlPolynomial | 8 vars, 256 coefficients, 32 points | 176 µs | - | ±1.5% | `1247810` |
| `multilinear-coeff-koalabear` | `multilinear-coeff-horner` · evalHorner · CMlPolynomial | 8 vars, 256 coefficients, 32 points | 6.68 µs | - | ±1.8% | `1247810` |
| `multilinear-coeff-koalabear` | `multilinear-coeff-eval-fast` · eval · CMlPolynomial | 8 vars, 256 coefficients, 32 points | 129 µs | - | ±1.4% !1 | `1247810` |
| `multilinear-coeff-koalabear` | `multilinear-coeff-horner-fast` · evalHorner · CMlPolynomial | 8 vars, 256 coefficients, 32 points | 3.11 µs | - | ±1.9% | `1247810` |
| `multilinear-hypercube-koalabear` | `multilinear-hypercube-eval` · eval · CMlPolynomialEval | 8 vars, 256 hypercube values, 32 points | 200 µs | - | ±1.4% | `1247810` |
| `multilinear-hypercube-koalabear` | `multilinear-hypercube-mle` · evalMle · CMlPolynomialEval | 8 vars, 256 hypercube values, 32 points | 10.1 µs | - | ±1.6% | `1247810` |
| `multilinear-hypercube-koalabear` | `multilinear-hypercube-eval-fast` · eval · CMlPolynomialEval | 8 vars, 256 hypercube values, 32 points | 114 µs | - | ±2.2% | `1247810` |
| `multilinear-hypercube-koalabear` | `multilinear-hypercube-mle-fast` · evalMle · CMlPolynomialEval | 8 vars, 256 hypercube values, 32 points | 3.36 µs | - | ±1.8% | `1247810` |
| `multilinear-many-mle-koalabear` | `multilinear-many-mle-scalar-loop` · evalManyMle · Array CMlPolynomialEval | 256 hypercube tables, 12 vars, 4096 values each, one shared point | 36.3 ms | - | ±0.3% | `1247810` |
| `multilinear-many-mle-koalabear` | `multilinear-many-mle-by-layers` · evalManyMleByLayers · Array CMlPolynomialEval | 256 hypercube tables, 12 vars, 4096 values each, one shared point | 74.6 ms | - | ±0.4% | `1247810` |
| `multilinear-many-mle-koalabear` | `multilinear-many-mle-scalar-loop-fast` · evalManyMle · Array CMlPolynomialEval | 256 hypercube tables, 12 vars, 4096 values each, one shared point | 9.56 ms | - | ±3.4% | `1247810` |
| `multilinear-many-mle-koalabear` | `multilinear-many-mle-by-layers-fast` · evalManyMleByLayers · Array CMlPolynomialEval | 256 hypercube tables, 12 vars, 4096 values each, one shared point | 6.60 ms | - | ±1.4% | `1247810` |
| `multilinear-coeff-goldilocks` | `multilinear-coeff-eval-goldilocks` · eval · CMlPolynomial | 8 vars, 256 coefficients, 32 points | 529 µs | - | ±0.9% | `1247810` |
| `multilinear-coeff-goldilocks` | `multilinear-coeff-horner-goldilocks` · evalHorner · CMlPolynomial | 8 vars, 256 coefficients, 32 points | 110 µs | - | ±1.5% | `1247810` |
| `multilinear-hypercube-goldilocks` | `multilinear-hypercube-eval-goldilocks` · eval · CMlPolynomialEval | 8 vars, 256 hypercube values, 32 points | 986 µs | - | ±0.4% !2 | `1247810` |
| `multilinear-hypercube-goldilocks` | `multilinear-hypercube-mle-goldilocks` · evalMle · CMlPolynomialEval | 8 vars, 256 hypercube values, 32 points | 230 µs | - | ±1.6% | `1247810` |

## Bivariate operations

*What it is.* Full evaluation of nested-univariate bivariate polynomials over
KoalaBear, Goldilocks and BN254, direct against Horner in either variable order
(`CompPoly/Bivariate/Basic.lean`), and division by a linear factor `Y - f(X)`
at three `Y`-degrees over the same three fields, Horner deflation against
generic `divByMonic` (`CompPoly/Bivariate/Factor.lean`). These are the
primitives the list decoder is built from.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `bivariate-full-koalabear` | `bivariate-full-eval-naive` · evalEval · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 30.7 µs | - | ±2.3% | `1247810` |
| `bivariate-full-koalabear` | `bivariate-full-eval-horner-yx` · evalEvalHornerYThenX · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 130 µs | - | ±1.9% | `1247810` |
| `bivariate-full-koalabear` | `bivariate-full-eval-horner-xy` · evalEvalHornerXThenY · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 17.9 µs | - | ±2.5% | `1247810` |
| `bivariate-full-koalabear` | `bivariate-full-eval-naive-fast` · evalEval · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 4.21 µs | - | ±2.3% | `1247810` |
| `bivariate-full-koalabear` | `bivariate-full-eval-horner-yx-fast` · evalEvalHornerYThenX · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 42.3 µs | - | ±1.0% !1 | `1247810` |
| `bivariate-full-koalabear` | `bivariate-full-eval-horner-xy-fast` · evalEvalHornerXThenY · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 657 ns | - | ±0.5% | `1247810` |
| `bivariate-full-goldilocks` | `bivariate-full-eval-naive-goldilocks` · evalEval · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 91.0 µs | - | ±4.7% | `1247810` |
| `bivariate-full-goldilocks` | `bivariate-full-eval-horner-yx-goldilocks` · evalEvalHornerYThenX · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 223 µs | - | ±1.5% !1 | `1247810` |
| `bivariate-full-goldilocks` | `bivariate-full-eval-horner-xy-goldilocks` · evalEvalHornerXThenY · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 138 µs | - | ±0.8% !2 | `1247810` |
| `bivariate-full-bn254` | `bivariate-full-eval-naive-bn254` · evalEval · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 111 µs | - | ±3.2% | `1247810` |
| `bivariate-full-bn254` | `bivariate-full-eval-horner-yx-bn254` · evalEvalHornerYThenX · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 296 µs | - | ±1.5% | `1247810` |
| `bivariate-full-bn254` | `bivariate-full-eval-horner-xy-bn254` · evalEvalHornerXThenY · CBivariate | xDegree<8, yDegree<64, one nonzero per 4 coeffs, 32 points | 196 µs | - | ±0.8% !2 | `1247810` |
| `bivariate-divlinear-koalabear-y8` | `bivariate-deflate-horner-y8` · divByLinearY · CBivariate | xDegree<8, yDegree<8, divisor Y - f with deg f < 8 | 250 µs | - | ±1.4% !1 | `1247810` |
| `bivariate-divlinear-koalabear-y8` | `bivariate-deflate-divbymonic-y8` · divByMonic · CBivariate | xDegree<8, yDegree<8, divisor Y - f with deg f < 8 | 1.53 ms | - | ±2.0% | `1247810` |
| `bivariate-divlinear-koalabear-y16` | `bivariate-deflate-horner-y16` · divByLinearY · CBivariate | xDegree<8, yDegree<16, divisor Y - f with deg f < 8 | 1.00 ms | - | ±1.6% !1 | `1247810` |
| `bivariate-divlinear-koalabear-y16` | `bivariate-deflate-divbymonic-y16` · divByMonic · CBivariate | xDegree<8, yDegree<16, divisor Y - f with deg f < 8 | 15.0 ms | - | ±0.4% | `1247810` |
| `bivariate-divlinear-koalabear-y32` | `bivariate-deflate-horner-y32` · divByLinearY · CBivariate | xDegree<8, yDegree<32, divisor Y - f with deg f < 8 | 4.05 ms | - | ±1.6% | `1247810` |
| `bivariate-divlinear-koalabear-y32` | `bivariate-deflate-divbymonic-y32` · divByMonic · CBivariate | xDegree<8, yDegree<32, divisor Y - f with deg f < 8 | 185 ms | - | ±0.6% | `1247810` |
| `bivariate-divlinear-goldilocks-y8` | `bivariate-deflate-horner-y8-goldilocks` · divByLinearY · CBivariate | xDegree<8, yDegree<8, divisor Y - f with deg f < 8 | 988 µs | - | ±2.8% | `1247810` |
| `bivariate-divlinear-goldilocks-y8` | `bivariate-deflate-divbymonic-y8-goldilocks` · divByMonic · CBivariate | xDegree<8, yDegree<8, divisor Y - f with deg f < 8 | 4.05 ms | - | ±1.0% | `1247810` |
| `bivariate-divlinear-goldilocks-y16` | `bivariate-deflate-horner-y16-goldilocks` · divByLinearY · CBivariate | xDegree<8, yDegree<16, divisor Y - f with deg f < 8 | 4.02 ms | - | ±1.8% | `1247810` |
| `bivariate-divlinear-goldilocks-y16` | `bivariate-deflate-divbymonic-y16-goldilocks` · divByMonic · CBivariate | xDegree<8, yDegree<16, divisor Y - f with deg f < 8 | 32.4 ms | - | ±0.9% | `1247810` |
| `bivariate-divlinear-goldilocks-y32` | `bivariate-deflate-horner-y32-goldilocks` · divByLinearY · CBivariate | xDegree<8, yDegree<32, divisor Y - f with deg f < 8 | 17.1 ms | - | ±1.6% | `1247810` |
| `bivariate-divlinear-goldilocks-y32` | `bivariate-deflate-divbymonic-y32-goldilocks` · divByMonic · CBivariate | xDegree<8, yDegree<32, divisor Y - f with deg f < 8 | 322 ms | - | ±0.4% | `1247810` |
| `bivariate-divlinear-bn254-y8` | `bivariate-deflate-horner-y8-bn254` · divByLinearY · CBivariate | xDegree<8, yDegree<8, divisor Y - f with deg f < 8 | 1.20 ms | - | ±2.9% | `1247810` |
| `bivariate-divlinear-bn254-y8` | `bivariate-deflate-divbymonic-y8-bn254` · divByMonic · CBivariate | xDegree<8, yDegree<8, divisor Y - f with deg f < 8 | 6.17 ms | - | ±1.0% !1 | `1247810` |
| `bivariate-divlinear-bn254-y16` | `bivariate-deflate-horner-y16-bn254` · divByLinearY · CBivariate | xDegree<8, yDegree<16, divisor Y - f with deg f < 8 | 4.87 ms | - | ±3.3% | `1247810` |
| `bivariate-divlinear-bn254-y16` | `bivariate-deflate-divbymonic-y16-bn254` · divByMonic · CBivariate | xDegree<8, yDegree<16, divisor Y - f with deg f < 8 | 48.1 ms | - | ±0.5% | `1247810` |
| `bivariate-divlinear-bn254-y32` | `bivariate-deflate-horner-y32-bn254` · divByLinearY · CBivariate | xDegree<8, yDegree<32, divisor Y - f with deg f < 8 | 19.5 ms | - | ±2.3% | `1247810` |
| `bivariate-divlinear-bn254-y32` | `bivariate-deflate-divbymonic-y32-bn254` · divByMonic · CBivariate | xDegree<8, yDegree<32, divisor Y - f with deg f < 8 | 451 ms | - | ±0.4% (n=4) | `1247810` |

## Guruswami-Sudan list decoding

*What it is.* The stages of the Guruswami-Sudan decoder over KoalaBear
(`CompPoly/Bivariate/GuruswamiSudan/`): construction and solving of the dense
interpolation system (copying against in-place elimination); interpolation end
to end by dense linear algebra, Lee-O'Sullivan (direct and subproduct), the
approximant basis and the budgeted hybrid; root finding by Roth-Ruckenstein and
Alekhnovich, each with the nonlinear and the NTTFast field-root oracle; the
packed distance filter; and the full core with and without the filter, on a
codeword and on a perturbed received word. Every stage runs on the canonical
and on the fast carrier. The `small` shapes are the ones a single iteration
can afford at this preset.

*State.* Several rows are `n=1` and carry no dispersion; they are listed so
that the record is complete, and a smaller shape is the fix before any of them
is optimised. *Peer:* none in production; do not invent one.

| Group | Row | Shape | Median | Per unit | Spread | Best at |
|---|---|---|---:|---:|---:|---|
| `guruswami-sudan-interp-system-small-koalabear` | `guruswami-sudan-interp-system` · Interpolation system construction · DenseMatrix | n=64,k=16,m=2,D=75 | 60.7 ms | - | ±0.8% | `1247810` |
| `guruswami-sudan-interp-system-small-koalabear` | `guruswami-sudan-interp-system-fast` · Interpolation system construction · DenseMatrix | n=64,k=16,m=2,D=75 | 26.6 ms | - | ±0.2% | `1247810` |
| `guruswami-sudan-interp-solve-small-koalabear` | `guruswami-sudan-interp-solve-copying` · Homogeneous interpolation solve, copying · DenseMatrix | n=64,k=16,m=2,D=75 | 1.29 s | - | n=1 | `1247810` |
| `guruswami-sudan-interp-solve-small-koalabear` | `guruswami-sudan-interp-solve` · Homogeneous interpolation solve, in-place · DenseMatrix | n=64,k=16,m=2,D=75 | 411 ms | - | ±0.0% (n=4) | `1247810` |
| `guruswami-sudan-interp-solve-small-koalabear` | `guruswami-sudan-interp-solve-copying-fast` · Homogeneous interpolation solve, copying · DenseMatrix | n=64,k=16,m=2,D=75 | 778 ms | - | ±0.6% (n=2) | `1247810` |
| `guruswami-sudan-interp-solve-small-koalabear` | `guruswami-sudan-interp-solve-inplace-fast` · Homogeneous interpolation solve, in-place · DenseMatrix | n=64,k=16,m=2,D=75 | 46.7 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-dense-small` · Dense linear · CBivariate | n=64,k=16,m=2,D=75 | 456 ms | - | ±0.9% (n=4) | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-lee-direct-small` · Lee-O'Sullivan direct · CBivariate | n=64,k=16,m=2,D=75 | 12.2 ms | - | ±0.4% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-lee-subproduct-small` · Lee-O'Sullivan subproduct · CBivariate | n=64,k=16,m=2,D=75 | 15.1 ms | - | ±0.4% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-dense-small-fast` · Dense linear · CBivariate | n=64,k=16,m=2,D=75 | 49.4 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-lee-direct-small-fast` · Lee-O'Sullivan direct · CBivariate | n=64,k=16,m=2,D=75 | 2.06 ms | - | ±1.3% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-lee-subproduct-small-fast` · Lee-O'Sullivan subproduct · CBivariate | n=64,k=16,m=2,D=75 | 3.71 ms | - | ±2.4% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-approximant-small` · Approximant basis (PM-Basis) · CBivariate | n=64,k=16,m=2,D=75 | 168 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-hybrid-small` · Hybrid (budgeted Lee-O'Sullivan with approximant fallback) · CBivariate | n=64,k=16,m=2,D=75 | 15.6 ms | - | ±1.5% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-approximant-small-fast` · Approximant basis (PM-Basis) · CBivariate | n=64,k=16,m=2,D=75 | 60.2 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-interp-small-koalabear` | `guruswami-sudan-interp-hybrid-small-fast` · Hybrid (budgeted Lee-O'Sullivan with approximant fallback) · CBivariate | n=64,k=16,m=2,D=75 | 3.64 ms | - | ±1.4% | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-roth` · Roth-Ruckenstein root finding with nonlinear field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 31.7 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-roth-nttfast` · Roth-Ruckenstein root finding with NTTFast field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 32.2 ms | - | ±0.5% !1 | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-alekhnovich` · Alekhnovich root finding with nonlinear field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 13.8 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-alekhnovich-nttfast` · Alekhnovich root finding with NTTFast field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 14.6 ms | - | ±0.8% | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-roth-fast` · Roth-Ruckenstein root finding with nonlinear field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 7.54 ms | - | ±0.9% | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-roth-fast-nttfast` · Roth-Ruckenstein root finding with NTTFast field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 7.78 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-alekhnovich-fast` · Alekhnovich root finding with nonlinear field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 3.36 ms | - | ±1.1% !1 | `1247810` |
| `guruswami-sudan-root-koalabear` | `guruswami-sudan-root-alekhnovich-fast-nttfast` · Alekhnovich root finding with NTTFast field-root equations · CBivariate | k=32,Q=(Y-p)(Y-(p+7)) | 3.64 ms | - | ±1.6% | `1247810` |
| `guruswami-sudan-packed-filter-koalabear` | `guruswami-sudan-packed-filter` · Packed distance filtering · CPolynomial | n=128,k=32,cand=128,r=0 | 116 ms | - | ±0.4% | `1247810` |
| `guruswami-sudan-packed-filter-koalabear` | `guruswami-sudan-packed-filter-fast` · Packed distance filtering · CPolynomial | n=128,k=32,cand=128,r=0 | 10.8 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-interp-noncodeword-small-koalabear` | `guruswami-sudan-interp-dense-noncodeword-small` · Dense linear · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 602 ms | - | ±0.0% (n=3) | `1247810` |
| `guruswami-sudan-interp-noncodeword-small-koalabear` | `guruswami-sudan-interp-lee-direct-noncodeword-small` · Lee-O'Sullivan direct · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 83.6 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-interp-noncodeword-small-koalabear` | `guruswami-sudan-interp-lee-subproduct-noncodeword-small` · Lee-O'Sullivan subproduct · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 86.7 ms | - | ±0.7% | `1247810` |
| `guruswami-sudan-interp-noncodeword-small-koalabear` | `guruswami-sudan-interp-dense-noncodeword-small-fast` · Dense linear · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 57.4 ms | - | ±0.3% !2 | `1247810` |
| `guruswami-sudan-interp-noncodeword-small-koalabear` | `guruswami-sudan-interp-lee-direct-noncodeword-small-fast` · Lee-O'Sullivan direct · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 14.6 ms | - | ±1.7% | `1247810` |
| `guruswami-sudan-interp-noncodeword-small-koalabear` | `guruswami-sudan-interp-lee-subproduct-noncodeword-small-fast` · Lee-O'Sullivan subproduct · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 16.1 ms | - | ±0.9% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-dense-small` · Dense linear + RR roots · CBivariate | n=64,k=16,m=2,D=75 | 448 ms | - | ±0.3% (n=4) | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-dense-small-alekhnovich` · Dense linear + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75 | 451 ms | - | ±0.0% (n=4) !1 | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-direct-small` · Lee-O'Sullivan direct + RR roots · CBivariate | n=64,k=16,m=2,D=75 | 9.61 ms | - | ±0.9% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-direct-small-alekhnovich` · Lee-O'Sullivan direct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75 | 11.3 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-subproduct-small` · Lee-O'Sullivan subproduct + RR roots · CBivariate | n=64,k=16,m=2,D=75 | 12.3 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-subproduct-small-alekhnovich` · Lee-O'Sullivan subproduct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75 | 14.0 ms | - | ±0.9% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-dense-small-fast` · Dense linear + RR roots · CBivariate | n=64,k=16,m=2,D=75 | 50.0 ms | - | ±0.3% !1 | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-dense-small-alekhnovich-fast` · Dense linear + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75 | 50.9 ms | - | ±0.8% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-direct-small-fast` · Lee-O'Sullivan direct + RR roots · CBivariate | n=64,k=16,m=2,D=75 | 2.72 ms | - | ±2.2% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-direct-small-alekhnovich-fast` · Lee-O'Sullivan direct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75 | 3.29 ms | - | ±1.2% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-subproduct-small-fast` · Lee-O'Sullivan subproduct + RR roots · CBivariate | n=64,k=16,m=2,D=75 | 4.28 ms | - | ±0.9% | `1247810` |
| `guruswami-sudan-core-small-koalabear` | `guruswami-sudan-core-lee-subproduct-small-alekhnovich-fast` · Lee-O'Sullivan subproduct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75 | 4.77 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-dense-small` · Dense linear + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 453 ms | - | ±0.7% (n=4) | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-dense-small-alekhnovich` · Dense linear + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 455 ms | - | ±0.0% (n=4) !1 | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-small` · Lee-O'Sullivan direct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 9.68 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-small-alekhnovich` · Lee-O'Sullivan direct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 11.3 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-small` · Lee-O'Sullivan subproduct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 12.7 ms | - | ±0.8% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich` · Lee-O'Sullivan subproduct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 14.2 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-dense-small-fast` · Dense linear + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 50.2 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-dense-small-alekhnovich-fast` · Dense linear + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 51.4 ms | - | ±1.1% !1 | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-small-fast` · Lee-O'Sullivan direct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 2.88 ms | - | ±1.1% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-small-alekhnovich-fast` · Lee-O'Sullivan direct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 3.32 ms | - | ±1.2% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-small-fast` · Lee-O'Sullivan subproduct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 4.26 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-filtered-core-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-small-alekhnovich-fast` · Lee-O'Sullivan subproduct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,r=0 | 4.87 ms | - | ±1.0% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-dense-noncodeword-small` · Dense linear + RR roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 599 ms | - | ±0.3% (n=3) | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-dense-noncodeword-small-alekhnovich` · Dense linear + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 595 ms | - | ±0.0% (n=3) | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-direct-noncodeword-small` · Lee-O'Sullivan direct + RR roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 130 ms | - | ±3.2% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-direct-noncodeword-small-alekhnovich` · Lee-O'Sullivan direct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 95.2 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-subproduct-noncodeword-small` · Lee-O'Sullivan subproduct + RR roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 127 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-subproduct-noncodeword-small-alekhnovich` · Lee-O'Sullivan subproduct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 98.2 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-dense-noncodeword-small-fast` · Dense linear + RR roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 56.5 ms | - | ±0.3% !1 | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-dense-noncodeword-small-alekhnovich-fast` · Dense linear + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 55.8 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-direct-noncodeword-small-fast` · Lee-O'Sullivan direct + RR roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 26.6 ms | - | ±0.9% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-direct-noncodeword-small-alekhnovich-fast` · Lee-O'Sullivan direct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 19.5 ms | - | ±0.5% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-subproduct-noncodeword-small-fast` · Lee-O'Sullivan subproduct + RR roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 28.8 ms | - | ±0.6% | `1247810` |
| `guruswami-sudan-core-noncodeword-small-koalabear` | `guruswami-sudan-core-lee-subproduct-noncodeword-small-alekhnovich-fast` · Lee-O'Sullivan subproduct + Alekhnovich roots · CBivariate | n=64,k=16,m=2,D=75,errors=every3 | 21.3 ms | - | ±0.7% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-dense-noncodeword-small` · Dense linear + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 594 ms | - | ±0.2% (n=3) | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-dense-noncodeword-small-alekhnovich` · Dense linear + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 590 ms | - | ±0.0% (n=3) | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-noncodeword-small` · Lee-O'Sullivan direct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 125 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-noncodeword-small-alekhnovich` · Lee-O'Sullivan direct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 96.1 ms | - | ±0.8% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small` · Lee-O'Sullivan subproduct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 127 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small-alekhnovich` · Lee-O'Sullivan subproduct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 98.1 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-dense-noncodeword-small-fast` · Dense linear + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 56.3 ms | - | ±0.4% !1 | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-dense-noncodeword-small-alekhnovich-fast` · Dense linear + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 55.4 ms | - | ±0.4% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-noncodeword-small-fast` · Lee-O'Sullivan direct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 26.4 ms | - | ±0.7% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-direct-noncodeword-small-alekhnovich-fast` · Lee-O'Sullivan direct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 19.2 ms | - | ±0.4% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small-fast` · Lee-O'Sullivan subproduct + RR roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 27.9 ms | - | ±0.3% | `1247810` |
| `guruswami-sudan-filtered-core-noncodeword-small-koalabear` | `guruswami-sudan-filtered-core-lee-subproduct-noncodeword-small-alekhnovich-fast` · Lee-O'Sullivan subproduct + Alekhnovich roots + filter · CBivariate | n=64,k=16,m=2,D=75,errors=every3,r=22 | 20.8 ms | - | ±0.7% | `1247810` |
