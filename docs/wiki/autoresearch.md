# Autoresearch: the optimisation loop

How an agent makes a fast implementation faster without anyone watching: edit,
prove, measure, keep or revert. [`benchmarking.md`](benchmarking.md) owns how the
suite measures; [`bench/README.md`](../../bench/README.md) is the operator's guide
to the executable. This page owns the loop that sits on top of both.

## What the loop is

CompPoly's fast paths are compiled Lean with a proof that each one equals its
specification. That makes an optimisation loop safer here than in an ordinary
library: a candidate that is fast but wrong does not build. The loop is therefore
three gates in a fixed order, and a decision:

1. **Proof gate.** `lake build` must succeed. The refinement theorem for the
   kernel being edited (`mul_eq_mulTbl`, `toField_mul`, `invGcdRaw_eq_inv`, and
   so on) still closes, or the change is wrong.
2. **Digest gate.** `lake exe CompPolyBench --validate-only --groups <target>`
   must exit 0. Every implementation in the group still agrees with the others.
3. **Measurement.** `./scripts/bench-ab.sh run <target>` compares the current
   build against a frozen baseline on this machine, turn about, and prints one
   verdict per row.
4. **Decision.** Keep the change only on `faster` with no `SUSPECT`. Otherwise
   revert.

The objective is the **ratio** the comparison prints, never a nanosecond figure.
Absolute numbers on a laptop drift by up to 2x between runs while ratios
measured turn about hold to a few percent, which is why the driver interleaves
the two binaries rather than comparing against a number written down yesterday.

## Protocol

Run from the repository root.

```bash
# once, on the clean commit the work starts from
./scripts/bench-ab.sh freeze

# each iteration
#   1. edit one kernel
lake build                                            # proofs still close
lake build CompPolyBenchLib CompPolyBench             # bench still builds
lake exe CompPolyBench --validate-only --groups fields-koalabear-mul
./scripts/bench-ab.sh run fields-koalabear-mul        # the verdict
#   2. keep on `faster` with no SUSPECT, else `git checkout -- <files>`
#   3. after a kept change, make it the new baseline
./scripts/bench-ab.sh freeze --force

# when the session ends
lake test
./scripts/lint-style.sh
lake exe axiomsweep --check
```

Rules the loop follows:

- **One change per iteration.** A verdict on two edits says nothing about either.
- **No new warnings.** Both builds were warning-clean when the loop began; keep
  them so.
- **Build before measuring, never during.** The driver builds once and then calls
  the binaries directly. Do not run `lake exe` or `lake build` while a run is in
  flight, and do not edit under `bench/` in the same iteration as a kernel.
- **Stop and read on `mismatch`, `missing`, or `SUSPECT`.** These are not
  measurements. A `mismatch` means the candidate computed a different digest from
  the baseline on identical inputs; `missing` means the set of rows changed;
  `SUSPECT` means the candidate is faster than its problem allows.
- **Never stage with `git add -A`.** Name the files.

## Reading the verdict

The comparison prints one Markdown table across every compared row. The side
columns are per-iteration medians in picoseconds, one median per invocation, of
which the driver runs five per side by default.

| Verdict | Meaning |
|---|---|
| `faster` | the ratio of medians is at least the threshold (default 5%) below 1, **and** every candidate run beat every baseline run |
| `slower` | the mirror image |
| `same` | anything else, including a real change too small to clear the threshold |
| `mismatch (checksum)` | the two builds disagree on a row's digest; exit 3 |
| `mismatch (work_units)` | the two builds disagree on a row's problem size; exit 3 |
| `missing (side)` | the row is absent from at least one of that side's files; exit 3 |
| `unjudged (zero median)` | the clock could not resolve the row |

Strict separation of two groups of five happens by chance one time in 252. With
`BENCH_AB_ROUNDS=1` it happens one time in two, and the header says so; a
one-round run is a smoke test, not a verdict.

`SUSPECT` is appended to a verdict, never a verdict on its own. Its three reasons
are the dead-body signatures recorded in `BENCHMARKING.md` §12.6 and §12.7: a
ratio below 0.1 with an unchanged digest, a one-unit row cheaper than the empty
harness loop, or a chained row cheaper per operation than the two-instruction
chain floor. In each case the compiler folded the body, the digest pass did not
notice because it is separate and untimed, and the number means nothing.

The header also reports **drift**: the candidate-over-baseline ratio of each
harness row, which the driver includes in every run. A ratio outside ±10% is a
warning that the machine was not steady across the two sides, and the run should
be repeated rather than read.

## What keeps the loop honest

- The gate is the proof. A kernel routed through `@[implemented_by]` has no
  proof gate, because that attribute substitutes code without one. The single
  use in `CompPoly/Univariate/Roots/Shoup/Basic.lean` is outside the loop, and no
  new one may be introduced by it. `@[csimp]` with an equality theorem, or a twin
  definition with an `_eq_` theorem that the call site depends on, are the two
  accepted shapes.
- The trusted code base does not move. `native_decide` stays forbidden; see the
  TCB policy in [`AGENTS.md`](../../AGENTS.md).
- Inputs are seeded per group, so digests are comparable across binaries. The
  `mismatch` verdict is that comparison. It is the only correctness check a
  single-row group gets beyond the build, so do not disable it.
- Harness rows are compared like any other but exempt from the floor alarm,
  because they define the floor.

## Targets

Ordered by how well each is gated and how much headroom is documented. Group
keys are the argument to `bench-ab.sh run`; `lake exe CompPolyBench --list`
is authoritative.

| Target | Groups | Fast implementation | Gate | Idea |
|---|---|---|---|---|
| `Ext.mul`, O(d³) → O(d²) | `fields-extension-{koalabear-ext4,babybear-ext4,koalabear-ext5,koalabear-ext6}-mul` | `CompPoly/Fields/Extension/Arithmetic.lean` (`mulTbl`, `red`) | `mul_eq_mulTbl` (`@[csimp]`), `toQuot_mul` in `CompPoly/Fields/Extension/Bridge.lean` | schoolbook into a flat `2d - 1` accumulator, one `red` fold, `red` hoisted per modulus. Single-row groups: the build and the cross-binary digest are the only gates |
| Base-field kernels | `fields-{koalabear,babybear,mersenne31,goldilocks}-{mul,add,inv,pow}`, `fields-{bn254,bls12-381,bls12-377}-mul` | `CompPoly/Fields/Montgomery/Native32Field.lean`, `CompPoly/Fields/Goldilocks/Fast.lean`, `CompPoly/Fields/Mersenne31/Fast.lean`, `CompPoly/Fields/Montgomery/Native64x8Mul.lean` | `toField_*`, `ringEquiv`, `instField` | two to four digest-cross-checked rows per group; the best-behaved targets |
| Eight-limb inversion | `fields-mont64x8-{bn254,bls12-381,bls12-377}-inv` | `CompPoly/Fields/Montgomery/Native64x8InvDefs.lean` | `invGcdRaw_eq_inv` and its bounds chain in `CompPoly/Fields/Montgomery/Native64x8Inv.lean` | three algorithms in one group, one digest class |
| Many-polynomial evaluation | `univariate-many-one-point-koalabear`, `univariate-dense-*` | `CompPoly/Univariate/ManyEval/Basic.lean`, `CompPoly/Univariate/Raw/Ops.lean` | `evalManyHorner_eq_map_eval`, `evalManySharedPowers_eq_map_eval`, `eval₂_horner_eq_eval₂` | plain array loops with short refinement proofs |
| Tower scalar kernels | `fields-tower-bt{8,64}-mul`, `fields-tower-bt64-inv-word`, `fields-tower-bt128-{mul,inv}` | `CompPoly/Fields/Binary/Tower/FastDefs.lean` | `mul64T_eq_mul64`, `inv64T_eq_inv64`, `toConcrete_*` in `CompPoly/Fields/Binary/Tower/Fast.lean` | table twins already close to optimal; low headroom |
| Additive NTT | `additive-ntt-btf3-l2-r2`, `additive-ntt-btf3-l4-r2`, `additive-ntt-btf4-l7-r2` | `CompPoly/Fields/Binary/AdditiveNTT/Impl.lean` | `computableAdditiveNTTFast_eq_computableAdditiveNTT` | the `btf4` group is fast-only; rely on the build |
| NTTFast stages | `ntt-{koalabear,babybear}-l{8,10,12,14,16}`, `ntt-plan-koalabear` | `CompPoly/Univariate/NTTFast/Plan.lean` | `CompPoly/Univariate/NTTFast/Correctness/Pipeline.lean` | largest surface and largest proof burden; last |

Prerequisites rather than loop iterations, because a definition is missing
before any optimisation applies: `Ext` over the Montgomery carrier (no
`Fintype (FastField _)` instance), an Itoh-Tsujii inverse (no `Ext.frobenius` or
`Ext.norm`), `clMul` from issue #129 (no group measures `carryLessMul`, and the
`GF(2^64)` groups are blocked by the `Fintype BF64` hang described in
[`benchmarking.md`](benchmarking.md)), and polynomial `pow` (no group).

## Stop condition

The loop can say "faster than before". It cannot say "fast enough": that needs
the peer measured on the same CPU, which is the external comparison of
`BENCHMARKING.md` §13 and has not been built. Until it lands, treat the bar there
as the target: within two to five times the *scalar* Plonky3 or Binius kernel for
the same operation at the same size.
