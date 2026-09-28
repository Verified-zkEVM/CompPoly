/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Harness.Sink

/-!
# Operation Chains

Measuring one field operation, rather than measuring the harness around it.

The suite's ordinary body shape performs its operation once per timed iteration
and reads its operands out of a pool: `xs.getD (i % xs.size) unit`. For a
polynomial that is fine. For a field multiply it is not — the generated C for
`goldilocks-mul-fast` performs two `lean_nat_mod`s, two `lean_nat_add`s, two
`lean_nat_dec_lt`s, two `lean_array_get_size`s, two `lean_array_fget`s, an
unbox and thirteen refcount operations around a single multiply, and the
measured 3.16 ns/iteration against a 1.80 ns harness floor is almost entirely
that scaffolding.

So a chain performs `n` operations per iteration with **no array and no `Nat`**
in the loop, and the row divides by `n` through `BenchSpec.workUnits`. At
`n = 1280` the per-iteration floor contributes under two picoseconds per
operation.

## Why not an array

`Subtype` erases to its payload, so `Goldilocks.Fast.Field` is a bare `UInt64`
in compiled code. `Array` does not inherit that: every element is a
`lean_object*`, and `lean_box_uint64` *allocates*. An `Array` of a 64-bit
carrier is a pointer array over separately allocated cells — two dependent
loads and a possible refcount write per element. A dependent `add` chain is
about one cycle per operation and cannot be fed from that.

This is also why the chain lengths here are not Plonky3's. Its
`benchmark_mul_latency` folds over a flat `Vec<F>` of 10000 elements; matching
that *element count* would mismatch the *working set*, which is the quantity
that decides what a memory-touching loop measures. Matching the **shape** —
latency separated from throughput — is what makes the two comparable.

## Why not `for` and `let mut`

`ForIn` threads a single state value, so ten mutable locals become a nested
`Prod`. `Prod` has two computationally relevant fields, so it is not a trivial
structure and does not erase: nine heap allocations per round around ten
multiplies. Every chain below is therefore a tail-recursive function with
scalar parameters, and `Harness/SelfCheck.lean` measures what is left.

## Why the inner block is unrolled

The loop counter is a structurally-recursive `Nat`. That allocates nothing —
small naturals are tagged immediates — but the emitted C still spends a
`lean_nat_sub`, a `lean_dec` and a `lean_nat_dec_eq` on every round, which is
several times a Montgomery multiply. So the counter runs the *blocks* and each
block is a straight-line `unrollBlock` of operations with no counter at all,
putting the loop overhead at one part in `unrollBlock` rather than one part in
one.
-/

public section

namespace CompPolyBench

/-- Operations in one straight-line, counter-free block. -/
def unrollBlock : Nat := 64

/-- Rounds in a chain, and so the `workUnits` of a latency row.

Large enough that the per-iteration harness floor (about 1.8 ns) contributes
under two picoseconds per operation, and small enough that a `ZMod` row — three
orders of magnitude slower than its native counterpart — still fits comfortably
inside one sample. A whole number of `unrollBlock`s, and equal to
`throughputUnits`, so a latency row and a throughput row perform the same number
of operations and their per-unit costs are directly comparable. -/
def chainRounds : Nat := 20 * unrollBlock

/-- Independent accumulators in a throughput chain.

Ten, as Plonky3 uses, so the two measure the same amount of instruction-level
parallelism. Eleven live values including the counter, which fits the register
file on both aarch64 and x86-64 — the same constraint the peer is under. -/
def throughputWidth : Nat := 10

/-- Straight-line rounds inside one throughput loop step. -/
def throughputUnroll : Nat := 4

/-- Rounds in a throughput chain; `throughputWidth` operations each.

A whole number of `throughputUnroll`s, for the same reason `chainRounds` is a
whole number of `unrollBlock`s. -/
def throughputRounds : Nat := 32 * throughputUnroll

/-- Operations a latency chain of `rounds` actually performs.

`chainLatency` runs whole `unrollBlock`s, so a `rounds` that is not a multiple
of one is rounded down. Rows take their `workUnits` from here rather than from
the `rounds` they asked for, so a badly chosen depth measures fewer operations
than its name suggests instead of dividing by a count the machine never
performed. -/
def latencyUnits (rounds : Nat) : Nat := unrollBlock * (rounds / unrollBlock)

/-- Operations a throughput chain of `rounds` actually performs.

`throughputWidth` per round, whole `throughputUnroll`s only; see
`latencyUnits`. -/
def throughputUnitsOf (rounds : Nat) : Nat :=
  throughputWidth * throughputUnroll * (rounds / throughputUnroll)

/-- Work units performed by one throughput iteration at `throughputRounds`.

Equal to `chainRounds` by construction; see the note there. -/
def throughputUnits : Nat := throughputUnitsOf throughputRounds

/-- Apply `op` eight times, straight-line.

Composed with itself to build the `unrollBlock`-deep block the chain loops over,
so the loop counter is paid once per 64 operations instead of once per one. -/
@[inline] def apply8 {F : Type} (op : F → F) (x : F) : F :=
  op (op (op (op (op (op (op (op x)))))))

/-- Apply `op` to `x` in a dependent chain, `rounds` deep.

Every step depends on the previous one, so this measures operation **latency**:
the pipeline cannot overlap two steps. `op` is a direct argument rather than a
`Mul` resolved from a `[Field F]` dictionary — `Goldilocks.Fast.instField` is
declared `(priority := low)` precisely so the concrete instance wins at concrete
sites, and a generic body would pay a projection chain and an indirect call per
step, several times the cost of the operation under test. -/
@[specialize] def chainLatency {F : Type} (op : F → F) (rounds : Nat) (x : F) : F :=
  let rec @[specialize] go (n : Nat) (acc : F) : F :=
    match n with
    | 0 => acc
    | n + 1 => go n (apply8 (apply8 op) acc)
  go (rounds / unrollBlock) x

/-- Apply `op` across ten independent accumulators, `rounds` times.

No accumulator depends on another within a round, so the pipeline can overlap
them and this measures operation **throughput**. Combined at the end with
`join`, so the whole computation stays live and returns a single value.

Ten scalar parameters rather than a tuple or a `for` loop with ten `let mut`
bindings: see the note at the top of this file on `Prod` not erasing. -/
@[specialize] def chainThroughput {F : Type} (op : F → F → F) (join : F → F → F)
    (rounds : Nat) (a b c d e f g h i j : F) : F :=
  let rec @[specialize] go (n : Nat) (a b c d e f g h i j : F) : F :=
    match n with
    | 0 =>
      join (join (join (join a b) (join c d)) (join (join e f) (join g h))) (join i j)
    | n + 1 =>
      let a0 := a; let b0 := b; let c0 := c; let d0 := d; let e0 := e
      let f0 := f; let g0 := g; let h0 := h; let i0 := i; let j0 := j
      let a1 := op a0 b0
      let b1 := op b0 c0
      let c1 := op c0 d0
      let d1 := op d0 e0
      let e1 := op e0 f0
      let f1 := op f0 g0
      let g1 := op g0 h0
      let h1 := op h0 i0
      let i1 := op i0 j0
      let j1 := op j0 a0
      let a2 := op a1 b1
      let b2 := op b1 c1
      let c2 := op c1 d1
      let d2 := op d1 e1
      let e2 := op e1 f1
      let f2 := op f1 g1
      let g2 := op g1 h1
      let h2 := op h1 i1
      let i2 := op i1 j1
      let j2 := op j1 a1
      let a3 := op a2 b2
      let b3 := op b2 c2
      let c3 := op c2 d2
      let d3 := op d2 e2
      let e3 := op e2 f2
      let f3 := op f2 g2
      let g3 := op g2 h2
      let h3 := op h2 i2
      let i3 := op i2 j2
      let j3 := op j2 a2
      let a4 := op a3 b3
      let b4 := op b3 c3
      let c4 := op c3 d3
      let d4 := op d3 e3
      let e4 := op e3 f3
      let f4 := op f3 g3
      let g4 := op g3 h3
      let h4 := op h3 i3
      let i4 := op i3 j3
      let j4 := op j3 a3
      go n a4 b4 c4 d4 e4 f4 g4 h4 i4 j4
  go (rounds / throughputUnroll) a b c d e f g h i j

end CompPolyBench
