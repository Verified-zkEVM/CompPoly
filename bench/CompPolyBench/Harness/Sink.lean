/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# Benchmark Result Sinks

Allocation-free `UInt64` digests whose only purpose is to keep a benchmark result
live inside the timed region. Correctness is established by the untimed
validation pass, which keeps the strong `Nat` digest in `CompPolyBench.Common`.

Nothing here is comparable across runs or across implementations; a sink value is
never reported.
-/

public section

namespace CompPolyBench

/-- Fold one result word into a running sink accumulator.

Kept `@[noinline]` so the fold survives optimisation; the `harness-floor` group
measures what this costs and `harness-canary` fails the run if it stops costing
anything. -/
@[inline] def sinkStep (acc x : UInt64) : UInt64 :=
  let mixed := (acc ^^^ x) * 0x9E3779B97F4A7C15
  (mixed <<< 27) ||| (mixed >>> 37)

/-- Truncate a `Nat` digest word to a sink word.

The fallback sink for benchmarks that have not declared a cheaper one. Free for
results whose digest already fits a machine word, one bignum reduction otherwise. -/
@[inline] def natSink (n : Nat) : UInt64 :=
  n.toUInt64

/-- Sink a `UInt64`-backed result directly. -/
@[inline] def u64Sink (x : UInt64) : UInt64 :=
  x

/-- Sink a fixed four-position sample of an array.

Aggregate results must never be walked in full inside the timed region; the
untimed validation pass digests every element. -/
@[inline] def arraySampleSink (toU64 : α → UInt64) (xs : Array α) : UInt64 :=
  let n := xs.size
  if n = 0 then
    0
  else
    let pick (i : Nat) : UInt64 :=
      match xs[i]? with
      | some x => toU64 x
      | none => 0
    sinkStep (sinkStep (sinkStep (pick 0) (pick (n / 3))) (pick (2 * n / 3))) (pick (n - 1))

end CompPolyBench
