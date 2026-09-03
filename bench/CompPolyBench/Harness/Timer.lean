/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Harness.Sink

/-!
# Benchmark Timing Core

The single place in the harness that reads the clock.

A benchmark body has type `Nat → UInt64 → UInt64`: it takes the iteration index
and the sink accumulator and returns the updated accumulator. Threading the
accumulator through the body is what keeps the benchmark result live, so a body
whose result is discarded cannot be written by accident.
-/

public section

namespace CompPolyBench

/-- Elapsed time for one timed sample, with the sink accumulator it produced. -/
structure TimedSample where
  /-- Nanoseconds spent inside the timed region. -/
  nanos : Nat
  /-- Final sink accumulator, carried out so the loop cannot be eliminated. -/
  sink : UInt64
deriving Inhabited

/-- Run a benchmark body `iters` times without timing it, returning the sink
accumulator so the loop has an observable result.

The accumulator must be fed into the subsequent timed run; discarding it would
leave the warmup loop eliminable, which is how warmup came to be a no-op before. -/
@[inline] def warmIterations (iters : Nat) (init : UInt64)
    (body : Nat → UInt64 → UInt64) : IO UInt64 := do
  let mut acc := init
  for i in [0:iters] do
    acc := body i acc
  pure acc

/-- Run a benchmark body `iters` times and return the elapsed nanoseconds.

`init` seeds the sink accumulator, normally from `warmIterations`. The
accumulator is bound and returned before the closing clock read, so the loop is
sequenced inside the timed region. -/
@[inline] def timeIterations (iters : Nat) (init : UInt64)
    (body : Nat → UInt64 → UInt64) : IO TimedSample := do
  let mut acc := init
  let start ← IO.monoNanosNow
  for i in [0:iters] do
    acc := body i acc
  let forced := acc
  let stop ← IO.monoNanosNow
  pure { nanos := stop - start, sink := forced }

/-- Warm a benchmark body and then time it, in one step. -/
@[inline] def warmThenTime (warmup measured : Nat)
    (body : Nat → UInt64 → UInt64) : IO TimedSample := do
  let warmed ← warmIterations warmup 0 body
  timeIterations measured warmed body

end CompPolyBench
