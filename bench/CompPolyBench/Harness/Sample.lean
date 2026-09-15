/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Harness.Stats
public import CompPolyBench.Harness.Timer

/-!
# Benchmark Sampling

Collecting a benchmark's cost as a *set* of samples rather than one total.

A row's cost is measured as several timed samples so the spread between them is
visible; `Harness.Budget` decides how many and how long each one is. A benchmark
whose single iteration already exhausts the budget cannot be split and is
reported as unreplicated rather than as a number with an implied precision it
does not have.
-/

public section

namespace CompPolyBench

/-- How a total iteration budget is divided into timed samples. -/
structure SamplingPlan where
  /-- Iterations timed inside each sample. -/
  itersPerSample : Nat
  /-- Number of samples to collect. -/
  sampleCount : Nat
deriving Inhabited

/-- Elapsed nanoseconds of one sample converted to picoseconds per iteration. -/
@[inline] def picosPerIteration (nanos iters : Nat) : Nat :=
  if iters = 0 then 0 else nanos * 1000 / iters

/-- Result of sampling one benchmark. -/
structure SampledRun where
  /-- Summary statistics over the samples. -/
  stats : SampleStats
  /-- Per-sample cost in picoseconds per iteration, in collection order. -/
  samples : Array Nat
  /-- Total nanoseconds spent inside timed regions. -/
  totalNanos : Nat
  /-- Total iterations timed. -/
  totalIterations : Nat
  /-- Final sink accumulator, carried out so the loops cannot be eliminated. -/
  sink : UInt64
deriving Inhabited

/-- Collect `plan.sampleCount` timed samples of a benchmark body.

`init` seeds the sink accumulator, and must be the one carried out of whatever
warmed the body — the calibration ramp in practice. Threading it is what keeps
that earlier loop from being eliminable. Every sample replays the same iteration
indices, so samples differ only in machine state and not in the work performed. -/
@[specialize] def collectSamples (init : UInt64) (plan : SamplingPlan)
    (body : Nat → UInt64 → UInt64) : IO SampledRun := do
  let mut acc := init
  let mut samples : Array Nat := Array.emptyWithCapacity plan.sampleCount
  let mut totalNanos := 0
  for _ in [0:plan.sampleCount] do
    let sample ← timeIterations plan.itersPerSample acc body
    acc := sample.sink
    samples := samples.push (picosPerIteration sample.nanos plan.itersPerSample)
    totalNanos := totalNanos + sample.nanos
  pure {
    stats := summarise plan.itersPerSample samples
    samples := samples
    totalNanos := totalNanos
    totalIterations := plan.itersPerSample * plan.sampleCount
    sink := acc }

end CompPolyBench
