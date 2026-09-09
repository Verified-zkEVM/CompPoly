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

The suite's per-benchmark iteration counts are treated as a total-work budget:
rather than timing all of them in one region and dividing, the budget is split
into `targetSampleCount` samples so the spread between them is visible. A
benchmark whose single iteration already exhausts the budget cannot be split and
is reported as unreplicated rather than as a number with an implied precision it
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

/-- Samples aimed for when the iteration budget allows it. -/
def targetSampleCount : Nat := 20

/-- Divide a total iteration budget into samples.

Where the budget allows at least `targetSampleCount` iterations the budget is
split evenly. Below that each iteration becomes its own sample, which keeps as
much replication as the budget can pay for. -/
def planSamples (totalIterations : Nat) : SamplingPlan :=
  if totalIterations = 0 then
    { itersPerSample := 0, sampleCount := 0 }
  else if totalIterations ≤ targetSampleCount then
    { itersPerSample := 1, sampleCount := totalIterations }
  else
    { itersPerSample := totalIterations / targetSampleCount, sampleCount := targetSampleCount }

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

/-- Warm a benchmark body, then collect `plan.sampleCount` timed samples of it.

`warmup` is the number of *residual* warmup iterations to run; the caller is
expected to have already discounted any pass that executed the body beforehand.
Every sample replays the same iteration indices, so samples differ only in
machine state and not in the work performed. -/
@[specialize] def collectSamples (warmup : Nat) (plan : SamplingPlan)
    (body : Nat → UInt64 → UInt64) : IO SampledRun := do
  let mut acc ← warmIterations warmup 0 body
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
