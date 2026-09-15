/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Harness.Sample

/-!
# Benchmark Measurement Budgets

Sizing a benchmark from a wall-clock budget instead of a written-down iteration
count.

The suite used to carry one hand-tuned iteration count per benchmark per preset.
A count is the wrong unit: it is not comparable between two rows of the same
table, it goes stale as the code it measures gets faster, and choosing one for a
new benchmark is guesswork that has to be redone on every machine. A budget is
comparable, and the harness can work the count out for itself.

The scheme is the one `BENCHMARKING.md` §6.3 describes:

1. a geometric ramp times 1, 2, 4, … iterations until `warmupNanos` of work has
   accumulated, and doubles as the benchmark's warmup;
2. the per-iteration cost estimate from that ramp sizes one sample to
   `sampleNanos`;
3. `sampleCount` samples are collected, subject to a total `measureNanos`.

Two properties are deliberate. The cost estimate comes from the ramp's **last
step alone** rather than its accumulated total, because the early steps run cold
and would bias the estimate high, which would size samples short and inflate the
dispersion the suite exists to report. And `sampleCount` is fixed once the plan
is chosen: no sample is skipped because the clock has run on. Re-checking
elapsed time between samples would make the count depend on how busy the machine
happened to be, which is a worse trade than the seconds it would save.
-/

public section

namespace CompPolyBench

/-- Wall-clock budgets for one benchmark row.

Replaces the per-benchmark iteration counts. Every field is nanoseconds except
`sampleCount`. -/
structure BenchBudget where
  /-- Work to accumulate in the calibration ramp before measuring. The ramp is
  also the benchmark's warmup, so this is the warmup budget. -/
  warmupNanos : Nat
  /-- How long one timed sample should take.

  Deliberately the same at every preset. A sample is a mean over
  `itersPerSample` iterations, so raising that count averages dispersion away; if
  this varied by preset then `--small` and `--large` would report structurally
  different spread for identical code and the reported spread would stop being
  comparable between them. It is a clock-resolution knob, not a quality knob:
  the two clock reads bounding a sample cost tens of nanoseconds, which is
  negligible against any value here. -/
  sampleNanos : Nat
  /-- Samples to collect when `measureNanos` allows it. The one honest quality
  axis, so this is what a preset mainly varies. -/
  sampleCount : Nat
  /-- Total time one row may spend inside timed regions.

  A second ceiling, and a necessary one: `sampleNanos * sampleCount` is a small
  fraction of a second, so without a separate total the workloads costing
  seconds per iteration could never be replicated at all. A target rather than a
  guarantee — the first iteration always runs to completion. -/
  measureNanos : Nat
deriving Inhabited

/-- Outcome of the calibration ramp. -/
structure Calibration where
  /-- Per-iteration cost in picoseconds, taken from the ramp's last step only. -/
  picosPerIteration : Nat
  /-- Iterations the ramp executed. These are the row's warmup. -/
  iterations : Nat
  /-- Nanoseconds the ramp spent. -/
  nanos : Nat
  /-- Sink accumulator carried out of the ramp, to be threaded into the timed
  samples so neither loop can be eliminated. -/
  sink : UInt64
deriving Inhabited

/-- Doublings the calibration ramp may perform.

Structural rather than a tuning knob: the wall-clock stop condition fires first
for any body costing more than a fraction of a nanosecond, so this exists only to
bound the loop. `2 ^ 40` iterations of even a one-nanosecond body is over a
minute, so the limit is never the binding constraint. -/
def calibrationRampLimit : Nat := 40

/-- Time a benchmark body over a geometric ramp, and estimate its per-iteration
cost.

Returns the estimate from the final ramp step, the iterations executed, and the
sink accumulator. The accumulator must be threaded into the timed samples: a ramp
whose result is discarded is eliminable, which is how warmup came to be a no-op
before. -/
@[specialize] def calibrate (warmupNanos : Nat) (body : Nat → UInt64 → UInt64) :
    IO Calibration := do
  let mut acc : UInt64 := 0
  let mut iters := 1
  let mut executed := 0
  let mut elapsed := 0
  let mut lastNanos := 0
  let mut lastIters := 0
  for _ in [0:calibrationRampLimit] do
    if elapsed ≥ warmupNanos then
      break
    let sample ← timeIterations iters acc body
    acc := sample.sink
    executed := executed + iters
    elapsed := elapsed + sample.nanos
    lastNanos := sample.nanos
    lastIters := iters
    iters := iters * 2
  pure {
    picosPerIteration := picosPerIteration lastNanos lastIters
    iterations := executed
    nanos := elapsed
    sink := acc }

/-- Size a benchmark's samples from a calibrated per-iteration cost.

`itersPerSample` is chosen so one sample takes about `budget.sampleNanos`, and
`sampleCount` is capped by what `budget.measureNanos` can pay for. Both are at
least one, so a workload whose single iteration exhausts the whole budget still
produces exactly one sample — which `Stats.summarise` then marks unreplicated
rather than reporting as a number with an implied precision it does not have. -/
def planFromCalibration (budget : BenchBudget) (picosPerIteration : Nat) :
    SamplingPlan :=
  let cost := max 1 picosPerIteration
  let itersPerSample := max 1 (budget.sampleNanos * 1000 / cost)
  let samplePicos := max 1 (itersPerSample * cost)
  let affordable := budget.measureNanos * 1000 / samplePicos
  { itersPerSample := itersPerSample
    sampleCount := max 1 (min budget.sampleCount affordable) }

/-! ## The three preset budgets

`sampleNanos` is 1 ms at every preset, for the reason recorded on the field.
What a preset varies is how many samples it asks for and how long a single row
may spend in total.
-/

/-- Budget for `--large`: 200 ms of warmup, 50 samples, one minute per row. -/
def largeBudget : BenchBudget :=
  { warmupNanos := 200000000, sampleNanos := 1000000, sampleCount := 50,
    measureNanos := 60000000000 }

/-- Budget for `--medium`, the default and what CI runs: 50 ms of warmup, 20
samples, two seconds per row. -/
def mediumBudget : BenchBudget :=
  { warmupNanos := 50000000, sampleNanos := 1000000, sampleCount := 20,
    measureNanos := 2000000000 }

/-- Budget for `--small`: 20 ms of warmup, 10 samples, 0.2 s per row. -/
def smallBudget : BenchBudget :=
  { warmupNanos := 20000000, sampleNanos := 1000000, sampleCount := 10,
    measureNanos := 200000000 }

/-! ## Sizing checks

Sample sizing at the three interesting scales, plus the degenerate ones.
`SamplingPlan` carries no `DecidableEq`, so these check the fields rather than
the structure. They run at elaboration time, so a wrong one fails `lake build`.
-/

section Guards

-- A 1.5 ns body: a sample is two thirds of a million iterations, and every
-- sample the count asks for is affordable.
#guard (planFromCalibration largeBudget 1500).itersPerSample == 666666
#guard (planFromCalibration largeBudget 1500).sampleCount == 50

-- A body that already costs one sample's worth of time: one iteration per
-- sample, still fully replicated.
#guard (planFromCalibration largeBudget 1000000000).itersPerSample == 1
#guard (planFromCalibration largeBudget 1000000000).sampleCount == 50

-- A 13 s body cannot be split, so the total budget decides how many samples
-- there are: four at `--large`, and one at `--medium`, where it is reported as
-- unreplicated rather than averaged.
#guard (planFromCalibration largeBudget 13000000000000).itersPerSample == 1
#guard (planFromCalibration largeBudget 13000000000000).sampleCount == 4
#guard (planFromCalibration mediumBudget 13000000000000).sampleCount == 1

-- A cost estimate of zero -- a body too cheap for the clock to resolve, or a
-- ramp that never ran -- must not divide by zero and must still sample.
#guard (planFromCalibration smallBudget 0).itersPerSample == 1000000000
#guard (planFromCalibration smallBudget 0).sampleCount == 10

end Guards

end CompPolyBench
