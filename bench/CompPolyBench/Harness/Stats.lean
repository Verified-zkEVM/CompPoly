/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

/-!
# Benchmark Sample Statistics

Summary statistics over the per-sample costs collected for one benchmark.

Costs are carried in **picoseconds per iteration** so that dividing a sample's
elapsed nanoseconds by its iteration count does not truncate sub-nanosecond
operations to zero.

Outliers are *labelled*, never dropped: a sample that took ten times the median
is data about the machine, and silently discarding it is how a harness comes to
report a stability it does not have.
-/

public section

namespace CompPolyBench

/-- Summary of the per-sample costs of one benchmark, in picoseconds per iteration. -/
structure SampleStats where
  /-- Number of samples collected. -/
  count : Nat
  /-- Iterations timed within each sample. -/
  itersPerSample : Nat
  /-- Fastest sample. -/
  minPicos : Nat
  /-- Median sample; the headline number. -/
  medianPicos : Nat
  /-- Arithmetic mean of the samples. -/
  meanPicos : Nat
  /-- 95th percentile, by nearest rank. -/
  p95Picos : Nat
  /-- Population standard deviation. -/
  stddevPicos : Nat
  /-- Median absolute deviation from the median. -/
  madPicos : Nat
  /-- Samples beyond 1.5x the interquartile range from the quartiles. -/
  mildOutliers : Nat
  /-- Samples beyond 3x the interquartile range from the quartiles. -/
  severeOutliers : Nat
  /-- Whether too few samples were collected for the spread to mean anything. -/
  unreplicated : Bool
deriving Inhabited

/-- Least number of samples for which dispersion is reported as meaningful. -/
def replicationThreshold : Nat := 5

/-- Sample at a fractional position of a sorted array, by nearest rank. -/
private def quantile (sorted : Array Nat) (numerator denominator : Nat) : Nat :=
  if sorted.isEmpty then 0
  else
    let idx := min (sorted.size - 1) (sorted.size * numerator / denominator)
    sorted.getD idx 0

/-- Median of a sorted array; the mean of the middle pair when the size is even. -/
private def medianOfSorted (sorted : Array Nat) : Nat :=
  let n := sorted.size
  if n = 0 then 0
  else if n % 2 = 1 then sorted.getD (n / 2) 0
  else (sorted.getD (n / 2 - 1) 0 + sorted.getD (n / 2) 0) / 2

/-- Integer square root, by Newton iteration. -/
private def natSqrt (n : Nat) : Nat :=
  if n < 2 then n
  else
    let rec step (guess fuel : Nat) : Nat :=
      match fuel with
      | 0 => guess
      | fuel + 1 =>
        let next := (guess + n / guess) / 2
        if next ≥ guess then guess else step next fuel
    step n (n.log2 + 2)

/-- Summarise per-iteration sample costs, in picoseconds. -/
def summarise (itersPerSample : Nat) (picosPerIteration : Array Nat) : SampleStats :=
  let sorted := picosPerIteration.qsort (· < ·)
  let n := sorted.size
  if n = 0 then
    { count := 0, itersPerSample := itersPerSample, minPicos := 0, medianPicos := 0,
      meanPicos := 0, p95Picos := 0, stddevPicos := 0, madPicos := 0,
      mildOutliers := 0, severeOutliers := 0, unreplicated := true }
  else
    let total := sorted.foldl (· + ·) 0
    let mean := total / n
    let median := medianOfSorted sorted
    let variance := sorted.foldl (init := 0) fun acc x ↦
      let d := if x ≥ mean then x - mean else mean - x
      acc + d * d
    let absDeviations := (sorted.map fun x ↦ if x ≥ median then x - median else median - x)
    let q1 := quantile sorted 1 4
    let q3 := quantile sorted 3 4
    let iqr := q3 - q1
    -- A zero interquartile range collapses both fences onto the quartiles, which
    -- would label every sample that differs at all as a severe outlier. Samples
    -- that agree to the picosecond are the opposite of an outlier signal.
    let label := iqr ≠ 0
    let mildLow := q1 - min q1 (3 * iqr / 2)
    let mildHigh := q3 + 3 * iqr / 2
    let severeLow := q1 - min q1 (3 * iqr)
    let severeHigh := q3 + 3 * iqr
    { count := n
      itersPerSample := itersPerSample
      minPicos := sorted.getD 0 0
      medianPicos := median
      meanPicos := mean
      p95Picos := quantile sorted 95 100
      stddevPicos := natSqrt (variance / n)
      madPicos := medianOfSorted (absDeviations.qsort (· < ·))
      mildOutliers := if !label then 0 else sorted.foldl (init := 0) fun acc x ↦
        if x < mildLow || x > mildHigh then acc + 1 else acc
      severeOutliers := if !label then 0 else sorted.foldl (init := 0) fun acc x ↦
        if x < severeLow || x > severeHigh then acc + 1 else acc
      unreplicated := n < replicationThreshold }

end CompPolyBench
