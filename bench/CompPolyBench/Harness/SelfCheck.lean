/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Common

/-!
# Harness Self-Check

Two synthetic benchmarks that measure the harness itself.

`harness-floor` times an empty body, giving the per-iteration cost of the loop
and the sink. Every other benchmark's reported cost sits on top of this floor.

`harness-canary` times a body with a known, deliberately non-eliminable cost. If
it ever measures close to the floor, benchmark bodies are being optimised away and
the run fails rather than reporting an impressive number.
-/

public section

namespace CompPolyBench

/-- Group metadata for the harness self-check. -/
def harnessGroupInfos : List BenchGroupInfo := [
  ⟨"harness-floor", "Harness loop and sink floor"⟩,
  ⟨"harness-canary", "Harness dead-code canary"⟩
]

/-- Rounds of mixing performed by one canary iteration. -/
def canaryRounds : Nat := 256

/-- One round of the canary's mixing chain. -/
@[inline] private def canaryRound (x : UInt64) : UInt64 :=
  let y := (x ^^^ (x >>> 33)) * 0xFF51AFD7ED558CCD
  y ^^^ (y >>> 29)

/-- Deliberately non-eliminable work, `canaryRounds` rounds deep.

`@[noinline]` and the dependence on the iteration index keep this from being
constant-folded. -/
@[noinline] private def canaryWork (x : UInt64) : UInt64 :=
  let rec go (n : Nat) (acc : UInt64) : UInt64 :=
    match n with
    | 0 => acc
    | n + 1 => go n (canaryRound acc)
  go canaryRounds x

/-- Least multiple by which the canary must exceed the floor.

The check is a ratio rather than an absolute duration so it is machine
independent: an eliminated canary body collapses onto the floor whatever the
hardware. -/
def canaryFloorRatio : Nat := 3

/-- Measured iterations for the self-check benchmarks. -/
private def harnessMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 2000000 500000 100000

/-- Time the harness floor and the canary, and reject a collapsed canary. -/
private def runHarnessSelfCheck (preset : BenchPreset) (selection : BenchSelection)
    (gen : StdGen) : IO (Array BenchGroup × StdGen) := do
  let measured := harnessMeasuredIterations preset
  let warmup := measured / 10
  let floorRecord ← runTimed "harness-floor" "UInt64" "empty body"
    "none" "no input" preset warmup measured
    (fun i ↦ i.toUInt64) (fun x ↦ x.toNat) (sink := u64Sink) (forceTiming := true)
  let canaryRecord ← runTimed "harness-canary" "UInt64" s!"{canaryRounds} mixing rounds"
    "none" "no input" preset warmup measured
    (fun i ↦ canaryWork i.toUInt64) (fun x ↦ x.toNat) (sink := u64Sink)
    (forceTiming := true)
  if canaryRecord.totalNanos < canaryFloorRatio * floorRecord.totalNanos then
    throw <| IO.userError <|
      s!"harness canary collapsed onto the loop floor: canary {canaryRecord.totalNanos}ns " ++
      s!"vs floor {floorRecord.totalNanos}ns over {measured} iterations " ++
      s!"(expected at least {canaryFloorRatio}x). Benchmark bodies are being " ++
      "optimised away, so every measured time in this run is meaningless."
  let mut groups := #[]
  if selection.selects "harness-floor" then
    groups := groups.push
      { groupKey := "harness-floor", title := "Harness loop and sink floor",
        records := #[floorRecord] }
  if selection.selects "harness-canary" then
    groups := groups.push
      { groupKey := "harness-canary", title := "Harness dead-code canary",
        records := #[canaryRecord] }
  pure (groups, gen)

/-- Registry entry for the harness self-check.

Both benchmarks are measured whenever either is selected, because the canary
check is a comparison between them. -/
def harnessTasks : List BenchTask := [
  { infos := harnessGroupInfos, runTask := runHarnessSelfCheck }
]

end CompPolyBench
