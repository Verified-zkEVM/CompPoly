/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Common
public import CompPolyBench.Harness.Chain

/-!
# Harness Self-Check

Two synthetic benchmarks that measure the harness itself.

`harness-floor` times an empty body, giving the per-iteration cost of the loop
and the sink. Every other benchmark's reported cost sits on top of this floor.

`harness-canary` times a body with a known, deliberately non-eliminable cost. If
it ever measures close to the floor, benchmark bodies are being optimised away and
the run fails rather than reporting an impressive number.

`harness-chain-floor` and `harness-chain-linearity` do the same two jobs for the
chained bodies in `Harness/Chain.lean`, which have their own floor (the chain's
loop, not the harness's) and their own way of going wrong (a chain the compiler
collapses still reports a plausible number).
-/

public section

namespace CompPolyBench

/-- Group metadata for the harness self-check. -/
def harnessGroupInfos : List BenchGroupInfo := [
  ⟨"harness-floor", "Harness loop and sink floor"⟩,
  ⟨"harness-canary", "Harness dead-code canary"⟩,
  ⟨"harness-chain-floor", "Chain loop floor, per operation"⟩,
  ⟨"harness-chain-linearity", "Chain linearity check"⟩
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

/-- Least multiple by which the canary's per-iteration cost must exceed the floor's.

The check is a ratio rather than an absolute duration so it is machine
independent: an eliminated canary body collapses onto the floor whatever the
hardware.

It compares **per-iteration medians**, not totals. Totals only separate the two
rows while they run the same number of iterations; once iteration counts come
from a wall-clock budget the totals are equalised by construction, and a check
on them would either throw on every run or, lowered to accommodate that, pass
vacuously forever — leaving the harness with no dead-code detection at all. -/
def canaryFloorRatio : Nat := 3

/-- Digest length for the self-check benchmarks.

Both bodies are unbounded in the iteration index, so they have no period. Their
digests are not correctness oracles — nothing is cross-checked against them — so
the length only has to be fixed. -/
private def harnessDigestIterations : Nat := 16

/-- Shift distance in the chain floor's mixing step. -/
private def chainFloorShift : UInt64 := 7

/-- The cheapest operation a chain can honestly carry.

A shift and a wrapping add: two ALU operations, each depending on the last, so a
chain of them runs at the machine's dependent-issue rate. The per-unit number
the row reports is the chain machinery *plus* this pair, so it is an upper bound
on the machinery alone; when it lands at the pair's own dependent latency, the
machinery costs nothing measurable.

**It must mix two algebras.** The obvious candidate, `x ^^^ (x >>> 7)`, is the
`GF(2)`-linear map `I + S`; in characteristic two `(I + S) ^ 64 = I + S ^ 64`,
and `S ^ 64` shifts right by 448, so **a 64-deep block of it is the identity**.
LLVM finds this, and the row then reports 15 ps per operation — a sixteenth of a
cycle — while still passing the linearity check below, because what collapses is
each block rather than the loop over blocks. Addition carries between bits and
so does not commute with the shift that way, and there is no reassociation rule
that merges the two. -/
@[inline] private def chainFloorStep (x : UInt64) : UInt64 :=
  x + (x >>> chainFloorShift)

/-- `chainFloorStep` as a binary operation, for the throughput chain.

The same two ALU operations, so the throughput floor and the latency floor
differ only in whether consecutive operations depend on each other. -/
@[inline] private def chainFloorPair (x y : UInt64) : UInt64 :=
  x + (y >>> chainFloorShift)

/-- Least ratio by which an eight-times-longer chain must outcost a short one.

One-sided and slack, deliberately. A chain that is executed reports a ratio near
eight; a chain the compiler has collapsed reports one. Demanding the exact
factor instead would fail on correct builds, because eight times the rounds is
not eight times the cache behaviour and the sample count moves with the cost. -/
def chainLinearityRatio : Nat := 4

/-- Chain length multiplier used by the linearity check. -/
def chainLinearityFactor : Nat := 8

/-- Time the harness and chain floors, and reject a body that has been folded away. -/
private def runHarnessSelfCheck (preset : BenchPreset) (selection : BenchSelection)
    (gen : StdGen) : IO (Array BenchGroup × StdGen) := do
  let floorRecord ← runTimedSpec
    { name := "harness-floor", representation := "UInt64", method := "empty body", field := "none",
      inputShape := "no input", digestIterations := harnessDigestIterations,
      forceTiming := true }
    preset (fun i ↦ i.toUInt64) (fun x ↦ x.toNat) (sink := u64Sink)
  let canaryRecord ← runTimedSpec
    { name := "harness-canary", representation := "UInt64",
      method := s!"{canaryRounds} mixing rounds", field := "none", inputShape := "no input",
      digestIterations := harnessDigestIterations, forceTiming := true }
    preset (fun i ↦ canaryWork i.toUInt64) (fun x ↦ x.toNat) (sink := u64Sink)
  let floorPicos := floorRecord.stats.medianPicos
  let canaryPicos := canaryRecord.stats.medianPicos
  if floorPicos == 0 || canaryPicos == 0 then
    throw <| IO.userError <|
      s!"harness self-check produced a zero per-iteration median (floor {floorPicos}ps, " ++
      s!"canary {canaryPicos}ps): the clock could not resolve the loop, so the canary " ++
      "check below cannot say anything and no timing in this run is trustworthy."
  if canaryPicos < canaryFloorRatio * floorPicos then
    throw <| IO.userError <|
      s!"harness canary collapsed onto the loop floor: canary {canaryPicos}ps per " ++
      s!"iteration vs floor {floorPicos}ps (expected at least {canaryFloorRatio}x). " ++
      "Benchmark bodies are being optimised away, so every measured time in this " ++
      "run is meaningless."
  -- Chain scaffolding, and proof that a chain is executed rather than folded.
  -- `chainRounds` is a compile-time constant but `mixer` is not, so the chain
  -- body depends on a runtime local and cannot be lifted to a one-time thunk.
  let (seeds, gen) := (randomNatArray throughputWidth (2 ^ 32 - 1)).run gen
  let seedAt (k : Nat) : UInt64 := UInt64.ofNat (seeds.getD k k + 1)
  let mixer : UInt64 := seedAt 0
  let chainBody (rounds : Nat) : Nat → UInt64 :=
    fun _ ↦ chainLatency chainFloorStep rounds mixer
  let throughputBody : Nat → UInt64 :=
    fun _ ↦ chainThroughput chainFloorPair (· + ·) throughputRounds
      (seedAt 0) (seedAt 1) (seedAt 2) (seedAt 3) (seedAt 4)
      (seedAt 5) (seedAt 6) (seedAt 7) (seedAt 8) (seedAt 9)
  let chainFloorRecord ← runTimedSpec
    { name := "harness-chain-floor", representation := "UInt64",
      method := s!"{chainRounds}x shift-add, dependent", field := "none",
      inputShape := "no input", digestIterations := 1, workUnits := chainRounds,
      digestClass := "latency", forceTiming := true }
    preset (chainBody chainRounds) (fun x ↦ x.toNat) (sink := u64Sink)
  let throughputFloorRecord ← runTimedSpec
    { name := "harness-chain-floor", representation := "UInt64",
      method := s!"{throughputUnits}x shift-add, {throughputWidth}-wide",
      field := "none", inputShape := "no input", digestIterations := 1,
      workUnits := throughputUnits, digestClass := "throughput",
      forceTiming := true }
    preset throughputBody (fun x ↦ x.toNat) (sink := u64Sink)
  -- Both linearity rows keep `workUnits = 1`. The check compares totals, and the
  -- two rows deliberately do different amounts of work, which a shared per-unit
  -- count could not describe.
  let shortRecord ← runTimedSpec
    { name := "harness-chain-linearity-short", representation := "UInt64",
      method := s!"{chainRounds} rounds", field := "none", inputShape := "no input",
      digestIterations := 1, digestClass := "short", forceTiming := true }
    preset (chainBody chainRounds) (fun x ↦ x.toNat) (sink := u64Sink)
  let longRecord ← runTimedSpec
    { name := "harness-chain-linearity-long", representation := "UInt64",
      method := s!"{chainLinearityFactor * chainRounds} rounds", field := "none",
      inputShape := "no input", digestIterations := 1, digestClass := "long",
      forceTiming := true }
    preset (chainBody (chainLinearityFactor * chainRounds)) (fun x ↦ x.toNat)
      (sink := u64Sink)
  let shortPicos := shortRecord.stats.medianPicos
  let longPicos := longRecord.stats.medianPicos
  if longPicos < chainLinearityRatio * shortPicos then
    throw <| IO.userError <|
      s!"chained benchmark bodies are not being executed: {chainLinearityFactor}x the " ++
      s!"rounds cost {longPicos}ps against {shortPicos}ps, a ratio under " ++
      s!"{chainLinearityRatio}x. Every per-unit number in this run divides by a " ++
      "work count the machine did not perform."
  let mut groups := #[]
  if selection.selects "harness-floor" then
    groups := groups.push
      { groupKey := "harness-floor", title := "Harness loop and sink floor",
        records := #[floorRecord] }
  if selection.selects "harness-canary" then
    groups := groups.push
      { groupKey := "harness-canary", title := "Harness dead-code canary",
        records := #[canaryRecord] }
  if selection.selects "harness-chain-floor" then
    groups := groups.push
      { groupKey := "harness-chain-floor", title := "Chain loop floor, per operation",
        records := #[chainFloorRecord, throughputFloorRecord] }
  if selection.selects "harness-chain-linearity" then
    groups := groups.push
      { groupKey := "harness-chain-linearity", title := "Chain linearity check",
        records := #[shortRecord, longRecord] }
  pure (groups, gen)

/-- Registry entry for the harness self-check.

Both benchmarks are measured whenever either is selected, because the canary
check is a comparison between them. -/
def harnessTasks : List BenchTask := [
  { infos := harnessGroupInfos, runTask := runHarnessSelfCheck }
]

end CompPolyBench
