/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Compare.Read

/-!
# A/B Verdicts

Judges a candidate build against a baseline build from the results files each
wrote, one file per invocation. The unit of evidence is the **invocation-level
median**: samples within one process are not independent of each other, so the
`K` medians from `K` separate processes are what the comparison reasons about.

A row is `faster` only when two things hold at once: the ratio of medians clears
a practical-importance threshold, *and* every candidate invocation beat every
baseline invocation. Strict separation of two groups of five happens by chance
one time in `C(10, 5) = 252`; the threshold keeps a real but negligible change
from being reported as a win. `slower` is the mirror image, and everything else
is `same`.

Two checks come for free from the harness. Inputs are seeded per group, so the
strong digest of a row is the same across binaries and commits; a candidate whose
digest differs from the baseline computed something else, and the row is a
`mismatch` rather than a measurement. And a candidate that is implausibly fast
with an unchanged digest is flagged `suspect`, the signature of a body the
compiler folded away (`BENCHMARKING.md` §12.6 and §12.7).
-/

public section

namespace CompPolyBench

/-- Identity of a row across files.

`name` alone is not unique: a chained group emits a latency and a throughput row
under one name, differing in `digestClass` and `method`, and single-row groups
reuse names across groups. -/
structure RowKey where
  groupKey : String
  name : String
  digestClass : String
  method : String
deriving BEq, Repr, Hashable, Inhabited

/-- The identity of a parsed row. -/
def CompareRow.key (row : CompareRow) : RowKey :=
  { groupKey := row.groupKey, name := row.name, digestClass := row.digestClass,
    method := row.method }

/-- Which build a file or a row came from. -/
inductive Side where
  | baseline
  | candidate
deriving BEq, Repr

/-- Display name of a side. -/
def Side.label : Side → String
  | Side.baseline => "baseline"
  | Side.candidate => "candidate"

/-- The `K` invocation-level medians of one row on one side, with their summary. -/
structure SideSummary where
  /-- Per-invocation `median_picos`, sorted ascending. -/
  medians : Array Nat
  /-- Median of `medians`. -/
  median : Nat
  /-- Smallest invocation median. -/
  lo : Nat
  /-- Largest invocation median. -/
  hi : Nat
  /-- Dispersion of the invocation medians as tenths of a percent of their median. -/
  spreadTenths : Nat
  /-- Some invocation collected fewer than `replicationThreshold` samples. -/
  anyUnreplicated : Bool
  /-- Some invocation labelled severe outliers. -/
  anySevere : Bool
  checksum : Nat
  checksumIterations : Nat
  workUnits : Nat
deriving Repr, Inhabited

/-- Summarise one side of one row from its per-invocation rows. -/
def summariseSide (rows : Array CompareRow) : SideSummary :=
  let meds := (rows.map (·.medianPicos)).qsort (· < ·)
  let median := medianOfSorted meds
  let absDev := (meds.map fun x ↦ if x ≥ median then x - median else median - x).qsort (· < ·)
  let first := rows.getD 0 default
  { medians := meds
    median
    lo := meds.getD 0 0
    hi := meds.getD (meds.size - 1) 0
    spreadTenths := if median = 0 then 0 else 1000 * medianOfSorted absDev / median
    anyUnreplicated := rows.any (·.unreplicated)
    anySevere := rows.any (·.severeOutliers > 0)
    checksum := first.checksum
    checksumIterations := first.checksumIterations
    workUnits := first.workUnits }

/-- Outcome for one row. -/
inductive Verdict where
  | faster
  | slower
  | same
  /-- The two sides disagree on the digest or on the problem size. -/
  | mismatch (reason : String)
  /-- The row is absent from at least one file of the named side. -/
  | missing (side : Side)
  /-- Both sides are present but no ratio can be formed. -/
  | unjudged (reason : String)
deriving BEq, Repr

/-- Whether a verdict means the comparison failed rather than concluded. -/
def Verdict.fatal : Verdict → Bool
  | Verdict.mismatch _ => true
  | Verdict.missing _ => true
  | _ => false

/-- Display form of a verdict. -/
def Verdict.label : Verdict → String
  | Verdict.faster => "faster"
  | Verdict.slower => "slower"
  | Verdict.same => "same"
  | Verdict.mismatch reason => s!"mismatch ({reason})"
  | Verdict.missing side => s!"missing ({side.label})"
  | Verdict.unjudged reason => s!"unjudged ({reason})"

/-- Judge a row from its two side summaries; `thresholdPercent` is in `1..99`.

Exact `Nat` arithmetic throughout: the threshold tests cross-multiply rather than
divide, so no rounding enters the decision. -/
def judge (thresholdPercent : Nat) (b c : SideSummary) : Verdict :=
  let medB := b.median
  let medC := c.median
  if medB == 0 || medC == 0 then
    Verdict.unjudged "zero median"
  else
    let fasterByT := medC * 100 ≤ medB * (100 - thresholdPercent)
    let slowerByT := medC * 100 ≥ medB * (100 + thresholdPercent)
    if fasterByT && c.hi < b.lo then Verdict.faster
    else if slowerByT && c.lo > b.hi then Verdict.slower
    else Verdict.same

/-- Candidate over baseline, in thousandths, rounded; `none` when the baseline is zero. -/
def ratioMilli (b c : SideSummary) : Option Nat :=
  if b.median = 0 then none else some ((c.median * 1000 + b.median / 2) / b.median)

/-- One row of the comparison. -/
structure RowComparison where
  key : RowKey
  workUnits : Nat
  baseline : Option SideSummary
  candidate : Option SideSummary
  ratioMilli : Option Nat
  verdict : Verdict
  /-- Dead-body alarm, when the candidate is faster than is plausible. -/
  suspect : Option String
deriving Repr

/-- What the compare command was asked to do. -/
structure CompareOptions where
  baselines : List System.FilePath
  candidates : List System.FilePath
  thresholdPercent : Nat := 5
  outDir : Option System.FilePath := none

/-- Candidate-over-baseline ratio of one harness row, as a check that the machine
stayed steady between the two sides. -/
structure DriftLine where
  label : String
  ratioMilli : Nat
  warn : Bool
deriving Repr

/-- The whole comparison, ready to render. -/
structure CompareReport where
  options : CompareOptions
  baselineFiles : Array System.FilePath
  candidateFiles : Array System.FilePath
  preset : String
  rows : Array RowComparison
  drift : Array DriftLine
  /-- Whether the harness floor rows were present on the candidate side. -/
  floorChecked : Bool
  /-- `C(Kb + Kc, Kb)`: one over the chance of strict separation under no change. -/
  separationDenominator : Nat

/-- Whether any row is a `mismatch` or `missing`. -/
def CompareReport.failed (report : CompareReport) : Bool :=
  report.rows.any fun row ↦ row.verdict.fatal

/-- Binomial coefficient, exact at every step of the product. -/
def binomial (n k : Nat) : Nat :=
  if k > n then 0
  else
    let k := min k (n - k)
    (List.range k).foldl (fun acc i ↦ acc * (n - i) / (i + 1)) 1

/-- Group keys of the harness self-check, exempt from the floor alarm because they
define the floor. -/
def harnessGroupKeys : List String :=
  ["harness-floor", "harness-canary", "harness-chain-floor", "harness-chain-linearity"]

/-- Whether a row belongs to the harness self-check. -/
def RowKey.isHarness (key : RowKey) : Bool :=
  harnessGroupKeys.contains key.groupKey

/-- Rows matching `p` across one side, provided every file of the side has one.

A row present in only some invocations means an invocation went wrong, and is
treated as absent rather than averaged over fewer runs than the other rows. -/
def sideRowsWhere (files : Array ResultsFile) (p : CompareRow → Bool) :
    Option (Array CompareRow) :=
  let hits := files.filterMap fun file ↦ file.rows.find? p
  if hits.size == files.size && !files.isEmpty then some hits else none

/-- Rows with identity `key` across one side, present in every file or not at all. -/
def sideRows (files : Array ResultsFile) (key : RowKey) : Option (Array CompareRow) :=
  sideRowsWhere files fun row ↦ row.key == key

/-- The first row identity that occurs twice in a file, if any. -/
def duplicateKey? (file : ResultsFile) : Option RowKey :=
  let rec go (seen : List RowKey) : List CompareRow → Option RowKey
    | [] => none
    | row :: rows => if seen.contains row.key then some row.key else go (row.key :: seen) rows
  go [] file.rows.toList

/-- Every row identity, baseline order first, then candidate-only rows. -/
def orderedKeys (baseline candidate : Array ResultsFile) : List RowKey :=
  ((baseline ++ candidate).toList.flatMap fun file ↦ file.rows.toList.map (·.key)).eraseDups

/-- Reason to doubt a candidate that is faster than its problem allows.

A one-unit row cheaper than the empty harness loop, or a chained row cheaper per
operation than the two-instruction chain floor, did not do its work. The ratio
alarm catches the same thing when no floor row was measured. -/
def suspectReason (workUnits medB medC : Nat) (floor chainFloor : Option SideSummary) :
    Option String :=
  if medC * 10 < medB then some "ratio < 0.1"
  else if workUnits == 1 then
    match floor with
    | some f => if medC < f.median then some "below harness floor" else none
    | none => none
  else
    match chainFloor with
    | some f => if medC * f.workUnits < f.median * workUnits then some "below chain floor" else none
    | none => none

/-- Judge one row from whatever each side has for it. -/
def compareRow (thresholdPercent : Nat) (floor chainFloor : Option SideSummary) (key : RowKey)
    (b c : Option (Array CompareRow)) : RowComparison :=
  match b, c with
  | none, none =>
      { key, workUnits := 1, baseline := none, candidate := none, ratioMilli := none,
        verdict := Verdict.missing Side.candidate, suspect := none }
  | none, some cRows =>
      let summary := summariseSide cRows
      { key, workUnits := summary.workUnits, baseline := none, candidate := some summary,
        ratioMilli := none, verdict := Verdict.missing Side.baseline, suspect := none }
  | some bRows, none =>
      let summary := summariseSide bRows
      { key, workUnits := summary.workUnits, baseline := some summary, candidate := none,
        ratioMilli := none, verdict := Verdict.missing Side.candidate, suspect := none }
  | some bRows, some cRows =>
      let bSummary := summariseSide bRows
      let cSummary := summariseSide cRows
      let all := bRows ++ cRows
      let base :=
        { key, workUnits := bSummary.workUnits, baseline := some bSummary,
          candidate := some cSummary, ratioMilli := ratioMilli bSummary cSummary,
          verdict := Verdict.same, suspect := none : RowComparison }
      if all.any (·.workUnits != bSummary.workUnits) then
        { base with verdict := Verdict.mismatch "work_units", ratioMilli := none }
      else if all.any fun row ↦
          row.checksum != bSummary.checksum ||
            row.checksumIterations != bSummary.checksumIterations then
        { base with verdict := Verdict.mismatch "checksum", ratioMilli := none }
      else
        let verdict := judge thresholdPercent bSummary cSummary
        let suspect :=
          if key.isHarness || verdict == Verdict.unjudged "zero median" then none
          else suspectReason bSummary.workUnits bSummary.median cSummary.median floor chainFloor
        { base with verdict, suspect }

/-- Drift of one harness row between the sides, when both measured it. -/
def driftLine? (row : RowComparison) : Option DriftLine :=
  match row.baseline, row.candidate, row.ratioMilli with
  | some b, some c, some milli =>
      let label := row.key.groupKey ++
        (if row.key.digestClass.isEmpty then "" else " · " ++ row.key.digestClass)
      some { label, ratioMilli := milli, warn := c.median * 10 < b.median * 9 || c.median * 10 > b.median * 11 }
  | _, _, _ => none

/-- Compare the two sides.

Errors are input-level problems that leave nothing compared: a duplicate row
inside one file, no rows at all, or sides measured under different presets. -/
def compareResults (options : CompareOptions) (baseline candidate : Array ResultsFile) :
    Except String CompareReport := do
  for file in baseline ++ candidate do
    if let some key := duplicateKey? file then
      throw s!"duplicate row `{key.groupKey} / {key.name} / {key.digestClass}` in `{file.path}`"
  let rows := (baseline ++ candidate).toList.flatMap fun file ↦ file.rows.toList
  let preset ← match rows.head? with
    | none => throw "no benchmark rows found"
    | some row => pure row.preset
  if let some other := rows.find? fun row ↦ row.preset != preset then
    throw <|
      s!"presets differ (`{preset}` vs `{other.preset}`): rows measured under different " ++
      "budgets are not compared"
  let floor := (sideRowsWhere candidate fun row ↦ row.groupKey == "harness-floor").map
    summariseSide
  let chainFloor := (sideRowsWhere candidate fun row ↦
    row.groupKey == "harness-chain-floor" && row.digestClass == "latency").map summariseSide
  let comparisons := (orderedKeys baseline candidate).toArray.map fun key ↦
    compareRow options.thresholdPercent floor chainFloor key (sideRows baseline key)
      (sideRows candidate key)
  let drift := (comparisons.filter fun row ↦ row.key.isHarness).filterMap driftLine?
  pure {
    options
    baselineFiles := baseline.map (·.path)
    candidateFiles := candidate.map (·.path)
    preset
    rows := comparisons
    drift
    floorChecked := floor.isSome && chainFloor.isSome
    separationDenominator := binomial (baseline.size + candidate.size) baseline.size }

/-! ### Guards -/

#guard binomial 10 5 == 252
#guard binomial 2 1 == 2
#guard binomial 6 3 == 20

private def summaryOf (medians : Array Nat) : SideSummary :=
  summariseSide <| medians.map fun m ↦
    { groupKey := "g", digestClass := "", name := "n", method := "m", field := "F",
      inputShape := "s", preset := "medium", workUnits := 1, checksumIterations := 1,
      checksum := 1, sampleCount := 20, itersPerSample := 1, unreplicated := false,
      medianPicos := m, madPicos := 0, severeOutliers := 0 }

-- 10% faster and every candidate run beats every baseline run.
#guard judge 5 (summaryOf #[1000, 1010, 1020]) (summaryOf #[900, 910, 920]) == Verdict.faster
-- 7% faster by the medians, but the ranges overlap.
#guard judge 5 (summaryOf #[1000, 1010, 1020]) (summaryOf #[905, 930, 1005]) == Verdict.same
-- Separated, but inside the threshold.
#guard judge 5 (summaryOf #[1000, 1010, 1020]) (summaryOf #[1030, 1040, 1050]) == Verdict.same
-- Slower by 10%, separated.
#guard judge 5 (summaryOf #[1000, 1010, 1020]) (summaryOf #[1100, 1110, 1120]) == Verdict.slower
#guard judge 5 (summaryOf #[0]) (summaryOf #[5]) == Verdict.unjudged "zero median"
#guard ratioMilli (summaryOf #[1000]) (summaryOf #[954]) == some 954
#guard (summaryOf #[1000, 1010, 1020]).spreadTenths == 9

end CompPolyBench
