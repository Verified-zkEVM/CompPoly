/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Compare.Read
public import CompPolyBench.Compare.Render
public import CompPolyBench.Compare.Verdict

/-!
# A/B Comparison Command

`--compare` reads the results files two builds wrote and judges the candidate
against the baseline. It measures nothing itself; the driver
`scripts/bench-ab.sh` produces the files by running the two binaries turn about.

Exit codes: `0` when every row was judged, whatever the verdicts; `1` when
nothing could be compared (a path that does not exist, a malformed file, sides
measured under different presets); `3` when at least one row is a `mismatch` or
`missing`, which means the candidate changed what a row computes or which rows
exist, and the loop must stop and look rather than read a ratio.
-/

public section

namespace CompPolyBench

/-- Exit code when some row could not be judged for a correctness or join reason. -/
def compareExitFailed : UInt32 := 3

/-- Run the compare command. -/
def runCompare (options : CompareOptions) : IO UInt32 := do
  try
    let baselinePaths := (← options.baselines.toArray.mapM expandResultsPath).flatten
    let candidatePaths := (← options.candidates.toArray.mapM expandResultsPath).flatten
    let baseline ← baselinePaths.mapM readResultsFile
    let candidate ← candidatePaths.mapM readResultsFile
    match compareResults options baseline candidate with
    | Except.error message =>
        IO.eprintln message
        pure 1
    | Except.ok report =>
        let markdown := renderCompareMarkdown report
        IO.print markdown
        if let some outDir := options.outDir then
          IO.FS.createDirAll outDir
          let path := comparePath outDir (← makeRunId)
          IO.FS.writeFile path markdown
          IO.println s!"wrote {path}"
        for row in report.rows do
          if row.verdict.fatal then
            IO.eprintln s!"ERROR: {row.key.groupKey} / {renderRowLabel row.key}: {row.verdict.label}"
        pure (if report.failed then compareExitFailed else 0)
  catch e =>
    IO.eprintln s!"{e}"
    pure 1

end CompPolyBench
