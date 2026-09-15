/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPolyBench.Common
-- The guards at the end of this file evaluate `BenchRecord.toJsonLine` and the parser
-- at elaboration time, which needs the definitions available to the elaborator too.
public meta import CompPolyBench.Common
public meta import CompPolyBench.Harness.Stats

/-!
# Reading Benchmark Results Back

The half of the JSONL schema that an A/B comparison consumes, and the file and
directory readers that feed it. The writer is `BenchRecord.toJsonLine`; both use
the key names in `JsonKey`, and the guards at the bottom fail the build if the
two ever disagree on a key.
-/

public section

namespace CompPolyBench

/-- The fields of one JSONL row that a comparison reads.

Deliberately not `BenchRecord`: a comparison needs neither the sample vector nor
the sink digest, and a slimmer reader has fewer ways to fall out of step with
the writer. -/
structure CompareRow where
  groupKey : String
  digestClass : String
  name : String
  method : String
  field : String
  inputShape : String
  preset : String
  workUnits : Nat
  checksumIterations : Nat
  checksum : Nat
  sampleCount : Nat
  itersPerSample : Nat
  unreplicated : Bool
  medianPicos : Nat
  madPicos : Nat
  severeOutliers : Nat
deriving BEq, Repr, Inhabited

/-- Decode one JSON object into a row; a missing or mistyped key is an error. -/
def CompareRow.fromJson? (json : Lean.Json) : Except String CompareRow := do
  let str (key : String) : Except String String := json.getObjVal? key >>= Lean.Json.getStr?
  let nat (key : String) : Except String Nat := json.getObjVal? key >>= Lean.Json.getNat?
  let bool (key : String) : Except String Bool := json.getObjVal? key >>= Lean.Json.getBool?
  pure {
    groupKey := ← str JsonKey.groupKey
    digestClass := ← str JsonKey.digestClass
    name := ← str JsonKey.name
    method := ← str JsonKey.method
    field := ← str JsonKey.field
    inputShape := ← str JsonKey.inputShape
    preset := ← str JsonKey.preset
    workUnits := ← nat JsonKey.workUnits
    checksumIterations := ← nat JsonKey.checksumIterations
    checksum := ← nat JsonKey.checksum
    sampleCount := ← nat JsonKey.sampleCount
    itersPerSample := ← nat JsonKey.itersPerSample
    unreplicated := ← bool JsonKey.unreplicated
    medianPicos := ← nat JsonKey.medianPicos
    madPicos := ← nat JsonKey.madPicos
    severeOutliers := ← nat JsonKey.severeOutliers }

/-- Parse one JSONL line. -/
def CompareRow.parseLine (line : String) : Except String CompareRow :=
  Lean.Json.parse line >>= CompareRow.fromJson?

/-- One results file, with its path kept for the report header and error messages. -/
structure ResultsFile where
  path : System.FilePath
  rows : Array CompareRow

/-- Read one JSONL results file.

Blank lines are skipped; any other line that does not parse is an error naming
the file and the 1-based line, raised as `IO.userError`. Nothing has been
compared when this fires, so the caller reports it as an input error. -/
def readResultsFile (path : System.FilePath) : IO ResultsFile := do
  let lines ← IO.FS.lines path
  let mut rows : Array CompareRow := #[]
  let mut lineNo := 0
  for line in lines do
    lineNo := lineNo + 1
    if line.trimAscii.toString.isEmpty then
      continue
    match CompareRow.parseLine line with
    | Except.ok row => rows := rows.push row
    | Except.error message => throw <| IO.userError s!"{path}:{lineNo}: {message}"
  pure { path, rows }

/-- Whether a directory entry is a results file the harness wrote. -/
def isResultsFileName (fileName : String) : Bool :=
  fileName.startsWith "results-" && fileName.endsWith ".jsonl"

/-- Expand a `--baseline` or `--candidate` argument into results files.

A file is taken as it is. A directory contributes its immediate `results-*.jsonl`
children, sorted by name; it is not searched recursively, because the driver
gives every invocation its own directory and a recursive search would silently
merge runs. -/
def expandResultsPath (path : System.FilePath) : IO (Array System.FilePath) := do
  if ← path.isDir then
    let entries ← path.readDir
    let files := (entries.filter fun entry ↦ isResultsFileName entry.fileName).map (·.path)
    let files := files.qsort fun a b ↦ a.toString < b.toString
    if files.isEmpty then
      throw <| IO.userError s!"no results-*.jsonl files in `{path}`"
    pure files
  else if ← path.pathExists then
    pure #[path]
  else
    throw <| IO.userError s!"no such file or directory: `{path}`"

/-! ### Round-trip guards

Every field non-trivial, and a checksum above `2^63`, so the trip cannot pass by
accident. -/

private def sampleRecord : BenchRecord :=
  { groupKey := "g", groupTitle := "G", digestClass := "latency", name := "n",
    representation := "UInt64", method := "mul (latency)", preset := "medium", field := "F",
    inputShape := "s", warmupIterations := 1, checksumIterations := 2, measuredIterations := 3,
    totalNanos := 4, medianNanos := 5, workUnits := 1280, checksum := 18446744073709551557,
    sinkDigest := 7,
    stats := { count := 20, itersPerSample := 9, minPicos := 10, medianPicos := 11,
               meanPicos := 12, p95Picos := 13, stddevPicos := 14, madPicos := 15,
               mildOutliers := 1, severeOutliers := 2, unreplicated := false },
    samples := #[10, 11, 12] }

private def sampleRow : CompareRow :=
  { groupKey := "g", digestClass := "latency", name := "n", method := "mul (latency)",
    field := "F", inputShape := "s", preset := "medium", workUnits := 1280,
    checksumIterations := 2, checksum := 18446744073709551557, sampleCount := 20,
    itersPerSample := 9, unreplicated := false, medianPicos := 11, madPicos := 15,
    severeOutliers := 2 }

-- Whatever the writer emits today, the reader must read back.
#guard (CompareRow.parseLine sampleRecord.toJsonLine).toOption == some sampleRow

/-- A row copied from a real results file, samples truncated. A key renamed in both
writer and reader still fails here until this fixture is updated, which is the
point: the on-disk schema is a contract with files already written. -/
private def frozenLine : String :=
  "{\"group_key\":\"harness-floor\",\"group_title\":\"Harness loop and sink floor\"," ++
  "\"name\":\"harness-floor\",\"representation\":\"UInt64\",\"method\":\"empty body\"," ++
  "\"preset\":\"medium\",\"field\":\"none\",\"input_shape\":\"no input\"," ++
  "\"warmup_iterations\":33554431,\"checksum_iterations\":16," ++
  "\"measured_iterations\":11217040,\"total_nanos\":19905749,\"median_nanos\":1," ++
  "\"work_units\":1,\"digest_class\":\"\",\"checksum\":18119557631070038941," ++
  "\"sink_digest\":5331405383607749542,\"sample_count\":20,\"iters_per_sample\":560852," ++
  "\"unreplicated\":false,\"min_picos\":1757,\"median_picos\":1765,\"mean_picos\":1774," ++
  "\"p95_picos\":1830,\"stddev_picos\":19,\"mad_picos\":7,\"mild_outliers\":1," ++
  "\"severe_outliers\":0,\"samples_picos\":[1763,1759]}"

private def frozenRow : CompareRow :=
  { groupKey := "harness-floor", digestClass := "", name := "harness-floor",
    method := "empty body", field := "none", inputShape := "no input", preset := "medium",
    workUnits := 1, checksumIterations := 16, checksum := 18119557631070038941,
    sampleCount := 20, itersPerSample := 560852, unreplicated := false, medianPicos := 1765,
    madPicos := 7, severeOutliers := 0 }

#guard (CompareRow.parseLine frozenLine).toOption == some frozenRow

-- A missing key is an error, not a default.
#guard (CompareRow.parseLine "{\"group_key\":\"g\"}").toOption == none

end CompPolyBench
