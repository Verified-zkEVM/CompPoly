/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPolyBench.Bivariate.Basic
public import CompPolyBench.Bivariate.Factor
public import CompPolyBench.Bivariate.GuruswamiSudan
public import CompPolyBench.Compare
public import CompPolyBench.Fields.Arith
public import CompPolyBench.Fields.Binary.AdditiveNTT.Impl
public import CompPolyBench.Fields.Binary.Tower
public import CompPolyBench.Fields.Binary.Tower.Scalar
public import CompPolyBench.Fields.Extension
public import CompPolyBench.Fields.Montgomery
public import CompPolyBench.Harness.SelfCheck
public import CompPolyBench.Multilinear.Basic
public import CompPolyBench.Multivariate.CMvPolynomial
public import CompPolyBench.Univariate

/-!
# Benchmark Suite Setup

Top-level orchestration for the compiled benchmark executable.
-/

public section

namespace CompPolyBench

/-- Runnable benchmark registry. -/
def allTasks : List BenchTask :=
  harnessTasks ++ univariateTasks ++ multivariateTasks ++ multilinearTasks ++ bivariateTasks ++
    factorTasks ++ guruswamiSudanTasks ++ additiveNttTasks ++ extensionTasks ++
    montgomeryInvTasks ++ towerTasks ++ towerScalarTasks ++ fieldArithTasks

/-- Metadata for every benchmark group accepted by the command-line selector. -/
def allGroupInfos : List BenchGroupInfo :=
  (allTasks.map fun task ↦ task.infos).flatten

/-- Output artifact set requested by the command line. -/
inductive BenchOutput where
  | all
  | markdownOnly
  | jsonOnly
deriving BEq

/-- Whether to write JSONL benchmark rows for this output mode. -/
def BenchOutput.writeJson : BenchOutput → Bool
  | BenchOutput.all => true
  | BenchOutput.markdownOnly => false
  | BenchOutput.jsonOnly => true

/-- Whether to write the Markdown benchmark report for this output mode. -/
def BenchOutput.writeMarkdown : BenchOutput → Bool
  | BenchOutput.all => true
  | BenchOutput.markdownOnly => true
  | BenchOutput.jsonOnly => false

/-- Add an output-mode flag, rejecting contradictory modes. -/
def setOutputMode (current : Option BenchOutput) (mode : BenchOutput) :
    Except String (Option BenchOutput) :=
  match current with
  | none => Except.ok (some mode)
  | some existing =>
      if existing == mode then
        Except.ok current
      else
        Except.error "cannot combine Markdown-only and JSON-only output modes"

/-- Add a benchmark preset flag, rejecting contradictory presets. -/
def setPresetMode (current : Option BenchPreset) (preset : BenchPreset) :
    Except String (Option BenchPreset) :=
  match current with
  | none => Except.ok (some preset)
  | some existing =>
      if existing == preset then
        Except.ok current
      else
        Except.error "cannot combine multiple benchmark presets"

/-- Command selected by benchmark CLI arguments. -/
inductive BenchCommand where
  | run (selection : BenchSelection) (output : BenchOutput) (preset : BenchPreset)
      (validateOnly : Bool) (outDir : System.FilePath)
  | compare (options : CompareOptions)
  | list
  | help

/-- Command-line usage text. -/
def usage : String :=
  "Usage:\n" ++
  "  lake exe CompPolyBench\n" ++
  "  lake exe CompPolyBench --list\n" ++
  "  lake exe CompPolyBench [--small|--medium|--large]\n" ++
  "  lake exe CompPolyBench --group <key> [--group <key> ...]\n" ++
  "  lake exe CompPolyBench --groups <key,key,...>\n" ++
  "  lake exe CompPolyBench [--small|--medium|--large] [--markdown-only|--json-only] " ++
    "[--out-dir <dir>] <key> [<key> ...]\n" ++
  "  lake exe CompPolyBench --validate-only [--groups <key,key,...>]\n" ++
  "  lake exe CompPolyBench <key> [<key> ...]\n" ++
  "  lake exe CompPolyBench --compare --baseline <path> [--baseline <path> ...]\n" ++
  "                         --candidate <path> [--candidate <path> ...]\n" ++
  "                         [--threshold <percent>] [--out-dir <dir>]\n" ++
  "\n" ++
  "  --validate-only  check that each group's implementations agree, collecting\n" ++
  "                   no timings. This is the correctness half of the suite and\n" ++
  "                   is what CI runs; use the benchmark workflow for timings.\n" ++
  "  --out-dir <dir>  write results, report and manifest into <dir> instead of\n" ++
  "                   bench/out. With --compare, also write compare-<run>.md there.\n" ++
  "  --compare        judge candidate runs against baseline runs; measures nothing.\n" ++
  "                   Each path is a results-*.jsonl file or a directory of them,\n" ++
  "                   one per invocation. Exit 0 when every row was judged, 3 on a\n" ++
  "                   checksum mismatch or a row present on one side only.\n" ++
  "  --threshold <p>  practical-importance threshold in percent, 1..99 (default 5).\n"

/-- Split a comma-separated CLI argument into nonempty group keys. -/
def splitGroupKeys (s : String) : List String :=
  (s.splitOn ",").filter fun key ↦ !key.isEmpty

/-- Check whether a key is present in the known group list. -/
def knownGroupKey (key : String) : Bool :=
  allGroupInfos.any fun info ↦ info.groupKey == key

/-- Everything the argument parser has seen so far; lists are accumulated reversed. -/
structure ParseState where
  keys : List String := []
  output : Option BenchOutput := none
  preset : Option BenchPreset := none
  validateOnly : Bool := false
  outDir : Option System.FilePath := none
  compare : Bool := false
  baselines : List System.FilePath := []
  candidates : List System.FilePath := []
  threshold : Option Nat := none

/-- Add an output directory, rejecting a second, different one. -/
def setOutDir (current : Option System.FilePath) (dir : String) :
    Except String (Option System.FilePath) :=
  match current with
  | none => Except.ok (some dir)
  | some existing =>
      if existing.toString == dir then
        Except.ok current
      else
        Except.error "cannot combine multiple `--out-dir` values"

/-- Parse the practical-importance threshold, a whole percentage in `1..99`. -/
def parseThreshold (raw : String) : Except String Nat :=
  match raw.toNat? with
  | some t =>
      if 1 ≤ t && t ≤ 99 then Except.ok t
      else Except.error s!"`--threshold` expects a whole percentage between 1 and 99, got `{raw}`"
  | none => Except.error s!"`--threshold` expects a whole percentage between 1 and 99, got `{raw}`"

/-- Turn the accumulated state into a command, checking the flags fit together. -/
def finishParse (state : ParseState) : Except String BenchCommand :=
  if state.compare then
    if !state.keys.isEmpty || state.preset.isSome || state.output.isSome ||
        state.validateOnly then
      Except.error <|
        "`--compare` cannot be combined with group selection, presets, `--validate-only` " ++
        "or output modes"
    else if state.baselines.isEmpty || state.candidates.isEmpty then
      Except.error "`--compare` needs at least one `--baseline` and one `--candidate`"
    else
      Except.ok <| BenchCommand.compare {
        baselines := state.baselines.reverse
        candidates := state.candidates.reverse
        thresholdPercent := state.threshold.getD 5
        outDir := state.outDir }
  else if !state.baselines.isEmpty || !state.candidates.isEmpty || state.threshold.isSome then
    Except.error "`--baseline`, `--candidate` and `--threshold` require `--compare`"
  else
    match state.keys.filter fun key ↦ !knownGroupKey key with
    | [] =>
        let selection :=
          if state.keys.isEmpty then BenchSelection.all
          else BenchSelection.only state.keys.reverse
        Except.ok <|
          BenchCommand.run selection (state.output.getD BenchOutput.all)
            (state.preset.getD BenchPreset.large) state.validateOnly
            (state.outDir.getD outputDir)
    | key :: _ => Except.error s!"unknown benchmark group `{key}`; use `--list`"

/-- Parse benchmark CLI arguments. -/
partial def parseArgs : List String → Except String BenchCommand
  | [] =>
      Except.ok <|
        BenchCommand.run BenchSelection.all BenchOutput.all BenchPreset.large false outputDir
  | args =>
      let rec go (args : List String) (state : ParseState) : Except String BenchCommand :=
        match args with
        | [] => finishParse state
        | "--help" :: _ => Except.ok BenchCommand.help
        | "-h" :: _ => Except.ok BenchCommand.help
        | "--list" :: _ => Except.ok BenchCommand.list
        | "--small" :: rest =>
            setPresetMode state.preset BenchPreset.small >>= fun preset ↦
              go rest { state with preset }
        | "--medium" :: rest =>
            setPresetMode state.preset BenchPreset.medium >>= fun preset ↦
              go rest { state with preset }
        | "--large" :: rest =>
            setPresetMode state.preset BenchPreset.large >>= fun preset ↦
              go rest { state with preset }
        | "--validate-only" :: rest => go rest { state with validateOnly := true }
        | "--markdown-only" :: rest =>
            setOutputMode state.output BenchOutput.markdownOnly >>= fun output ↦
              go rest { state with output }
        | "--json-only" :: rest =>
            setOutputMode state.output BenchOutput.jsonOnly >>= fun output ↦
              go rest { state with output }
        | "--group" :: key :: rest => go rest { state with keys := key :: state.keys }
        | "--group" :: [] => Except.error "missing value after `--group`"
        | "--groups" :: rawKeys :: rest =>
            go rest { state with keys := (splitGroupKeys rawKeys).reverse ++ state.keys }
        | "--groups" :: [] => Except.error "missing value after `--groups`"
        | "--out-dir" :: dir :: rest =>
            setOutDir state.outDir dir >>= fun outDir ↦ go rest { state with outDir }
        | "--out-dir" :: [] => Except.error "missing value after `--out-dir`"
        | "--compare" :: rest => go rest { state with compare := true }
        | "--baseline" :: path :: rest =>
            go rest { state with baselines := System.FilePath.mk path :: state.baselines }
        | "--baseline" :: [] => Except.error "missing value after `--baseline`"
        | "--candidate" :: path :: rest =>
            go rest { state with candidates := System.FilePath.mk path :: state.candidates }
        | "--candidate" :: [] => Except.error "missing value after `--candidate`"
        | "--threshold" :: raw :: rest =>
            parseThreshold raw >>= fun t ↦ go rest { state with threshold := some t }
        | "--threshold" :: [] => Except.error "missing value after `--threshold`"
        | arg :: rest =>
            if arg.startsWith "-" then
              Except.error s!"unknown option `{arg}`"
            else
              go rest { state with keys := arg :: state.keys }
      go args {}

/-- Print all runnable benchmark group keys. -/
def printGroupList : IO Unit := do
  IO.println "Available benchmark groups:"
  for info in allGroupInfos do
    IO.println s!"  {info.groupKey}  -  {info.title}"

/-- Run selected benchmark groups and write the requested reports. -/
def runSelected (selection : BenchSelection) (output : BenchOutput) (preset : BenchPreset)
    (validateOnly : Bool) (outDir : System.FilePath) : IO UInt32 := do
  let runId ← makeRunId
  let gen := mkStdGen seed
  let (groups, _) ← runSelectedTasks allTasks preset selection gen
  let records := flattenGroups groups
  IO.FS.createDirAll outDir
  -- Written for every run, including `--validate-only` and `--markdown-only`: a
  -- result nobody can attribute to a commit and a machine is not worth keeping.
  let manifest ← collectRunManifest runId preset validateOnly selection groups.size records.size
  IO.FS.writeFile (manifestPath outDir runId) manifest.render
  if output.writeJson then
    IO.FS.writeFile (resultsPath outDir runId) (renderJsonl records)
  if output.writeMarkdown then
    if validateOnly then
      IO.FS.writeFile (reportPath outDir runId) (renderValidationMarkdown preset groups)
    else
      IO.FS.writeFile (reportPath outDir runId) (renderMarkdown manifest.hardware preset groups)
  IO.println <|
    if validateOnly then
      s!"validated {records.size} benchmark records in {groups.size} groups for run {runId}"
    else
      s!"wrote {records.size} benchmark records in {groups.size} groups for run {runId}"
  let mut failed := false
  for group in checksumMismatchGroups groups do
    IO.eprintln s!"ERROR: checksum mismatch in benchmark group `{group.groupKey}`"
    failed := true
  -- Rows of one group measure the same problem, so disagreeing on `workUnits`
  -- means the group is mis-specified rather than merely unrenderable.
  for group in workUnitsMismatchGroups groups do
    IO.eprintln <|
      s!"ERROR: rows of benchmark group `{group.groupKey}` disagree on workUnits; " ++
      "every row of a group must declare the same problem size"
    failed := true
  pure (if failed then 1 else 0)

/-- Execute the benchmark command selected by command-line arguments. -/
def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | Except.error message =>
      IO.eprintln message
      IO.eprintln usage
      pure 1
  | Except.ok BenchCommand.help =>
      IO.println usage
      pure 0
  | Except.ok BenchCommand.list =>
      printGroupList
      pure 0
  | Except.ok (BenchCommand.compare options) =>
      runCompare options
  | Except.ok (BenchCommand.run selection output preset validateOnly outDir) =>
      validateOnlyRef.set validateOnly
      runSelected selection output preset validateOnly outDir

end CompPolyBench
