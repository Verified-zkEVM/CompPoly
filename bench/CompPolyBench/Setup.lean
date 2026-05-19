/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Bivariate.Basic
import CompPolyBench.Fields.Binary.AdditiveNTT.Impl
import CompPolyBench.Multilinear.Basic
import CompPolyBench.Multivariate.CMvPolynomial
import CompPolyBench.Univariate

/-!
# Benchmark Suite Setup

Top-level orchestration for the compiled benchmark executable.
-/

namespace CompPolyBench

/-- Runnable benchmark registry. -/
def allTasks : List BenchTask :=
  univariateTasks ++ multivariateTasks ++ multilinearTasks ++ bivariateTasks ++ additiveNttTasks

/-- Metadata for every benchmark group accepted by the command-line selector. -/
def allGroupInfos : List BenchGroupInfo :=
  (allTasks.map fun task => task.infos).flatten

/-- Command selected by benchmark CLI arguments. -/
inductive BenchCommand where
  | run (selection : BenchSelection)
  | list
  | help

/-- Command-line usage text. -/
def usage : String :=
  "Usage:\n" ++
  "  lake exe CompPolyBench\n" ++
  "  lake exe CompPolyBench --list\n" ++
  "  lake exe CompPolyBench --group <key> [--group <key> ...]\n" ++
  "  lake exe CompPolyBench <key> [<key> ...]\n"

/-- Split a comma-separated CLI argument into nonempty group keys. -/
def splitGroupKeys (s : String) : List String :=
  (s.splitOn ",").filter fun key => !key.isEmpty

/-- Check whether a key is present in the known group list. -/
def knownGroupKey (key : String) : Bool :=
  allGroupInfos.any fun info => info.groupKey == key

/-- Parse benchmark CLI arguments. -/
partial def parseArgs : List String → Except String BenchCommand
  | [] => Except.ok (BenchCommand.run BenchSelection.all)
  | args =>
      let rec go (args : List String) (keys : List String) : Except String BenchCommand :=
        match args with
        | [] =>
            let unknown := keys.filter fun key => !knownGroupKey key
            match unknown with
            | [] =>
                Except.ok <| BenchCommand.run <|
                  if keys.isEmpty then BenchSelection.all else BenchSelection.only keys.reverse
            | key :: _ => Except.error s!"unknown benchmark group `{key}`; use `--list`"
        | "--help" :: _ => Except.ok BenchCommand.help
        | "-h" :: _ => Except.ok BenchCommand.help
        | "--list" :: _ => Except.ok BenchCommand.list
        | "--group" :: key :: rest => go rest (key :: keys)
        | "--group" :: [] => Except.error "missing value after `--group`"
        | "--groups" :: rawKeys :: rest => go rest ((splitGroupKeys rawKeys).reverse ++ keys)
        | "--groups" :: [] => Except.error "missing value after `--groups`"
        | arg :: rest =>
            if arg.startsWith "-" then
              Except.error s!"unknown option `{arg}`"
            else
              go rest (arg :: keys)
      go args []

/-- Print all runnable benchmark group keys. -/
def printGroupList : IO Unit := do
  IO.println "Available benchmark groups:"
  for info in allGroupInfos do
    IO.println s!"  {info.groupKey}  -  {info.title}"

/-- Run the complete benchmark suite and write reports. -/
def runSelected (selection : BenchSelection) : IO UInt32 := do
  let runId ← makeRunId
  let hardware ← collectRunnerHardware
  let gen := mkStdGen seed
  let (groups, _) ← runSelectedTasks allTasks selection gen
  let records := flattenGroups groups
  let results := resultsPath runId
  let report := reportPath runId
  IO.FS.writeFile results (renderJsonl records)
  IO.FS.writeFile report (renderMarkdown hardware groups)
  IO.println <|
    s!"wrote `{records.size}` benchmark records in `{groups.size}` groups for run `{runId}`"
  pure 0

/-- Run the complete benchmark suite according to command-line arguments. -/
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
  | Except.ok (BenchCommand.run selection) =>
      runSelected selection

end CompPolyBench
