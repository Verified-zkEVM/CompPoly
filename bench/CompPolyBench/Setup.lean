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
    "<key> [<key> ...]\n" ++
  "  lake exe CompPolyBench <key> [<key> ...]\n"

/-- Split a comma-separated CLI argument into nonempty group keys. -/
def splitGroupKeys (s : String) : List String :=
  (s.splitOn ",").filter fun key => !key.isEmpty

/-- Check whether a key is present in the known group list. -/
def knownGroupKey (key : String) : Bool :=
  allGroupInfos.any fun info => info.groupKey == key

/-- Parse benchmark CLI arguments. -/
partial def parseArgs : List String → Except String BenchCommand
  | [] => Except.ok (BenchCommand.run BenchSelection.all BenchOutput.all BenchPreset.large)
  | args =>
      let rec go (args : List String) (keys : List String) (output : Option BenchOutput)
          (preset : Option BenchPreset) : Except String BenchCommand :=
        match args with
        | [] =>
            let unknown := keys.filter fun key => !knownGroupKey key
            match unknown with
            | [] =>
                let selection :=
                  if keys.isEmpty then BenchSelection.all else BenchSelection.only keys.reverse
                Except.ok <|
                  BenchCommand.run selection (output.getD BenchOutput.all)
                    (preset.getD BenchPreset.large)
            | key :: _ => Except.error s!"unknown benchmark group `{key}`; use `--list`"
        | "--help" :: _ => Except.ok BenchCommand.help
        | "-h" :: _ => Except.ok BenchCommand.help
        | "--list" :: _ => Except.ok BenchCommand.list
        | "--small" :: rest =>
            setPresetMode preset BenchPreset.small >>= go rest keys output
        | "--medium" :: rest =>
            setPresetMode preset BenchPreset.medium >>= go rest keys output
        | "--large" :: rest =>
            setPresetMode preset BenchPreset.large >>= go rest keys output
        | "--markdown-only" :: rest =>
            setOutputMode output BenchOutput.markdownOnly >>= fun output =>
              go rest keys output preset
        | "--json-only" :: rest =>
            setOutputMode output BenchOutput.jsonOnly >>= fun output =>
              go rest keys output preset
        | "--group" :: key :: rest => go rest (key :: keys) output preset
        | "--group" :: [] => Except.error "missing value after `--group`"
        | "--groups" :: rawKeys :: rest =>
            go rest ((splitGroupKeys rawKeys).reverse ++ keys) output preset
        | "--groups" :: [] => Except.error "missing value after `--groups`"
        | arg :: rest =>
            if arg.startsWith "-" then
              Except.error s!"unknown option `{arg}`"
            else
              go rest (arg :: keys) output preset
      go args [] none none

/-- Print all runnable benchmark group keys. -/
def printGroupList : IO Unit := do
  IO.println "Available benchmark groups:"
  for info in allGroupInfos do
    IO.println s!"  {info.groupKey}  -  {info.title}"

/-- Run the complete benchmark suite and write selected reports. -/
def runSelected (selection : BenchSelection) (output : BenchOutput) (preset : BenchPreset) :
    IO UInt32 := do
  let runId ← makeRunId
  let gen := mkStdGen seed
  let (groups, _) ← runSelectedTasks allTasks preset selection gen
  let records := flattenGroups groups
  if output.writeJson then
    IO.FS.writeFile (resultsPath runId) (renderJsonl records)
  if output.writeMarkdown then
    let hardware ← collectRunnerHardware
    IO.FS.writeFile (reportPath runId) (renderMarkdown hardware preset groups)
  IO.println <|
    s!"wrote `{records.size}` benchmark records in `{groups.size}` groups for run `{runId}`"
  match checksumMismatchGroups groups with
  | [] => pure 0
  | mismatchedGroups =>
      for group in mismatchedGroups do
        IO.eprintln s!"ERROR: checksum mismatch in benchmark group `{group.groupKey}`"
      pure 1

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
  | Except.ok (BenchCommand.run selection output preset) =>
      runSelected selection output preset

end CompPolyBench
