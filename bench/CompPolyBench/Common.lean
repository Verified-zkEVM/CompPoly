/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import Init.Data.Random
import Lean.Data.Json.Parser
import Std.Time
import CompPoly.Fields.BabyBear
import CompPoly.Fields.Binary.AdditiveNTT.Impl
import CompPoly.Fields.Goldilocks
import CompPoly.Fields.KoalaBear
import CompPoly.Univariate.BatchEval
import CompPoly.Univariate.Basic

/-!
# Shared Benchmark Helpers

Common data structures, input generators, checksum utilities, and report rendering
for the compiled benchmark executable.
-/

open CompPoly
open ConcreteBinaryTower

namespace CompPolyBench

/-- Fixed seed used to make benchmark inputs deterministic across runs. -/
def seed : Nat := 20260504

/-- Number of warmup iterations for ordinary evaluation benchmarks. -/
def warmupIterations : Nat := 100

/-- Number of measured iterations for ordinary evaluation benchmarks. -/
def measuredIterations : Nat := 5000

/-- Number of warmup iterations for full-array batch-evaluation benchmarks. -/
def batchWarmupIterations : Nat := 1

/-- Number of measured iterations for full-array batch-evaluation benchmarks. -/
def batchMeasuredIterations : Nat := 5

/-- Number of warmup iterations for medium full-array batch-evaluation benchmarks. -/
def mediumBatchWarmupIterations : Nat := 1

/-- Number of measured iterations for medium full-array batch-evaluation benchmarks. -/
def mediumBatchMeasuredIterations : Nat := 10

/-- Number of warmup iterations for large full-array batch-evaluation benchmarks. -/
def largeBatchWarmupIterations : Nat := 1

/-- Number of measured iterations for large full-array batch-evaluation benchmarks. -/
def largeBatchMeasuredIterations : Nat := 10

/-- Number of warmup iterations for direct monic-remainder benchmarks. -/
def modWarmupIterations : Nat := 1

/-- Number of measured iterations for direct monic-remainder benchmarks. -/
def modMeasuredIterations : Nat := 20

/-- Number of warmup iterations for medium direct monic-remainder benchmarks. -/
def mediumModWarmupIterations : Nat := 1

/-- Number of measured iterations for medium direct monic-remainder benchmarks. -/
def mediumModMeasuredIterations : Nat := 5

/-- Number of warmup iterations for direct univariate multiplication benchmarks. -/
def mulWarmupIterations : Nat := 1

/-- Number of measured iterations for direct univariate multiplication benchmarks. -/
def mulMeasuredIterations : Nat := 20

/-- Number of warmup iterations for the slower additive NTT benchmark. -/
def additiveNttWarmupIterations : Nat := 10

/-- Number of measured iterations for the smaller additive NTT benchmark. -/
def additiveNttMeasuredIterations : Nat := 1000

/-- Primality witness used for generic `ZMod` benchmarks over `BabyBear`. -/
instance : Fact (Nat.Prime BabyBear.fieldSize) where
  out := BabyBear.is_prime

/-- Primality witness used for generic `ZMod` benchmarks over `Goldilocks`. -/
instance : Fact (Nat.Prime Goldilocks.fieldSize) where
  out := Goldilocks.is_prime

/-- Result row emitted by one timed benchmark case. -/
structure BenchRecord where
  name : String
  representation : String
  method : String
  field : String
  inputShape : String
  warmupIterations : Nat
  measuredIterations : Nat
  totalNanos : Nat
  averageNanos : Nat
  checksum : Nat

/-- A set of benchmark rows expected to produce matching checksums. -/
structure BenchGroup where
  groupKey : String
  title : String
  records : Array BenchRecord

/-- Lightweight metadata for a runnable benchmark group. -/
structure BenchGroupInfo where
  groupKey : String
  title : String

/-- Selection of benchmark groups requested by the command line. -/
inductive BenchSelection where
  | all
  | only (keys : List String)

/-- Runnable benchmark group entry used by the command-line registry. -/
structure BenchTask where
  infos : List BenchGroupInfo
  runTask : BenchSelection → StdGen → IO (Array BenchGroup × StdGen)

/-- Decide whether a group key should run under a selection. -/
def BenchSelection.selects : BenchSelection → String → Bool
  | BenchSelection.all, _ => true
  | BenchSelection.only keys, key => keys.any fun selected => selected == key

/-- Decide whether any key in a collection should run under a selection. -/
def BenchSelection.selectsAny (selection : BenchSelection) (keys : List String) : Bool :=
  match selection with
  | BenchSelection.all => true
  | BenchSelection.only _ => keys.any selection.selects

/-- Select runnable benchmark tasks from a registry. -/
def BenchSelection.filterTasks (selection : BenchSelection)
    (tasks : List BenchTask) : List BenchTask :=
  match selection with
  | BenchSelection.all => tasks
  | BenchSelection.only _ =>
      tasks.filter fun task =>
        selection.selectsAny (task.infos.map fun info => info.groupKey)

/-- Build one registry task from metadata and a single-group runner. -/
def BenchTask.fromGroupRunner (info : BenchGroupInfo)
    (runGroup : StdGen → IO (BenchGroup × StdGen)) : BenchTask where
  infos := [info]
  runTask := fun _ gen => do
    let (group, gen) ← runGroup gen
    pure (#[group], gen)

/-- Run selected tasks from a registry and concatenate their emitted groups. -/
def runSelectedTasks (tasks : List BenchTask) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  let mut gen := gen
  let mut groups := #[]
  for task in selection.filterTasks tasks do
    let (taskGroups, nextGen) ← task.runTask selection gen
    gen := nextGen
    for group in taskGroups do
      groups := groups.push group
  pure (groups, gen)

/-- Hardware metadata included in benchmark reports when available. -/
structure RunnerHardware where
  runnerOs : Option String
  runnerArch : Option String
  cpuModel : Option String
  logicalCpus : Option String
  coresPerSocket : Option String
  threadsPerCore : Option String
  sockets : Option String
  ramTotal : Option String
  rootDisk : Option String
  hypervisor : Option String

/-- Build a compact timestamp identifier for generated report filenames. -/
def makeRunId : IO String := do
  let started ← Std.Time.ZonedDateTime.now
  pure <| started.format "yyMMdd-HHmmss"

/-- Path for the generated JSONL benchmark results. -/
def resultsPath (runId : String) : System.FilePath :=
  "bench" / ("evaluation-bench-results-" ++ runId ++ ".jsonl")

/-- Path for the generated Markdown benchmark report. -/
def reportPath (runId : String) : System.FilePath :=
  "bench" / ("evaluation-bench-report-" ++ runId ++ ".md")

/-- Trim command output and normalize empty output to the empty string. -/
def trimCommandOutput (s : String) : String :=
  let trimmed := s.trimAscii.toString
  if trimmed.isEmpty then "" else trimmed

/-- Run an optional host-info command, returning `none` if it fails or prints nothing. -/
def runInfoCommand (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let output ← IO.Process.output { cmd := cmd, args := args }
    if output.exitCode = 0 then
      let text := trimCommandOutput output.stdout
      pure <| if text.isEmpty then none else some text
    else
      pure none
  catch _ =>
    pure none

/-- Read a string field from a JSON object. -/
def jsonObjString? (json : Lean.Json) (key : String) : Option String :=
  (json.getObjVal? key >>= Lean.Json.getStr?).toOption

/-- Extract a named field from `lscpu --json` output. -/
def lscpuJsonField (output key : String) : Option String := do
  let json ← (Lean.Json.parse output).toOption
  let fields ← (json.getObjVal? "lscpu" >>= Lean.Json.getArr?).toOption
  let rec go : List Lean.Json → Option String
    | [] => none
    | field :: fields =>
        match jsonObjString? field "field", jsonObjString? field "data" with
        | some name, some value => if name = key then some value else go fields
        | _, _ => go fields
  go fields.toList

/-- Split a command-output row on ASCII spaces and tabs. -/
def whitespaceFields (s : String) : List String :=
  (s.replace "\t" " ").splitOn " " |>.filter fun field => !field.isEmpty

/-- Parse the root filesystem size from `df` output. -/
def dfRootSize (output : String) : Option String :=
  let lines := output.splitOn "\n"
  match lines with
  | _header :: row :: _ =>
      match whitespaceFields row with
      | size :: _ => some size
      | _ => none
  | _ => none

/-- Parse total memory from `/proc/meminfo` and report whole GiB. -/
def memTotalGib (output : String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | line :: lines =>
        match whitespaceFields line with
        | "MemTotal:" :: kib :: _ =>
            match kib.toNat? with
            | some kib =>
                let gib := kib / (1024 * 1024)
                some <| toString gib ++ " GiB"
            | none => go lines
        | _ => go lines
  go (output.splitOn "\n")

/-- Collect best-effort GitHub runner or local machine metadata. -/
def collectRunnerHardware : IO RunnerHardware := do
  let runnerOs ← IO.getEnv "RUNNER_OS"
  let runnerArch ← IO.getEnv "RUNNER_ARCH"
  let nproc ← runInfoCommand "nproc" #[]
  let lscpu ← runInfoCommand "lscpu" #["--json"]
  let meminfo ←
    try
      let text ← IO.FS.readFile "/proc/meminfo"
      pure (some text)
    catch _ =>
      pure none
  let dfRoot ← runInfoCommand "df" #["--output=size", "-h", "/"]
  pure {
    runnerOs := runnerOs
    runnerArch := runnerArch
    cpuModel := lscpu.bind fun output => lscpuJsonField output "Model name:"
    logicalCpus := nproc.orElse fun _ => lscpu.bind fun output => lscpuJsonField output "CPU(s):"
    coresPerSocket := lscpu.bind fun output => lscpuJsonField output "Core(s) per socket:"
    threadsPerCore := lscpu.bind fun output => lscpuJsonField output "Thread(s) per core:"
    sockets := lscpu.bind fun output => lscpuJsonField output "Socket(s):"
    ramTotal := meminfo.bind memTotalGib
    rootDisk := dfRoot.bind dfRootSize
    hypervisor := lscpu.bind fun output => lscpuJsonField output "Hypervisor vendor:"
  }

/-- Generate one pseudo-random natural number and advance the generator. -/
def nextNat (lo hi : Nat) : StateM StdGen Nat := do
  let g ← get
  let (n, g') := randNat g lo hi
  set g'
  pure n

/-- Generate an array of pseudo-random natural numbers in the given range. -/
def randomNatArray (size : Nat) (hi : Nat) : StateM StdGen (Array Nat) := do
  let mut values := #[]
  for _ in [0:size] do
    values := values.push (← nextNat 0 hi)
  pure values

/-- Generate dense or patterned-sparse coefficients over `ZMod modulus`. -/
def zmodArrayWithStride (modulus : Nat) (size sparseStride : Nat) :
    StateM StdGen (Array (ZMod modulus)) := do
  let values ← randomNatArray size (modulus - 1)
  let mut coeffs := #[]
  for i in [0:size] do
    let value : ZMod modulus :=
      if 0 < sparseStride && i % sparseStride != 0 then
        0
      else
        (values.getD i 0 : ZMod modulus)
    coeffs := coeffs.push value
  pure coeffs

/-- Generate dense or patterned-sparse coefficients over `ZMod modulus`. -/
def zmodArray (modulus : Nat) (size : Nat) (sparse : Bool) :
    StateM StdGen (Array (ZMod modulus)) :=
  zmodArrayWithStride modulus size (if sparse then 4 else 0)

/-- Generate BabyBear coefficients with the same shape controls as `zmodArray`. -/
def babyBearArray (size : Nat) (sparse : Bool) : StateM StdGen (Array BabyBear.Field) := do
  zmodArray BabyBear.fieldSize size sparse

/-- Generate BabyBear coefficients with a nonzero every `sparseStride` entries. -/
def babyBearArrayWithStride (size sparseStride : Nat) :
    StateM StdGen (Array BabyBear.Field) := do
  zmodArrayWithStride BabyBear.fieldSize size sparseStride

/-- Generate BabyBear vectors for multilinear benchmark inputs. -/
def babyBearVector (size : Nat) (sparse : Bool) : StateM StdGen (Array BabyBear.Field) :=
  babyBearArray size sparse

/-- Generate dense BabyBear evaluation points. -/
def babyBearPoints (size : Nat) : StateM StdGen (Array BabyBear.Field) :=
  babyBearArray size false

/-- Generate KoalaBear coefficients with the same shape controls as `zmodArray`. -/
def koalaBearArray (size : Nat) (sparse : Bool) :
    StateM StdGen (Array KoalaBear.Field) := do
  zmodArray KoalaBear.fieldSize size sparse

/-- Build a canonical computable polynomial from generated coefficients. -/
def cpolyOfArray {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (coeffs : Array R) : CPolynomial R :=
  let p : CPolynomial.Raw R := coeffs
  ⟨p.trim, CPolynomial.Raw.Trim.isCanonical_trim p⟩

/-- Build a monic divisor as a product of linear factors `X - C x`. -/
def monicDivisorFromPoints {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (xs : Array R) : CPolynomial R :=
  xs.foldl (fun acc x => acc * CPolynomial.linearFactor x) (CPolynomial.C 1)

/-- Mix one benchmark output value into a stable checksum accumulator. -/
def mixChecksum (acc value : Nat) : Nat :=
  (acc * 16777619 + value + 97) % 18446744073709551557

/-- Convert a BabyBear field element to a checksum word. -/
def checksumBabyBear (x : BabyBear.Field) : Nat :=
  ZMod.val x

/-- Convert a KoalaBear field element to a checksum word. -/
def checksumKoalaBear (x : KoalaBear.Field) : Nat :=
  ZMod.val x

/-- Convert a `ZMod` element to a checksum word. -/
def checksumZMod {modulus : Nat} (x : ZMod modulus) : Nat :=
  ZMod.val x

/-- Convert a concrete `BTF₃` element to a checksum word. -/
def checksumBtf3 (x : AdditiveNTT.BTF₃) : Nat :=
  BitVec.toNat x

/-- Convert a concrete binary-tower field element to a checksum word. -/
def checksumConcreteBtf {k : Nat} (x : ConcreteBTField k) : Nat :=
  BitVec.toNat x

/-- Checksum an array-like benchmark result. -/
def checksumArray (checksum : α → Nat) (xs : Array α) : Nat :=
  xs.foldl (fun acc x => mixChecksum acc (checksum x)) 0

/-- Checksum a canonical univariate polynomial by its coefficient array. -/
def checksumCPolynomial [Zero α] (checksum : α → Nat) (p : CPolynomial α) : Nat :=
  checksumArray checksum p.val

/-- Checksum a raw univariate polynomial by its stored coefficient array. -/
def checksumRawPolynomial (checksum : α → Nat) (p : CPolynomial.Raw α) : Nat :=
  checksumArray checksum p

/-- Time one benchmark closure and package its metadata and checksum. -/
def runTimed (name representation method field inputShape : String)
    (warmup measured : Nat) (run : Nat → α) (checksum : α → Nat) : IO BenchRecord := do
  for i in [0:warmup] do
    let _ := run i
    pure ()
  let start ← IO.monoNanosNow
  let mut acc := 0
  for i in [0:measured] do
    acc := mixChecksum acc (checksum (run i))
  let stop ← IO.monoNanosNow
  let total := stop - start
  pure {
    name := name
    representation := representation
    method := method
    field := field
    inputShape := inputShape
    warmupIterations := warmup
    measuredIterations := measured
    totalNanos := total
    averageNanos := if measured = 0 then 0 else total / measured
    checksum := acc
  }

/-- Append benchmark records without relying on array append notation. -/
def appendRecords (xs ys : Array BenchRecord) : Array BenchRecord :=
  ys.foldl (init := xs) fun acc record => acc.push record

/-- Append benchmark groups without relying on array append notation. -/
def appendGroups (xs ys : Array BenchGroup) : Array BenchGroup :=
  ys.foldl (init := xs) fun acc group => acc.push group

/-- Flatten grouped benchmark records for JSONL output. -/
def flattenGroups (groups : Array BenchGroup) : Array BenchRecord :=
  groups.foldl (init := #[]) fun acc group => appendRecords acc group.records

/-- Render a benchmark string field as a JSON string. -/
def jsonString (s : String) : String :=
  "\"" ++ s ++ "\""

/-- Render one benchmark record as a JSONL row. -/
def BenchRecord.toJsonLine (record : BenchRecord) : String :=
  "{" ++ String.intercalate "," [
    "\"name\":" ++ jsonString record.name,
    "\"representation\":" ++ jsonString record.representation,
    "\"method\":" ++ jsonString record.method,
    "\"field\":" ++ jsonString record.field,
    "\"input_shape\":" ++ jsonString record.inputShape,
    "\"warmup_iterations\":" ++ toString record.warmupIterations,
    "\"measured_iterations\":" ++ toString record.measuredIterations,
    "\"total_nanos\":" ++ toString record.totalNanos,
    "\"average_nanos\":" ++ toString record.averageNanos,
    "\"checksum\":" ++ toString record.checksum
  ] ++ "}"

/-- Render all benchmark records as JSONL. -/
def renderJsonl (records : Array BenchRecord) : String :=
  String.intercalate "\n" (records.toList.map BenchRecord.toJsonLine) ++ "\n"

/-- Produce a string of spaces for Markdown table padding. -/
def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

/-- Produce a string of dashes for Markdown table separators. -/
def dashes (n : Nat) : String :=
  String.ofList (List.replicate n '-')

/-- Right-pad a string to a target display width. -/
def padRight (s : String) (width : Nat) : String :=
  s ++ spaces (width - s.length)

/-- Left-pad a string to a target display width. -/
def padLeft (s : String) (width : Nat) : String :=
  spaces (width - s.length) ++ s

/-- Columns rendered in each grouped benchmark result table. -/
def resultColumns : List (String × Bool × (BenchRecord → String)) := [
  ("Name", false, fun r => r.name),
  ("Iterations", true, fun r => toString r.measuredIterations),
  ("Total ns", true, fun r => toString r.totalNanos),
  ("Avg ns", true, fun r => toString r.averageNanos),
  ("Checksum", true, fun r => toString r.checksum)
]

/-- Compute the Markdown width required for a result table column. -/
def columnWidth (records : List BenchRecord)
    (column : String × Bool × (BenchRecord → String)) : Nat :=
  records.foldl (fun width record => max width (column.2.2 record).length) column.1.length

/-- Pad one Markdown table cell according to its alignment. -/
def formatCell (alignRight : Bool) (width : Nat) (s : String) : String :=
  if alignRight then padLeft s width else padRight s width

/-- Pad a list of Markdown table cells. -/
def formatCells : List String → List Nat → List Bool → List String
  | cell :: cells, width :: widths, alignRight :: alignRights =>
      formatCell alignRight width cell :: formatCells cells widths alignRights
  | _, _, _ => []

/-- Render one Markdown table row. -/
def markdownRow (cells : List String) (widths : List Nat)
    (alignRights : List Bool) : String :=
  "| " ++ String.intercalate " | " (formatCells cells widths alignRights) ++ " |"

/-- Render one Markdown table separator cell. -/
def markdownSeparatorCell (alignRight : Bool) (width : Nat) : String :=
  if alignRight then dashes ((max width 4) - 1) ++ ":" else dashes (max width 3)

/-- Render a Markdown table for benchmark results. -/
def renderMarkdownTable (columns : List (String × Bool × (BenchRecord → String)))
    (records : List BenchRecord) : List String :=
  let widths := columns.map (columnWidth records)
  let headers := columns.map (fun column => column.1)
  let alignRights := columns.map (fun column => column.2.1)
  let separator := columns.mapIdx
    (fun i column => markdownSeparatorCell column.2.1 (widths.getD i 3))
  let rows := records.map fun record =>
    markdownRow (columns.map (fun column => column.2.2 record)) widths alignRights
  markdownRow headers widths (columns.map (fun _ => false)) :: markdownRow separator widths
    (columns.map (fun _ => false)) :: rows

/-- Return the shared checksum for a group if all rows have the same checksum. -/
def matchingChecksum? (records : List BenchRecord) : Option Nat :=
  match records with
  | [] => none
  | record :: records =>
      if records.all (fun other => other.checksum == record.checksum) then
        some record.checksum
      else
        none

/-- Render a short checksum status line for a benchmark group. -/
def renderChecksumStatus (records : List BenchRecord) : String :=
  match matchingChecksum? records with
  | some checksum => "- Expected matching checksum: `" ++ toString checksum ++ "`"
  | none => "- Expected matching checksum: `mismatch detected`"

/-- Render one benchmark group result table. -/
def renderGroupResults (group : BenchGroup) : List String :=
  let records := group.records.toList
  [
    "### " ++ group.title,
    "",
    "- Group key: `" ++ group.groupKey ++ "`",
    renderChecksumStatus records,
    ""
  ] ++ renderMarkdownTable resultColumns records ++ [""]

/-- Render detailed configuration lines for one benchmark record. -/
def renderConfigSection (record : BenchRecord) : List String := [
  "### " ++ record.name,
  "",
  "- Representation: `" ++ record.representation ++ "`",
  "- Method: `" ++ record.method ++ "`",
  "- Field / configuration: `" ++ record.field ++ "`",
  "- Input shape: " ++ record.inputShape,
  "- Warmup iterations: `" ++ toString record.warmupIterations ++ "`",
  ""
]

/-- Render the runner OS and architecture line. -/
def renderRunnerLine (hardware : RunnerHardware) : String :=
  match hardware.runnerOs, hardware.runnerArch with
  | some os, some arch => "- Runner: `" ++ os ++ " " ++ arch ++ "`"
  | some os, none => "- Runner OS: `" ++ os ++ "`"
  | none, some arch => "- Runner architecture: `" ++ arch ++ "`"
  | none, none => "- Runner: unavailable outside GitHub Actions"

/-- Render an optional hardware metadata line. -/
def renderOptionalLine (label : String) (value : Option String) : Option String :=
  value.map fun value => "- " ++ label ++ ": `" ++ value ++ "`"

/-- Render CPU topology metadata when enough fields are available. -/
def renderTopologyLine (hardware : RunnerHardware) : Option String :=
  match hardware.coresPerSocket, hardware.threadsPerCore, hardware.sockets with
  | some cores, some threads, some sockets =>
      some <| "- Topology: `" ++ cores ++ " cores per socket, " ++ threads ++
        " threads per core, " ++ sockets ++ " socket(s)`"
  | some cores, some threads, none =>
      some <| "- Topology: `" ++ cores ++ " cores per socket, " ++ threads ++
        " threads per core`"
  | some cores, none, _ => some <| "- Cores per socket: `" ++ cores ++ "`"
  | none, some threads, _ => some <| "- Threads per core: `" ++ threads ++ "`"
  | none, none, some sockets => some <| "- Sockets: `" ++ sockets ++ "`"
  | none, none, none => none

/-- Drop missing optional lines while preserving present ones. -/
def keepSome : List (Option String) → List String
  | [] => []
  | some line :: lines => line :: keepSome lines
  | none :: lines => keepSome lines

/-- Render the hardware section of the Markdown report. -/
def renderHardwareSection (hardware : RunnerHardware) : List String :=
  [
    "## Runner Hardware",
    "",
    renderRunnerLine hardware,
  ] ++ keepSome [
    renderOptionalLine "CPU" hardware.cpuModel,
    renderOptionalLine "Exposed CPUs"
      (hardware.logicalCpus.map fun cpus => cpus ++ " logical CPUs"),
    renderTopologyLine hardware,
    renderOptionalLine "RAM" hardware.ramTotal,
    renderOptionalLine "Root disk" hardware.rootDisk,
    renderOptionalLine "Hypervisor" hardware.hypervisor
  ] ++ [
    ""
  ]

/-- Render the complete Markdown benchmark report. -/
def renderMarkdown (hardware : RunnerHardware) (groups : Array BenchGroup) : String :=
  let records := flattenGroups groups
  String.intercalate "\n" ([
    "# Evaluation Benchmark Report",
    "",
    "- Seed: `" ++ toString seed ++ "`",
    "- Early CI performance comparisons are informational only.",
    "",
  ] ++ renderHardwareSection hardware ++ [
    "## Results",
    ""
  ] ++ (groups.toList.map renderGroupResults).foldr List.append [] ++ [
    "## Benchmark Configuration",
    ""
  ] ++ (records.toList.map renderConfigSection).foldr List.append []) ++ "\n"

end CompPolyBench
