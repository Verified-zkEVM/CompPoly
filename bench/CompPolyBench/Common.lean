/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import Init.Data.Random
import Lean.Data.Json.Parser
import Std.Time
import CompPoly.Fields.KoalaBear
import CompPoly.Fields.Binary.AdditiveNTT.Impl
import CompPoly.Fields.Goldilocks
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

/-- Benchmark preset controlling warmup and measured iteration counts. -/
inductive BenchPreset where
  | small
  | medium
  | large
deriving BEq

/-- Lowercase CLI/report label for a benchmark preset. -/
def BenchPreset.name : BenchPreset → String
  | BenchPreset.small => "small"
  | BenchPreset.medium => "medium"
  | BenchPreset.large => "large"

/-- Return the precomputed value for the active benchmark preset. -/
def BenchPreset.selectNat (preset : BenchPreset) (large medium small : Nat) : Nat :=
  match preset with
  | BenchPreset.large => large
  | BenchPreset.medium => medium
  | BenchPreset.small => small

/-- Warmup iteration count for ordinary evaluation benchmarks. -/
def warmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 100 10 0

/-- Measured iteration count for ordinary evaluation benchmarks. -/
def measuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 5000 700 150

/-- Warmup iteration count for batch-evaluation benchmarks over the base input shape. -/
def batchWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 0

/-- Measured iteration count for batch-evaluation benchmarks over the base input shape. -/
def batchMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 5 1 1

/-- Warmup iteration count for batch-evaluation benchmarks over the medium input shape. -/
def mediumBatchWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 0

/-- Measured iteration count for batch-evaluation benchmarks over the medium input shape. -/
def mediumBatchMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 10 1 1

/-- Warmup iteration count for batch-evaluation benchmarks over the large input shape. -/
def largeBatchWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 0

/-- Measured iteration count for batch-evaluation benchmarks over the large input shape. -/
def largeBatchMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 10 1 1

/-- Warmup iteration count for direct monic-remainder benchmarks. -/
def modWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 0

/-- Measured iteration count for direct monic-remainder benchmarks. -/
def modMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 20 3 1

/-- Warmup iteration count for direct monic-remainder benchmarks over the medium input shape. -/
def mediumModWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 0

/-- Measured iteration count for direct monic-remainder benchmarks over the medium input shape. -/
def mediumModMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 5 1 1

/-- Warmup iteration count for direct univariate multiplication benchmarks. -/
def mulWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1 1 0

/-- Measured iteration count for direct univariate multiplication benchmarks. -/
def mulMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 20 3 1

/-- Warmup iteration count for the base additive NTT benchmark. -/
def additiveNttWarmupIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 10 1 0

/-- Measured iteration count for the base additive NTT benchmark. -/
def additiveNttMeasuredIterations (preset : BenchPreset) : Nat :=
  preset.selectNat 1000 150 30

/-- Primality witness used for generic `ZMod` benchmarks over `KoalaBear`. -/
instance : Fact (Nat.Prime KoalaBear.fieldSize) where
  out := KoalaBear.is_prime

/-- Primality witness used for generic `ZMod` benchmarks over `Goldilocks`. -/
instance : Fact (Nat.Prime Goldilocks.fieldSize) where
  out := Goldilocks.is_prime

/-- Result row emitted by one timed benchmark case. -/
structure BenchRecord where
  name : String
  representation : String
  method : String
  preset : String
  field : String
  inputShape : String
  warmupIterations : Nat
  checksumIterations : Nat
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
  runTask : BenchPreset → BenchSelection → StdGen → IO (Array BenchGroup × StdGen)

/-- Decide whether a group key should run under a selection. -/
def BenchSelection.selects : BenchSelection → String → Bool
  | BenchSelection.all, _ => true
  | BenchSelection.only keys, key => keys.any fun selected ↦ selected == key

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
      tasks.filter fun task ↦
        selection.selectsAny (task.infos.map fun info ↦ info.groupKey)

/-- Build one registry task from metadata and a single-group runner. -/
def BenchTask.fromGroupRunner (info : BenchGroupInfo)
    (runGroup : BenchPreset → StdGen → IO (BenchGroup × StdGen)) : BenchTask where
  infos := [info]
  runTask := fun preset _ gen ↦ do
    let (group, gen) ← runGroup preset gen
    pure (#[group], gen)

/-- Total measured runtime across all benchmark records in a group. -/
def totalGroupNanos (records : List BenchRecord) : Nat :=
  records.foldl (fun acc record ↦ acc + record.totalNanos) 0

/-- Human-readable time units for benchmark reports. -/
inductive TimeUnit where
  | ns
  | us
  | ms
  | s

/-- Unit label used in Markdown and CLI output. -/
def TimeUnit.label : TimeUnit → String
  | TimeUnit.ns => "ns"
  | TimeUnit.us => "us"
  | TimeUnit.ms => "ms"
  | TimeUnit.s => "s"

/-- Number of nanoseconds represented by one unit. -/
def TimeUnit.divisor : TimeUnit → Nat
  | TimeUnit.ns => 1
  | TimeUnit.us => 1000
  | TimeUnit.ms => 1000000
  | TimeUnit.s => 1000000000

/-- Select the largest readable unit that keeps the largest value at least one unit. -/
def chooseTimeUnit (values : List Nat) : TimeUnit :=
  let largest := values.foldl Nat.max 0
  if largest >= TimeUnit.s.divisor then
    TimeUnit.s
  else if largest >= TimeUnit.ms.divisor then
    TimeUnit.ms
  else if largest >= TimeUnit.us.divisor then
    TimeUnit.us
  else
    TimeUnit.ns

/-- Render a fractional part rounded to two decimal places, dropping trailing zeroes. -/
def renderCentiFraction (centi : Nat) : String :=
  if centi = 0 then
    ""
  else if centi % 10 = 0 then
    "." ++ toString (centi / 10)
  else
    "." ++ (if centi < 10 then "0" else "") ++ toString centi

/-- Render a nanosecond duration in a fixed unit, rounded to at most two decimals. -/
def formatNanosInUnit (unit : TimeUnit) (nanos : Nat) : String :=
  match unit with
  | TimeUnit.ns => toString nanos
  | _ =>
      let divisor := unit.divisor
      let scaled := (nanos * 100 + divisor / 2) / divisor
      if nanos != 0 && scaled = 0 then
        "<0.01"
      else
        toString (scaled / 100) ++ renderCentiFraction (scaled % 100)

/-- Render a nanosecond duration with an explicit fixed unit label. -/
def formatNanosWithUnit (unit : TimeUnit) (nanos : Nat) : String :=
  formatNanosInUnit unit nanos ++ " " ++ unit.label

/-- Render one nanosecond duration using the best unit for that single value. -/
def formatNanosAuto (nanos : Nat) : String :=
  let unit := chooseTimeUnit [nanos]
  formatNanosWithUnit unit nanos

/-- Run selected tasks from a registry and concatenate their emitted groups. -/
def runSelectedTasks (tasks : List BenchTask) (preset : BenchPreset) (selection : BenchSelection)
    (gen : StdGen) : IO (Array BenchGroup × StdGen) := do
  let mut gen := gen
  let mut groups := #[]
  for task in selection.filterTasks tasks do
    let (taskGroups, nextGen) ← task.runTask preset selection gen
    gen := nextGen
    for group in taskGroups do
      let groupTotal := totalGroupNanos group.records.toList
      IO.println s!"finished {group.groupKey} in {formatNanosAuto groupTotal}"
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
  "bench" / ("results-" ++ runId ++ ".jsonl")

/-- Path for the generated Markdown benchmark report. -/
def reportPath (runId : String) : System.FilePath :=
  "bench" / ("report-" ++ runId ++ ".md")

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
  (s.replace "\t" " ").splitOn " " |>.filter fun field ↦ !field.isEmpty

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
    cpuModel := lscpu.bind fun output ↦ lscpuJsonField output "Model name:"
    logicalCpus := nproc.orElse fun _ ↦ lscpu.bind fun output ↦ lscpuJsonField output "CPU(s):"
    coresPerSocket := lscpu.bind fun output ↦ lscpuJsonField output "Core(s) per socket:"
    threadsPerCore := lscpu.bind fun output ↦ lscpuJsonField output "Thread(s) per core:"
    sockets := lscpu.bind fun output ↦ lscpuJsonField output "Socket(s):"
    ramTotal := meminfo.bind memTotalGib
    rootDisk := dfRoot.bind dfRootSize
    hypervisor := lscpu.bind fun output ↦ lscpuJsonField output "Hypervisor vendor:"
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

/-- Generate KoalaBear coefficients with the same shape controls as `zmodArray`. -/
def koalaBearArray (size : Nat) (sparse : Bool) : StateM StdGen (Array KoalaBear.Field) := do
  zmodArray KoalaBear.fieldSize size sparse

/-- Convert KoalaBear field inputs to the native-word KoalaBear representation. -/
def koalaBearFastArray (xs : Array KoalaBear.Field) : Array KoalaBear.Fast.Field :=
  xs.map KoalaBear.Fast.ofField

/-- Generate KoalaBear coefficients with a nonzero every `sparseStride` entries. -/
def koalaBearArrayWithStride (size sparseStride : Nat) :
    StateM StdGen (Array KoalaBear.Field) := do
  zmodArrayWithStride KoalaBear.fieldSize size sparseStride

/-- Generate KoalaBear vectors for multilinear benchmark inputs. -/
def koalaBearVector (size : Nat) (sparse : Bool) : StateM StdGen (Array KoalaBear.Field) :=
  koalaBearArray size sparse

/-- Generate dense KoalaBear evaluation points. -/
def koalaBearPoints (size : Nat) : StateM StdGen (Array KoalaBear.Field) :=
  koalaBearArray size false

/-- Build a canonical computable polynomial from generated coefficients. -/
def cpolyOfArray {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (coeffs : Array R) : CPolynomial R :=
  CPolynomial.ofArray coeffs

/-- Build a monic divisor as a product of linear factors `X - C x`. -/
def monicDivisorFromPoints {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (xs : Array R) : CPolynomial R :=
  xs.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) (CPolynomial.C 1)

/-- Mix one benchmark output value into a stable checksum accumulator. -/
def mixChecksum (acc value : Nat) : Nat :=
  (acc * 16777619 + value + 97) % 18446744073709551557

/-- Convert a KoalaBear field element to a checksum word. -/
def checksumKoalaBear (x : KoalaBear.Field) : Nat :=
  ZMod.val x

/-- Convert a fast KoalaBear element to a checksum word. -/
def checksumKoalaBearFast (x : KoalaBear.Fast.Field) : Nat :=
  KoalaBear.Fast.toNat x

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
  xs.foldl (fun acc x ↦ mixChecksum acc (checksum x)) 0

/-- Checksum a canonical univariate polynomial by its coefficient array. -/
def checksumCPolynomial [Zero α] (checksum : α → Nat) (p : CPolynomial α) : Nat :=
  checksumArray checksum p.val

/-- Checksum a raw univariate polynomial by its stored coefficient array. -/
def checksumRawPolynomial (checksum : α → Nat) (p : CPolynomial.Raw α) : Nat :=
  checksumArray checksum p

/-- Compute the checksum iteration count shared by a benchmark group. -/
def groupChecksumIterations (first : Nat) (rest : List Nat) : Nat :=
  rest.foldl Nat.min first

/--
Time one benchmark closure and package its metadata and checksum.

The checksum is computed before timing over `checksumIterations`, the minimum
measured-iteration count used by the records in the surrounding benchmark group.
The timed loop consumes each result so implementations with different iteration
counts remain comparable within the same group.
-/
def runTimed (name representation method field inputShape : String) (preset : BenchPreset)
    (warmup measured : Nat) (run : Nat → α) (checksum : α → Nat)
    (checksumIterations : Nat := measured) : IO BenchRecord := do
  for i in [0:warmup] do
    let _ := run i
    pure ()
  let mut validationChecksum := 0
  for i in [0:checksumIterations] do
    validationChecksum := mixChecksum validationChecksum (checksum (run i))
  let start ← IO.monoNanosNow
  let mut timingChecksum := 0
  for i in [0:measured] do
    timingChecksum := mixChecksum timingChecksum (checksum (run i))
  let stop ← IO.monoNanosNow
  let _ := timingChecksum
  let total := stop - start
  pure {
    name := name
    representation := representation
    method := method
    preset := preset.name
    field := field
    inputShape := inputShape
    warmupIterations := warmup
    checksumIterations := checksumIterations
    measuredIterations := measured
    totalNanos := total
    averageNanos := if measured = 0 then 0 else total / measured
    checksum := validationChecksum
  }

/-- Append benchmark records from `ys` onto `xs`. -/
def appendRecords (xs ys : Array BenchRecord) : Array BenchRecord :=
  ys.foldl (init := xs) fun acc record ↦ acc.push record

/-- Append benchmark groups from `ys` onto `xs`. -/
def appendGroups (xs ys : Array BenchGroup) : Array BenchGroup :=
  ys.foldl (init := xs) fun acc group ↦ acc.push group

/-- Flatten grouped benchmark records for JSONL output. -/
def flattenGroups (groups : Array BenchGroup) : Array BenchRecord :=
  groups.foldl (init := #[]) fun acc group ↦ appendRecords acc group.records

/-- Render a benchmark string field as a JSON string. -/
def jsonString (s : String) : String :=
  "\"" ++ s ++ "\""

/-- Render one benchmark record as a JSONL row. -/
def BenchRecord.toJsonLine (record : BenchRecord) : String :=
  "{" ++ String.intercalate "," [
    "\"name\":" ++ jsonString record.name,
    "\"representation\":" ++ jsonString record.representation,
    "\"method\":" ++ jsonString record.method,
    "\"preset\":" ++ jsonString record.preset,
    "\"field\":" ++ jsonString record.field,
    "\"input_shape\":" ++ jsonString record.inputShape,
    "\"warmup_iterations\":" ++ toString record.warmupIterations,
    "\"checksum_iterations\":" ++ toString record.checksumIterations,
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

/-- Drop missing optional lines while preserving present ones. -/
def keepSome : List (Option String) → List String
  | [] => []
  | some line :: lines => line :: keepSome lines
  | none :: lines => keepSome lines

/-- Compute the Markdown width required for a result table column. -/
def columnWidth (records : List BenchRecord)
    (column : String × Bool × (BenchRecord → String)) : Nat :=
  records.foldl (fun width record ↦ max width (column.2.2 record).length) column.1.length

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
  let headers := columns.map (fun column ↦ column.1)
  let alignRights := columns.map (fun column ↦ column.2.1)
  let separator := columns.mapIdx
    (fun i column ↦ markdownSeparatorCell column.2.1 (widths.getD i 3))
  let rows := records.map fun record ↦
    markdownRow (columns.map (fun column ↦ column.2.2 record)) widths alignRights
  markdownRow headers widths (columns.map (fun _ ↦ false)) :: markdownRow separator widths
    (columns.map (fun _ ↦ false)) :: rows

/-- Return the shared checksum for a group if all rows have the same checksum. -/
def matchingChecksum? (records : List BenchRecord) : Option Nat :=
  match records with
  | [] => none
  | record :: records =>
      if records.all (fun other ↦
          other.checksumIterations == record.checksumIterations &&
            other.checksum == record.checksum) then
        some record.checksum
      else
        none

/-- Return a shared string field for a group if all rows agree. -/
def matchingString? (records : List BenchRecord) (field : BenchRecord → String) : Option String :=
  match records with
  | [] => none
  | record :: records =>
      let value := field record
      if records.all (fun other ↦ field other == value) then
        some value
      else
        none

/-- Return a shared natural-number field for a group if all rows agree. -/
def matchingNat? (records : List BenchRecord) (field : BenchRecord → Nat) : Option Nat :=
  match records with
  | [] => none
  | record :: records =>
      let value := field record
      if records.all (fun other ↦ field other == value) then
        some value
      else
        none

/-- Render a shared string metadata line for a benchmark group. -/
def renderSharedStringLine (label : String) (records : List BenchRecord)
    (field : BenchRecord → String) : Option String :=
  (matchingString? records field).map fun value ↦ "- " ++ label ++ ": `" ++ value ++ "`"

/-- Render a shared natural-number metadata line for a benchmark group. -/
def renderSharedNatLine (label : String) (records : List BenchRecord)
    (field : BenchRecord → Nat) : Option String :=
  (matchingNat? records field).map fun value ↦ "- " ++ label ++ ": `" ++ toString value ++ "`"

/-- Render a short checksum status line for a benchmark group. -/
def renderChecksumStatus (records : List BenchRecord) : String :=
  match matchingChecksum? records with
  | some checksum => "- Checksum: `" ++ toString checksum ++ "`"
  | none => "- Checksum: **ERROR: mismatch detected**"

/-- Return benchmark groups whose rows do not have a shared checksum. -/
def checksumMismatchGroups (groups : Array BenchGroup) : List BenchGroup :=
  groups.toList.filter fun group ↦ (matchingChecksum? group.records.toList).isNone

/-- Lookup a rendered implementation label by exact benchmark metadata. -/
def lookupImplementationLabel? : String → List (String × String) → Option String
  | _, [] => none
  | key, (source, label) :: labels =>
      if key == source then some label else lookupImplementationLabel? key labels

/-- Human-readable implementation labels keyed by benchmark record name. -/
def implementationNameLabels : List (String × String) := [
  ("univariate-mul-naive", "Naive"),
  ("univariate-mul-ntt", "NTT"),
  ("univariate-mul-ntt-fast", "Fast NTT"),
  ("univariate-mul-ntt-fast-plan", "Fast NTT with cached plan"),
  ("univariate-mul-naive-fast", "Naive"),
  ("univariate-mul-ntt-koalabear-fast", "NTT"),
  ("univariate-mul-ntt-fast-koalabear-fast", "Fast NTT"),
  ("univariate-mul-ntt-fast-plan-fast", "Fast NTT with cached plan"),
  ("univariate-mul-naive-koalabear", "Naive"),
  ("univariate-mul-ntt-koalabear", "NTT"),
  ("univariate-mul-ntt-fast-koalabear", "Fast NTT"),
  ("univariate-mul-ntt-fast-plan-koalabear", "Fast NTT with cached plan"),
  ("guruswami-sudan-root-roth", "Roth-Ruckenstein root finding"),
  ("guruswami-sudan-root-roth-nttfast",
    "Roth-Ruckenstein root finding (fast mul/mod)"),
  ("guruswami-sudan-root-roth-fast",
    "Roth-Ruckenstein root finding (fast KoalaBear)"),
  ("guruswami-sudan-root-roth-fast-nttfast",
    "Roth-Ruckenstein root finding (fast mul/mod, fast KoalaBear)"),
  ("guruswami-sudan-core-dense-roth", "Dense interpolation plus root finding"),
  ("guruswami-sudan-core-dense-roth-nttfast",
    "Dense interpolation plus root finding (fast mul/mod)"),
  ("guruswami-sudan-core-dense-roth-fast",
    "Dense interpolation plus root finding (fast KoalaBear)"),
  ("guruswami-sudan-core-dense-roth-fast-nttfast",
    "Dense interpolation plus root finding (fast mul/mod, fast KoalaBear)"),
  ("additive-ntt-btf3", "Reference implementation"),
  ("additive-ntt-btf3-fast", "Fast implementation"),
  ("additive-ntt-btf3-l4-r2", "Reference implementation"),
  ("additive-ntt-btf3-l4-r2-fast", "Fast implementation"),
  ("additive-ntt-btf4-l7-r2-fast", "Fast implementation")
]

/-- Human-readable implementation labels keyed by benchmark method. -/
def implementationMethodLabels : List (String × String) := [
  ("eval sum-of-powers", "Sum of powers"),
  ("evalHorner", "Horner"),
  ("eval", "Direct evaluation"),
  ("evalMle", "Multilinear extension"),
  ("evalManyMle", "Iterated direct evaluation"),
  ("evalManyMleByLayers", "Evaluation by layers"),
  ("evalManyHorner", "Horner"),
  ("evalManySharedPowers", "Shared powers"),
  ("evalEval", "Direct evaluation"),
  ("evalEvalHornerYThenX", "Horner in Y, then in X"),
  ("evalEvalHornerXThenY", "Horner in X, then in Y"),
  ("evalBatch", "Batch sum of powers"),
  ("evalBatchHorner", "Batch Horner"),
  ("evalBatchSubproduct naive mul/mod", "Subproduct tree, naive mul/mod"),
  ("evalBatchSubproduct naive mul/remainder-only mod",
    "Subproduct tree, naive mul/remainder-only"),
  ("evalBatchSubproduct ntt mul/remainder-only mod",
    "Subproduct tree, NTT mul/remainder-only"),
  ("evalBatchSubproduct ntt-fast mul/remainder-only mod",
    "Subproduct tree, fast NTT mul/remainder-only"),
  ("evalBatchSubproduct naive mul/reversal-convolution-low mod",
    "Subproduct tree, naive mul/reversal convolution"),
  ("evalBatchSubproduct ntt mul/reversal-ntt-low mod",
    "Subproduct tree, NTT mul/reversal low product"),
  ("evalBatchSubproduct ntt-fast mul/reversal-ntt-fast-low mod",
    "Subproduct tree, fast NTT mul/reversal low product"),
  ("mul", "Naive"),
  ("modByMonic", "Long division"),
  ("modByMonicRemainderOnly", "Remainder-only division"),
  ("modByMonicByReversal, MulLowContext.convolution",
    "Reversal with convolution low product"),
  ("modByMonicByReversal, FastMulLow.withFallback",
    "Reversal with NTT low product"),
  ("modByMonicByReversal, NTTFast.FastMulLow.withFallback",
    "Reversal with fast NTT low product"),
  ("MulLowContext.naive", "Naive"),
  ("MulLowContext.convolution", "Convolution"),
  ("FastMulLow.withFallback", "NTT with fallback"),
  ("NTTFast.FastMulLow.withFallback", "Fast NTT with fallback"),
  ("computableAdditiveNTT", "Reference implementation"),
  ("computableAdditiveNTTFast", "Fast implementation")
]

/-- Render the implementation label shown in result tables. -/
def implementationLabel (record : BenchRecord) : String :=
  match lookupImplementationLabel? record.name implementationNameLabels with
  | some label => label
  | none =>
      match lookupImplementationLabel? record.method implementationMethodLabels with
      | some label => label
      | none => record.method

/-- Record-specific implementation names whose labels already include the field variant. -/
def implementationNamesWithField : List String := [
  "guruswami-sudan-root-roth-fast",
  "guruswami-sudan-root-roth-fast-nttfast",
  "guruswami-sudan-core-dense-roth-fast",
  "guruswami-sudan-core-dense-roth-fast-nttfast",
  "guruswami-sudan-filtered-core-fast",
  "guruswami-sudan-filtered-core-fast-nttfast"
]

/-- Whether a record-specific implementation label already includes the field variant. -/
def implementationLabelIncludesField (record : BenchRecord) : Bool :=
  implementationNamesWithField.contains record.name

/-- Implementation label that includes the field only when rows mix field representations. -/
def implementationLabelInGroup (records : List BenchRecord) (record : BenchRecord) : String :=
  let label := implementationLabel record
  if (matchingString? records fun r ↦ r.field).isSome then
    label
  else if record.field == "KoalaBear.Field" then
    label
  else if implementationLabelIncludesField record then
    label
  else if record.field == "KoalaBear.Fast.Field" then
    label ++ " (fast KoalaBear)"
  else
    label ++ " (" ++ record.field ++ ")"

/-- Columns rendered in a group result table after shared metadata is lifted out. -/
def groupResultColumns (records : List BenchRecord) (totalUnit avgUnit : TimeUnit) :
    List (String × Bool × (BenchRecord → String)) :=
  [
    ("Implementation", false, implementationLabelInGroup records),
    ("Iterations", true, fun r ↦ toString r.measuredIterations),
    ("Total (" ++ totalUnit.label ++ ")", true, fun r ↦
      formatNanosInUnit totalUnit r.totalNanos),
    ("Avg (" ++ avgUnit.label ++ ")", true, fun r ↦
      formatNanosInUnit avgUnit r.averageNanos)
  ]

/-- Shared metadata rendered before each benchmark group result table. -/
def renderGroupMetadata (records : List BenchRecord) (totalUnit : TimeUnit) : List String :=
  keepSome [
    renderSharedStringLine "Representation" records (fun r ↦ r.representation),
    renderSharedStringLine "Field / configuration" records (fun r ↦ r.field),
    renderSharedStringLine "Input shape" records (fun r ↦ r.inputShape),
    renderSharedNatLine "Warmup iterations" records (fun r ↦ r.warmupIterations),
    renderSharedNatLine "Checksum iterations" records (fun r ↦ r.checksumIterations)
  ] ++ [
    "- Total group time: `" ++ formatNanosWithUnit totalUnit (totalGroupNanos records) ++
      "`",
    renderChecksumStatus records
  ]

/-- Render one benchmark group result table. -/
def renderGroupResults (group : BenchGroup) : List String :=
  let records := group.records.toList
  let groupTotal := totalGroupNanos records
  let totalUnit := chooseTimeUnit (groupTotal :: records.map fun r ↦ r.totalNanos)
  let avgUnit := chooseTimeUnit (records.map fun r ↦ r.averageNanos)
  [
    "### " ++ group.title,
    "",
    "- Group key: `" ++ group.groupKey ++ "`",
  ] ++ renderGroupMetadata records totalUnit ++ [""] ++
    renderMarkdownTable (groupResultColumns records totalUnit avgUnit) records ++ [""]

/-- Render the runner OS and architecture line. -/
def renderRunnerLine (hardware : RunnerHardware) : String :=
  match hardware.runnerOs, hardware.runnerArch with
  | some os, some arch => "- Runner: `" ++ os ++ " " ++ arch ++ "`"
  | some os, none => "- Runner OS: `" ++ os ++ "`"
  | none, some arch => "- Runner architecture: `" ++ arch ++ "`"
  | none, none => "- Runner: unavailable outside GitHub Actions"

/-- Render an optional hardware metadata line. -/
def renderOptionalLine (label : String) (value : Option String) : Option String :=
  value.map fun value ↦ "- " ++ label ++ ": `" ++ value ++ "`"

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

/-- Render the hardware section of the Markdown report. -/
def renderHardwareSection (hardware : RunnerHardware) : List String :=
  [
    "## Runner Hardware",
    "",
    renderRunnerLine hardware,
  ] ++ keepSome [
    renderOptionalLine "CPU" hardware.cpuModel,
    renderOptionalLine "Exposed CPUs"
      (hardware.logicalCpus.map fun cpus ↦ cpus ++ " logical CPUs"),
    renderTopologyLine hardware,
    renderOptionalLine "RAM" hardware.ramTotal,
    renderOptionalLine "Root disk" hardware.rootDisk,
    renderOptionalLine "Hypervisor" hardware.hypervisor
  ] ++ [
    ""
  ]

/-- Render the complete Markdown benchmark report. -/
def renderMarkdown (hardware : RunnerHardware) (preset : BenchPreset) (groups : Array BenchGroup) :
    String :=
  String.intercalate "\n" ([
    "# Evaluation Benchmark Report",
    "",
    "- Seed: `" ++ toString seed ++ "`",
    "- Preset: `" ++ preset.name ++ "`",
    "- Benchmark timings are informational and depend on runner hardware.",
    "",
  ] ++ renderHardwareSection hardware ++ [
    "## Results",
    ""
  ] ++ (groups.toList.map renderGroupResults).foldr List.append []) ++ "\n"

end CompPolyBench
