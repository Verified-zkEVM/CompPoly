import Init.Data.Random
import Std.Time
import CompPoly.Bivariate.Basic
import CompPoly.Fields.BabyBear
import CompPoly.Fields.Binary.AdditiveNTT.Impl
import CompPoly.Fields.BN254
import CompPoly.Fields.Goldilocks
import CompPoly.Multilinear.Basic
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Univariate.Raw.Ops

open CompPoly
open ConcreteBinaryTower

namespace CompPolyBench

private def seed : Nat := 20260504
private def warmupIterations : Nat := 100
private def measuredIterations : Nat := 5000
private def additiveNTTWarmupIterations : Nat := 10
private def additiveNTTMeasuredIterations : Nat := 100

instance : Fact (Nat.Prime BabyBear.fieldSize) := ⟨BabyBear.is_prime⟩
instance : Fact (Nat.Prime Goldilocks.fieldSize) := ⟨Goldilocks.is_prime⟩

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

private def makeRunId : IO String := do
  let started ← Std.Time.ZonedDateTime.now
  pure <| started.format "yyMMdd-HHmmss"

private def resultsPath (runId : String) : System.FilePath :=
  "bench" / ("evaluation-bench-results-" ++ runId ++ ".jsonl")

private def reportPath (runId : String) : System.FilePath :=
  "bench" / ("evaluation-bench-report-" ++ runId ++ ".md")

private def nextNat (lo hi : Nat) : StateM StdGen Nat := do
  let g ← get
  let (n, g') := randNat g lo hi
  set g'
  pure n

private def randomNatArray (size : Nat) (hi : Nat) : StateM StdGen (Array Nat) := do
  let mut values := #[]
  for _ in [0:size] do
    values := values.push (← nextNat 0 hi)
  pure values

private def zmodArray (p : Nat) (size : Nat) (sparse : Bool) : StateM StdGen (Array (ZMod p)) := do
  let values ← randomNatArray size (p - 1)
  let mut coeffs := #[]
  for i in [0:size] do
    let value : ZMod p :=
      if sparse && i % 4 != 0 then
        0
      else
        (values.getD i 0 : ZMod p)
    coeffs := coeffs.push value
  pure coeffs

private def babyBearArray (size : Nat) (sparse : Bool) : StateM StdGen (Array BabyBear.Field) := do
  zmodArray BabyBear.fieldSize size sparse

private def babyBearVector (size : Nat) (sparse : Bool) : StateM StdGen (Array BabyBear.Field) :=
  babyBearArray size sparse

private def babyBearPoints (size : Nat) : StateM StdGen (Array BabyBear.Field) :=
  babyBearArray size false

private def mixChecksum (acc value : Nat) : Nat :=
  (acc * 16777619 + value + 97) % 18446744073709551557

private def checksumBabyBear (x : BabyBear.Field) : Nat :=
  ZMod.val x

private def checksumZMod {p : Nat} (x : ZMod p) : Nat :=
  ZMod.val x

private def checksumBTF3 (x : AdditiveNTT.BTF₃) : Nat :=
  BitVec.toNat x

private def runTimed (name representation method field inputShape : String)
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

private def jsonString (s : String) : String :=
  "\"" ++ s ++ "\""

private def BenchRecord.toJsonLine (record : BenchRecord) : String :=
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

private def renderJsonl (records : Array BenchRecord) : String :=
  String.intercalate "\n" (records.toList.map BenchRecord.toJsonLine) ++ "\n"

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

private def dashes (n : Nat) : String :=
  String.ofList (List.replicate n '-')

private def padRight (s : String) (width : Nat) : String :=
  s ++ spaces (width - s.length)

private def padLeft (s : String) (width : Nat) : String :=
  spaces (width - s.length) ++ s

private def resultColumns : List (String × Bool × (BenchRecord → String)) := [
  ("Name", false, fun r => r.name),
  ("Iterations", true, fun r => toString r.measuredIterations),
  ("Total ns", true, fun r => toString r.totalNanos),
  ("Avg ns", true, fun r => toString r.averageNanos),
  ("Checksum", true, fun r => toString r.checksum)
]

private def columnWidth (records : List BenchRecord)
    (column : String × Bool × (BenchRecord → String)) : Nat :=
  records.foldl (fun width record => max width (column.2.2 record).length) column.1.length

private def formatCell (alignRight : Bool) (width : Nat) (s : String) : String :=
  if alignRight then padLeft s width else padRight s width

private def formatCells : List String → List Nat → List Bool → List String
  | cell :: cells, width :: widths, alignRight :: alignRights =>
      formatCell alignRight width cell :: formatCells cells widths alignRights
  | _, _, _ => []

private def markdownRow (cells : List String) (widths : List Nat) (alignRights : List Bool) : String :=
  "| " ++ String.intercalate " | " (formatCells cells widths alignRights) ++ " |"

private def markdownSeparatorCell (alignRight : Bool) (width : Nat) : String :=
  if alignRight then dashes ((max width 4) - 1) ++ ":" else dashes (max width 3)

private def renderMarkdownTable (columns : List (String × Bool × (BenchRecord → String)))
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

private def renderConfigSection (record : BenchRecord) : List String := [
  "### " ++ record.name,
  "",
  "- Representation: `" ++ record.representation ++ "`",
  "- Method: `" ++ record.method ++ "`",
  "- Field / configuration: `" ++ record.field ++ "`",
  "- Input shape: " ++ record.inputShape,
  "- Warmup iterations: `" ++ toString record.warmupIterations ++ "`",
  ""
]

private def renderMarkdown (records : Array BenchRecord) : String :=
  String.intercalate "\n" ([
    "# Evaluation Benchmark Report",
    "",
    "- Seed: `" ++ toString seed ++ "`",
    "- Early CI performance comparisons are informational only.",
    "",
    "## Results",
    ""
  ] ++ renderMarkdownTable resultColumns records.toList ++ [
    "",
    "## Benchmark Configuration",
    ""
  ] ++ (records.toList.map renderConfigSection).foldr List.append []) ++ "\n"

private def appendRecords (xs ys : Array BenchRecord) : Array BenchRecord :=
  ys.foldl (init := xs) fun acc record => acc.push record

private def buildCMvPolynomial (terms : Array BabyBear.Field) : CPoly.CMvPolynomial 3 BabyBear.Field :=
  Id.run do
    let mut p : CPoly.CMvPolynomial 3 BabyBear.Field := 0
    for i in [0:terms.size] do
      let m : CPoly.CMvMonomial 3 := Vector.ofFn fun j =>
        (i / (j.val + 1)) % 4
      p := p + CPoly.CMvPolynomial.monomial m (terms.getD i 0)
    pure p

private def buildCBivariate (terms : Array BabyBear.Field) : CBivariate BabyBear.Field :=
  Id.run do
    let mut p : CBivariate BabyBear.Field := 0
    for i in [0:terms.size] do
      let xDegree := i % 8
      let yDegree := i / 8
      p := p + CBivariate.monomialXY xDegree yDegree (terms.getD i 0)
    pure p

private def runDenseUnivariateZMod (p : Nat) [Fact (Nat.Prime p)]
    (nameSuffix fieldName : String) (gen : StdGen) : IO (Array BenchRecord × StdGen) := do
  let (denseCoeffs, gen) := (zmodArray p 512 false).run gen
  let (points, gen) := (zmodArray p 32 false).run gen
  let densePoly : CPolynomial.Raw (ZMod p) := denseCoeffs
  let mut records := #[]
  records := records.push (← runTimed
    ("univariate-dense-sum-" ++ nameSuffix) "CPolynomial.Raw" "eval₂ sum-of-powers" fieldName
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.Raw.eval (points.getD (i % points.size) 0) densePoly)
    checksumZMod)
  records := records.push (← runTimed
    ("univariate-dense-horner-" ++ nameSuffix) "CPolynomial.Raw" "eval₂Horner" fieldName
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.Raw.eval₂Horner (RingHom.id (ZMod p))
      (points.getD (i % points.size) 0) densePoly)
    checksumZMod)
  pure (records, gen)

private def runUnivariate (gen : StdGen) : IO (Array BenchRecord × StdGen) := do
  let (denseCoeffs, gen) := (babyBearArray 512 false).run gen
  let (sparseCoeffs, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 32).run gen
  let densePoly : CPolynomial.Raw BabyBear.Field := denseCoeffs
  let sparsePoly : CPolynomial.Raw BabyBear.Field := sparseCoeffs
  let nextGen := gen
  let mut records := #[]
  records := records.push (← runTimed
    "univariate-dense-sum" "CPolynomial.Raw" "eval₂ sum-of-powers" "BabyBear.Field"
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.Raw.eval (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear)
  records := records.push (← runTimed
    "univariate-dense-horner" "CPolynomial.Raw" "eval₂Horner" "BabyBear.Field"
    "degree<512, dense, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.Raw.eval₂Horner (RingHom.id BabyBear.Field)
      (points.getD (i % points.size) 0) densePoly)
    checksumBabyBear)
  records := records.push (← runTimed
    "univariate-sparse-sum" "CPolynomial.Raw" "eval₂ sum-of-powers" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.Raw.eval (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear)
  records := records.push (← runTimed
    "univariate-sparse-horner" "CPolynomial.Raw" "eval₂Horner" "BabyBear.Field"
    "degree<512, one nonzero per 4 coeffs, 32 points" warmupIterations measuredIterations
    (fun i => CPolynomial.Raw.eval₂Horner (RingHom.id BabyBear.Field)
      (points.getD (i % points.size) 0) sparsePoly)
    checksumBabyBear)
  let (goldilocksRecords, extraGen) ← runDenseUnivariateZMod
    Goldilocks.fieldSize "goldilocks" "Goldilocks.Field" nextGen
  records := appendRecords records goldilocksRecords
  let (bn254Records, _) ← runDenseUnivariateZMod
    BN254.scalarFieldSize "bn254" "BN254.ScalarField" extraGen
  records := appendRecords records bn254Records
  pure (records, nextGen)

private def runMultivariate (gen : StdGen) : IO (Array BenchRecord × StdGen) := do
  let (terms, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 96).run gen
  let p := buildCMvPolynomial terms
  let evalPoint (offset : Nat) : Fin 3 → BabyBear.Field :=
    fun j => points.getD ((offset + j.val) % points.size) 0
  let record ← runTimed
    "multivariate-eval" "CMvPolynomial" "eval" "BabyBear.Field"
    "3 vars, 512 generated terms, sparse coeffs, 32 points" warmupIterations measuredIterations
    (fun i => CPoly.CMvPolynomial.eval (evalPoint (i % 32)) p)
    checksumBabyBear
  pure (#[record], gen)

private def runMultilinear (gen : StdGen) : IO (Array BenchRecord × StdGen) := do
  let (coeffs, gen) := (babyBearVector 256 false).run gen
  let (evals, gen) := (babyBearVector 256 false).run gen
  let (points, gen) := (babyBearPoints 256).run gen
  let coeffPoly : CMlPolynomial BabyBear.Field 8 := CMlPolynomial.ofArray coeffs 8
  let evalPoly : CMlPolynomialEval BabyBear.Field 8 := CMlPolynomialEval.ofArray evals 8
  let evalPoint (offset : Nat) : Vector BabyBear.Field 8 :=
    Vector.ofFn fun j => points.getD ((offset + j.val) % points.size) 0
  let mut records := #[]
  records := records.push (← runTimed
    "multilinear-coeff-eval" "CMlPolynomial" "eval" "BabyBear.Field"
    "8 vars, 256 coefficients, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomial.eval coeffPoly (evalPoint (i % 32)))
    checksumBabyBear)
  records := records.push (← runTimed
    "multilinear-hypercube-eval" "CMlPolynomialEval" "eval" "BabyBear.Field"
    "8 vars, 256 hypercube values, 32 points" warmupIterations measuredIterations
    (fun i => CMlPolynomialEval.eval evalPoly (evalPoint (i % 32)))
    checksumBabyBear)
  pure (records, gen)

private def runBivariate (gen : StdGen) : IO (Array BenchRecord × StdGen) := do
  let (terms, gen) := (babyBearArray 512 true).run gen
  let (points, gen) := (babyBearPoints 64).run gen
  let p := buildCBivariate terms
  let record ← runTimed
    "bivariate-full-eval" "CBivariate" "evalEval" "BabyBear.Field"
    "xDegree<32, yDegree<16, sparse coeffs, 32 points" warmupIterations measuredIterations
    (fun i =>
      let x := points.getD ((2 * (i % 32)) % points.size) 0
      let y := points.getD ((2 * (i % 32) + 1) % points.size) 0
      CBivariate.evalEval x y p)
    checksumBabyBear
  pure (#[record], gen)

private def checksumBTF3Output (output : Fin (2 ^ (2 + 2)) → AdditiveNTT.BTF₃) : Nat :=
  (List.finRange (2 ^ (2 + 2))).foldl
    (fun acc i => mixChecksum acc (checksumBTF3 (output i))) 0

private def runBTF3NTT (input : Fin 4 → AdditiveNTT.BTF₃) :
    Fin (2 ^ (2 + 2)) → AdditiveNTT.BTF₃ := by
  letI : Algebra (ConcreteBTField 0) AdditiveNTT.BTF₃ :=
    ConcreteBTFieldAlgebra (l := 0) (r := 3) (h_le := by omega)
  haveI : Fact (LinearIndependent (ConcreteBTField 0) (AdditiveNTT.computableBasisExplicit 3)) :=
    { out := AdditiveNTT.hβ_lin_indep_concrete 3 }
  exact AdditiveNTT.computableAdditiveNTT
    (𝔽q := ConcreteBTField 0) (L := AdditiveNTT.BTF₃) (r := 2 ^ 3)
    (ℓ := 2) (R_rate := 2) (h_ℓ_add_R_rate := by omega)
    (β := AdditiveNTT.computableBasisExplicit (k := 3)) (a := input)

private def runAdditiveNTT (gen : StdGen) : IO (Array BenchRecord × StdGen) := do
  let (values, gen) := (randomNatArray 4 255).run gen
  let input : Fin 4 → AdditiveNTT.BTF₃ :=
    fun i => ConcreteBinaryTower.fromNat (k := 3) (values.getD i.val 0)
  let record ← runTimed
    "additive-ntt-btf3" "computableAdditiveNTT" "computableAdditiveNTT"
    "ConcreteBTField 0 -> BTF3, l=2, R_rate=2"
    "4 input coeffs, 16 output evals" additiveNTTWarmupIterations additiveNTTMeasuredIterations
    (fun _ => runBTF3NTT input)
    checksumBTF3Output
  pure (#[record], gen)

def run : IO UInt32 := do
  let runId ← makeRunId
  let mut gen := mkStdGen seed
  let mut records := #[]
  let (univariateRecords, gen') ← runUnivariate gen
  gen := gen'
  records := appendRecords records univariateRecords
  let (multivariateRecords, gen') ← runMultivariate gen
  gen := gen'
  records := appendRecords records multivariateRecords
  let (multilinearRecords, gen') ← runMultilinear gen
  gen := gen'
  records := appendRecords records multilinearRecords
  let (bivariateRecords, gen') ← runBivariate gen
  gen := gen'
  records := appendRecords records bivariateRecords
  let (nttRecords, _) ← runAdditiveNTT gen
  records := appendRecords records nttRecords
  let results := resultsPath runId
  let report := reportPath runId
  IO.FS.writeFile results (renderJsonl records)
  IO.FS.writeFile report (renderMarkdown records)
  IO.println s!"wrote {records.size} benchmark records for run {runId}"
  pure 0

end CompPolyBench

def main : IO UInt32 :=
  CompPolyBench.run
