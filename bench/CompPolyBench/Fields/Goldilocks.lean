/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.Goldilocks

/-!
# Goldilocks field arithmetic benchmarks

Times multiplication and inversion over the Goldilocks prime `2^64 - 2^32 + 1`. Each
group runs the canonical `ZMod` implementation and the verified native-word
implementation on shared inputs, so the group checksum cross-checks the two.

Goldilocks fits neither Montgomery carrier — `Mont32Field` requires modulus `< 2^31`
and `Mont64x8Field` is an eight-limb layout — so the fast path is the single-word
`UInt64` implementation in `CompPoly.Fields.Goldilocks.Fast`.
-/

public section

namespace CompPolyBench

/-- Input-shape label shared by the Goldilocks arithmetic benchmarks. -/
private def goldilocksShape : String := "256 random elements"

/-- Time canonical against native-word Goldilocks multiplication as a single group. -/
private def runGoldilocksMul (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let fastValues := goldilocksFastArray values
  let checksumIterations := digestPeriod values.size
  let zmodRecord ← runTimedSpec
    { name := "goldilocks-mul-zmod", representation := "ZMod", method := "mul",
      field := "Goldilocks.Field", inputShape := goldilocksShape,
      digestIterations := checksumIterations }
    preset
    (fun i ↦ values.getD (i % values.size) 1 * values.getD ((i + 1) % values.size) 1) checksumZMod
    (sink := sinkZMod)
  let fastRecord ← runTimedSpec
    { name := "goldilocks-mul-fast", representation := "UInt64", method := "mul",
      field := "Goldilocks.Fast.Field", inputShape := goldilocksShape,
      digestIterations := checksumIterations }
    preset
    (fun i ↦ fastValues.getD (i % fastValues.size) 1 *
      fastValues.getD ((i + 1) % fastValues.size) 1)
    checksumGoldilocksFast (sink := sinkGoldilocksFast)
  pure ({ groupKey := "fields-goldilocks-mul", title := "Goldilocks multiplication",
          records := #[zmodRecord, fastRecord] }, gen)

/-- Time canonical against native-word Goldilocks inversion as a single group. -/
private def runGoldilocksInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let fastValues := goldilocksFastArray values
  let checksumIterations := digestPeriod values.size
  let zmodRecord ← runTimedSpec
    { name := "goldilocks-inv-zmod", representation := "ZMod", method := "inv",
      field := "Goldilocks.Field", inputShape := goldilocksShape,
      digestIterations := checksumIterations }
    preset (fun i ↦ (values.getD (i % values.size) 1)⁻¹) checksumZMod
    (sink := sinkZMod)
  let fastRecord ← runTimedSpec
    { name := "goldilocks-inv-fast", representation := "UInt64", method := "inv (Fermat chain)",
      field := "Goldilocks.Fast.Field", inputShape := goldilocksShape,
      digestIterations := checksumIterations }
    preset (fun i ↦ (fastValues.getD (i % fastValues.size) 1)⁻¹)
    checksumGoldilocksFast (sink := sinkGoldilocksFast)
  pure ({ groupKey := "fields-goldilocks-inv", title := "Goldilocks inversion",
          records := #[zmodRecord, fastRecord] }, gen)

/-- Registry entries for the Goldilocks arithmetic benchmarks. -/
def goldilocksTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"fields-goldilocks-mul", "Goldilocks multiplication"⟩
    runGoldilocksMul,
  BenchTask.fromGroupRunner
    ⟨"fields-goldilocks-inv", "Goldilocks inversion"⟩
    runGoldilocksInv
]

end CompPolyBench
