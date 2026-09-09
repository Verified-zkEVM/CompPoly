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
  let warmup := warmupIterations preset
  let zmodMeasured := preset.selectNat 200000 30000 6000
  let fastMeasured := preset.selectNat 200000 30000 6000
  let checksumIterations := groupChecksumIterations zmodMeasured [fastMeasured]
  let zmodRecord ← runTimed "goldilocks-mul-zmod" "ZMod" "mul" "Goldilocks.Field"
    goldilocksShape preset warmup zmodMeasured
    (fun i ↦ values.getD (i % values.size) 1 * values.getD ((i + 1) % values.size) 1)
    checksumZMod (checksumIterations := checksumIterations) (sink := sinkZMod)
  let fastRecord ← runTimed "goldilocks-mul-fast" "UInt64" "mul" "Goldilocks.Fast.Field"
    goldilocksShape preset warmup fastMeasured
    (fun i ↦ fastValues.getD (i % fastValues.size) 1 *
      fastValues.getD ((i + 1) % fastValues.size) 1)
    checksumGoldilocksFast (checksumIterations := checksumIterations)
    (sink := sinkGoldilocksFast)
  pure ({ groupKey := "fields-goldilocks-mul", title := "Goldilocks multiplication",
          records := #[zmodRecord, fastRecord] }, gen)

/-- Time canonical against native-word Goldilocks inversion as a single group. -/
private def runGoldilocksInv (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (values, gen) := (zmodArray Goldilocks.fieldSize 256 false).run gen
  let fastValues := goldilocksFastArray values
  let warmup := warmupIterations preset
  let zmodMeasured := preset.selectNat 20000 3000 600
  let fastMeasured := preset.selectNat 24000 3600 720
  let checksumIterations := groupChecksumIterations zmodMeasured [fastMeasured]
  let zmodRecord ← runTimed "goldilocks-inv-zmod" "ZMod" "inv" "Goldilocks.Field"
    goldilocksShape preset warmup zmodMeasured
    (fun i ↦ (values.getD (i % values.size) 1)⁻¹)
    checksumZMod (checksumIterations := checksumIterations) (sink := sinkZMod)
  let fastRecord ← runTimed "goldilocks-inv-fast" "UInt64" "inv (Fermat chain)"
    "Goldilocks.Fast.Field" goldilocksShape preset warmup fastMeasured
    (fun i ↦ (fastValues.getD (i % fastValues.size) 1)⁻¹)
    checksumGoldilocksFast (checksumIterations := checksumIterations)
    (sink := sinkGoldilocksFast)
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
