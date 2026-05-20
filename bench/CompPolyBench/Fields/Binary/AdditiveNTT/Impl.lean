/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common

/-!
# Additive NTT Benchmarks
-/

open ConcreteBinaryTower

namespace CompPolyBench

/-- Benchmark group metadata for `CompPoly.Fields.Binary.AdditiveNTT.Impl`. -/
def additiveNttGroupInfos : List BenchGroupInfo := [
  ⟨"additive-ntt-btf3-l2-r2", "Additive NTT BTF3 l=2 R_rate=2"⟩,
  ⟨"additive-ntt-btf3-l4-r2", "Additive NTT BTF3 l=4 R_rate=2"⟩,
  ⟨"additive-ntt-btf4-l7-r2", "Additive NTT BTF4 l=7 R_rate=2"⟩
]

/-- Checksum all output values from a `BTF₃` additive NTT benchmark. -/
private def checksumBtf3Output {n : Nat} (output : Fin (2 ^ n) → AdditiveNTT.BTF₃) : Nat :=
  (List.finRange (2 ^ n)).foldl
    (fun acc i => mixChecksum acc (checksumBtf3 (output i))) 0

/-- Checksum a `BTF₃` additive NTT output array. -/
private def checksumBtf3OutputArray {n : Nat} (output : Array AdditiveNTT.BTF₃) : Nat :=
  checksumBtf3Output (AdditiveNTT.arrayToFinFunction (2 ^ n) output)

/-- Checksum a concrete binary-tower additive NTT output array. -/
private def checksumConcreteBtfOutputArray {k n : Nat} (output : Array (ConcreteBTField k)) :
    Nat :=
  (List.finRange (2 ^ n)).foldl
    (fun acc i =>
      mixChecksum acc
        (checksumConcreteBtf ((AdditiveNTT.arrayToFinFunction (2 ^ n) output) i))) 0

/-- Run an additive NTT over `BTF₃`. -/
private def runBtf3Ntt (ℓ R_rate : Nat) (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ 3)
    (input : Fin (2 ^ ℓ) → AdditiveNTT.BTF₃) :
    Fin (2 ^ (ℓ + R_rate)) → AdditiveNTT.BTF₃ := by
  letI : Algebra (ConcreteBTField 0) AdditiveNTT.BTF₃ :=
    ConcreteBTFieldAlgebra (l := 0) (r := 3) (h_le := by omega)
  haveI : Fact (LinearIndependent (ConcreteBTField 0) (AdditiveNTT.computableBasisExplicit 3)) :=
    { out := AdditiveNTT.hβ_lin_indep_concrete 3 }
  exact AdditiveNTT.computableAdditiveNTT
    (𝔽q := ConcreteBTField 0) (L := AdditiveNTT.BTF₃) (r := 2 ^ 3)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (β := AdditiveNTT.computableBasisExplicit (k := 3)) (a := input)

/-- Run the fast additive NTT implementation over `BTF₃`. -/
private def runBtf3NttFast (ℓ R_rate : Nat) (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ 3)
    (input : Fin (2 ^ ℓ) → AdditiveNTT.BTF₃) :
    Array AdditiveNTT.BTF₃ := by
  letI : Algebra (ConcreteBTField 0) AdditiveNTT.BTF₃ :=
    ConcreteBTFieldAlgebra (l := 0) (r := 3) (h_le := by omega)
  exact AdditiveNTT.computableAdditiveNTTFast
    (L := AdditiveNTT.BTF₃) (r := 2 ^ 3)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (β := AdditiveNTT.computableBasisExplicit (k := 3)) (a := input)

/-- Run the fast additive NTT implementation over a concrete binary-tower field. -/
private def runConcreteBtfNttFast (k ℓ R_rate : Nat)
    (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ k)
    (input : Fin (2 ^ ℓ) → ConcreteBTField k) :
    Array (ConcreteBTField k) := by
  letI : Fintype (ConcreteBTField k) :=
    Fintype.ofEquiv (Fin (2 ^ (2 ^ k))) (BitVec.equivFin (m := 2 ^ k)).symm.toEquiv
  letI : Algebra (ConcreteBTField 0) (ConcreteBTField k) :=
    ConcreteBTFieldAlgebra (l := 0) (r := k) (h_le := by omega)
  exact AdditiveNTT.computableAdditiveNTTFast
    (L := ConcreteBTField k) (r := 2 ^ k)
    (ℓ := ℓ) (R_rate := R_rate) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (β := AdditiveNTT.computableBasisExplicit (k := k)) (a := input)

/-- Run one additive NTT benchmark case over `BTF₃`. -/
private def runAdditiveNttCase (ℓ R_rate : Nat) (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ 3)
    (key currentName fastName : String) (warmup measured fastMeasured : Nat)
    (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let inputSize := 2 ^ ℓ
  let outputSize := 2 ^ (ℓ + R_rate)
  let (values, gen) := (randomNatArray inputSize 255).run gen
  let input : Fin (2 ^ ℓ) → AdditiveNTT.BTF₃ :=
    fun i => ConcreteBinaryTower.fromNat (k := 3) (values.getD i.val 0)
  let fieldLabel := s!"ConcreteBTField 0 -> BTF3, l={ℓ}, R_rate={R_rate}"
  let inputShape := s!"{inputSize} input coeffs, {outputSize} output evals"
  let checksumIterations := groupChecksumIterations measured [fastMeasured]
  let currentRecord ← runTimed
    currentName "computableAdditiveNTT" "computableAdditiveNTT"
    fieldLabel inputShape preset warmup measured
    (fun _ => runBtf3Ntt ℓ R_rate h_ℓ_add_R_rate input)
    (checksumBtf3Output (n := ℓ + R_rate)) (checksumIterations := checksumIterations)
  let fastRecord ← runTimed
    fastName "computableAdditiveNTTFast" "computableAdditiveNTTFast"
    fieldLabel inputShape preset warmup fastMeasured
    (fun _ => runBtf3NttFast ℓ R_rate h_ℓ_add_R_rate input)
    (checksumBtf3OutputArray (n := ℓ + R_rate)) (checksumIterations := checksumIterations)
  pure ({
      groupKey := key,
      title := s!"Additive NTT BTF3 l={ℓ} R_rate={R_rate}",
      records := #[currentRecord, fastRecord] }, gen)

/-- Run one larger fast-only additive NTT benchmark over a concrete binary-tower field. -/
private def runAdditiveNttFastLargeCase (k ℓ R_rate : Nat)
    (h_ℓ_add_R_rate : ℓ + R_rate < 2 ^ k) (key fastName : String)
    (warmup measured : Nat) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let inputSize := 2 ^ ℓ
  let outputSize := 2 ^ (ℓ + R_rate)
  let (values, gen) := (randomNatArray inputSize (2 ^ (2 ^ k) - 1)).run gen
  let input : Fin (2 ^ ℓ) → ConcreteBTField k :=
    fun i => ConcreteBinaryTower.fromNat (k := k) (values.getD i.val 0)
  let fieldLabel := s!"ConcreteBTField 0 -> BTF{k}, l={ℓ}, R_rate={R_rate}"
  let inputShape := s!"{inputSize} input coeffs, {outputSize} output evals"
  let fastRecord ← runTimed
    fastName "computableAdditiveNTTFast" "computableAdditiveNTTFast"
    fieldLabel inputShape preset warmup measured
    (fun _ => runConcreteBtfNttFast k ℓ R_rate h_ℓ_add_R_rate input)
    (checksumConcreteBtfOutputArray (k := k) (n := ℓ + R_rate))
  pure ({
      groupKey := key,
      title := s!"Additive NTT BTF{k} l={ℓ} R_rate={R_rate}",
      records := #[fastRecord] }, gen)

/-- Run the small additive NTT benchmark over `BTF₃`. -/
private def runAdditiveNttBtf3L2R2 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let warmup := additiveNttWarmupIterations preset
  let measured := additiveNttMeasuredIterations preset
  let fastMeasured := preset.selectNat 13000 2000 400
  runAdditiveNttCase 2 2 (by omega)
    "additive-ntt-btf3-l2-r2" "additive-ntt-btf3" "additive-ntt-btf3-fast"
    warmup measured fastMeasured preset gen

/-- Run the wider additive NTT benchmark over `BTF₃`. -/
private def runAdditiveNttBtf3L4R2 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let warmup := preset.selectNat 2 1 0
  let measured := preset.selectNat 10 1 1
  let fastMeasured := preset.selectNat 2000 300 60
  runAdditiveNttCase 4 2 (by omega)
    "additive-ntt-btf3-l4-r2" "additive-ntt-btf3-l4-r2"
    "additive-ntt-btf3-l4-r2-fast" warmup measured fastMeasured preset gen

/-- Run the large fast-only additive NTT benchmark over `BTF₄`. -/
private def runAdditiveNttBtf4L7R2 (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let warmup := preset.selectNat 1 1 0
  let measured := preset.selectNat 10 1 1
  runAdditiveNttFastLargeCase 4 7 2 (by omega)
    "additive-ntt-btf4-l7-r2" "additive-ntt-btf4-l7-r2-fast" warmup measured preset gen

/-- Runnable additive-NTT benchmark tasks. -/
def additiveNttTasks : List BenchTask := [
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-btf3-l2-r2", "Additive NTT BTF3 l=2 R_rate=2"⟩
    runAdditiveNttBtf3L2R2,
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-btf3-l4-r2", "Additive NTT BTF3 l=4 R_rate=2"⟩
    runAdditiveNttBtf3L4R2,
  BenchTask.fromGroupRunner
    ⟨"additive-ntt-btf4-l7-r2", "Additive NTT BTF4 l=7 R_rate=2"⟩
    runAdditiveNttBtf4L7R2
]

/-- Run the additive NTT benchmark. -/
def runAdditiveNtt (preset : BenchPreset) (selection : BenchSelection) (gen : StdGen) :
    IO (Array BenchGroup × StdGen) := do
  runSelectedTasks additiveNttTasks preset selection gen

end CompPolyBench
