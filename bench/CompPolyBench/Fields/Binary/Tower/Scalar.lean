/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Fields.Arith
public import CompPoly.Fields.Binary.Tower.Fast

/-!
# Binary tower operations matched with Binius

Fast 8-, 64-, and 128-bit Fan–Paar tower arithmetic. Multiplication has a 64-step
latency chain and two independent 32-step throughput chains. Inversion mixes a fixed
word by XOR before each of 64 inversions. Squaring uses 63 dependent operations,
which is not a whole Frobenius cycle in any selected field. Only the final result is observed.
Lean's refinements live in `Tower/Fast.lean`; the Rust driver validates cross-language
chain results before timing. Field words encode tower coefficients, not field numerals.
-/

public section

open ConcreteBinaryTower

namespace CompPolyBench

/-- Shared deterministic word pool. Excluding zero and one avoids trivial mul constants. -/
def towerBenchPool (bits : Nat) (gen : StdGen) : Array Nat × StdGen :=
  let (xs, gen) := (randomNatArray fieldPoolSize (2 ^ bits - 3)).run gen
  (xs.map (· + 2), gen)

/-- Sixty-three dependent squares, unrolled seven at a time to avoid an identity block. -/
@[specialize] def towerSquareChain {F : Type} (square : F → F) (x : F) : F :=
  let rec @[specialize] go (n : Nat) (x : F) : F :=
    match n with
    | 0 => x
    | n + 1 => go n (square (square (square (square (square (square (square x)))))))
  go 9 x

/-- Run one operation on a known fast representation; Rust consumes identical fixtures. -/
@[specialize] private def runTowerOperation {F : Type} (bits : Nat) (opTag : String)
    (rep : ChainRep F) (add mul : F → F → F) (square inv : F → F)
    (preset : BenchPreset) : IO BenchGroup := do
  let tag := s!"tower-bt{bits}"
  let constant := rep.constant
  let records ← match opTag with
    | "mul" => do
      let latency ← chainLatencyRow tag opTag "mul (latency)" "latency" 64 rep
        (fun x ↦ mul x constant) preset
      let throughput ← chainThroughputRow tag opTag "mul (throughput)" "throughput"
        32 rep mul preset .parallel2
      pure #[latency, throughput]
    | "square" => do
      let row ← runTimedSpec
        { name := s!"{tag}-square-fast", representation := rep.representation,
          method := "square (63 dependent steps)", field := rep.field,
          inputShape := chainShape 63, digestIterations := digestPeriod fieldPoolSize,
          workUnits := 63, digestClass := "latency" }
        preset
        (fun i ↦ towerSquareChain square (rep.pool.getD (i % fieldPoolSize) constant))
        rep.checksum (sink := rep.sink)
      pure #[row]
    | "inv" => do
      let row ← chainLatencyRow tag opTag "inv (XOR-mixed latency)" "latency" 64 rep
        (fun x ↦ inv (add x constant)) preset
      pure #[row]
    | _ => throw <| IO.userError s!"unknown binary tower operation: {opTag}"
  pure { groupKey := s!"fields-{tag}-{opTag}", title := s!"GF(2^{bits}) tower {opTag}", records }

/-- Machine-word operands for a scalar tower level. -/
private def wordRep (bits : Nat) (xs : Array Nat) : ChainRep UInt64 :=
  let pool := xs.map UInt64.ofNat
  { representation := "UInt64 table kernels", field := s!"GF(2^{bits}) Fan–Paar tower",
    suffix := "fast", pool, constant := pool.getD 0 2,
    checksum := UInt64.toNat, sink := u64Sink }

/-- Select a tower level outside the timed region, preserving statically known operations. -/
private def runTower (bits : Nat) (opTag : String) (preset : BenchPreset) (gen : StdGen) :
    IO (BenchGroup × StdGen) := do
  let (xs, gen) := towerBenchPool bits gen
  let group ← match bits with
    | 8 =>
      runTowerOperation 8 opTag (wordRep 8 xs) (· ^^^ ·)
        Fast.mul8T Fast.sq8T Fast.inv8T preset
    | 64 =>
      runTowerOperation 64 opTag (wordRep 64 xs) (· ^^^ ·)
        Fast.mul64T Fast.sq64T Fast.inv64T preset
    | 128 =>
      let pool := xs.map Fast.FastBT128.ofNat
      let rep : ChainRep Fast.FastBT128 :=
        { representation := "FastBT128", field := "GF(2^128) Fan–Paar tower", suffix := "fast",
          pool, constant := pool.getD 0 (.ofNat 2), checksum := Fast.FastBT128.toNat,
          sink := fun x ↦ x.lo ^^^ x.hi }
      runTowerOperation 128 opTag rep Fast.FastBT128.add Fast.FastBT128.mul
        Fast.FastBT128.square Fast.FastBT128.inv preset
    | _ => throw <| IO.userError s!"unsupported binary tower width: {bits}"
  pure (group, gen)

/-- Three representative tower sizes, with shared group names in fixtures and Rust. -/
def towerScalarTasks : List BenchTask :=
  [8, 64, 128].flatMap fun bits ↦
    ["mul", "square", "inv"].map fun op ↦
      BenchTask.fromGroupRunner
        ⟨s!"fields-tower-bt{bits}-{op}", s!"GF(2^{bits}) tower {op}"⟩ (runTower bits op)

end CompPolyBench
