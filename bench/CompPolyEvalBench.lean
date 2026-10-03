/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Fields.Inputs
public import CompPoly.Fields.Binary.Tower.Fast
public import CompPoly.Univariate.EvalFastFields

/-! # One-polynomial, one-point evaluation against Rust -/

public section
open CompPoly CompPolyBench

/-- Decode fixed-width little-endian field coordinates outside timing. -/
def readCoordinates (bytes : ByteArray) (width count : Nat) : Array Nat := Id.run do
  let mut values := Array.mkEmpty count
  for i in [:count] do
    let mut value := 0
    for j in [:width] do
      value := value * 256 + bytes[i * width + (width - 1 - j)]!.toNat
    values := values.push value
  return values

/-- Run the existing Horner API or the parallel API on a prebuilt polynomial. -/
@[specialize]
def runEval {F : Type} [Semiring F] [CPolynomial.EvalKernel F] [BEq F] [LawfulBEq F]
    (field : String) (values : Array Nat) (n depth : Nat) (mode : String)
    (decode : Nat → F) (checksum : F → Nat) (sink : F → UInt64) : IO Unit := do
  let points := (values.extract 0 4).map decode
  let p := cpolyOfArray ((values.extract 4 (n + 4)).map decode)
  if p.val.size != n then throw <| IO.userError "fixture must have nonzero leading coefficient"
  let row ← runTimedSpec
    { name := s!"poly-eval-{field}-{n}-{mode}-fast", representation := "CPolynomial",
      method := mode, field, inputShape := s!"{n} coefficients, one point per evaluation",
      digestIterations := 4, digestClass := mode }
    .medium
    (fun i ↦
      let x := points.getD (i % 4) 0
      if mode == "horner" then p.evalHorner x else p.evalFast x depth)
    checksum (sink := sink)
  IO.println ({ row with groupKey := s!"poly-eval-{field}-{n}" } : BenchRecord).toJsonLine

/-- Binary fixture: four points followed by coefficients, all fixed-width coordinates. -/
def main (args : List String) : IO UInt32 := do
  let [field, path, count, logWorkers, mode, validate] := args |
    throw <| IO.userError "usage: CompPolyEvalBench FIELD FIXTURE COUNT LOG_WORKERS MODE VALIDATE"
  let some n := count.toNat? | throw <| IO.userError "invalid count"
  let some depth := logWorkers.toNat? | throw <| IO.userError "invalid worker count"
  if mode != "horner" && mode != "parallel" then throw <| IO.userError "invalid mode"
  let width := match field with
    | "koalabear" => 4 | "goldilocks" => 8 | "bn254" => 32 | "tower-bt128" => 16
    | _ => 0
  if width == 0 then throw <| IO.userError "unsupported field"
  let bytes ← IO.FS.readBinFile path
  if bytes.size < (n + 4) * width then throw <| IO.userError "short fixture"
  let values := readCoordinates bytes width (n + 4)
  validateOnlyRef.set (validate == "true")
  match field with
  | "koalabear" =>
    runEval field values n depth mode
      (fun v ↦ KoalaBear.Fast.ofField (v : KoalaBear.Field))
      checksumKoalaBearFast (fun v ↦ (checksumKoalaBearFast v).toUInt64)
  | "goldilocks" =>
    runEval field values n depth mode Goldilocks.Fast.ofNat
      checksumGoldilocksFast (fun v ↦ v.val)
  | "bn254" =>
    runEval field values n depth mode
      (fun v ↦ BN254.Fast.ofField (v : BN254.ScalarField)) checksumBn254Fast sinkMont64x4
  | "tower-bt128" =>
    runEval field values n depth mode
      ConcreteBinaryTower.Fast.FastBT128.ofNat ConcreteBinaryTower.Fast.FastBT128.toNat
      (fun v ↦ v.lo ^^^ v.hi)
  | _ => pure ()
  return 0
