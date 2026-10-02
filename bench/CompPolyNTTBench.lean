/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.NTTFast.Parallel

/-! # Natural-order KoalaBear NTT benchmarks against optimized Plonky3 -/

public section
open CompPoly CompPolyBench

/-- Read canonical 32-bit coordinates without silently reducing malformed fixtures. -/
def nttCoordinates (bytes : ByteArray) : IO (Array KoalaBear.Fast.Field) := do
  if bytes.size % 4 != 0 then throw <| IO.userError "unaligned NTT fixture"
  let mut values := Array.mkEmpty (bytes.size / 4)
  for i in [:bytes.size / 4] do
    let mut v := 0
    for j in [:4] do
      v := v * 256 + bytes[4 * i + (3 - j)]!.toNat
    if v ≥ 2130706433 then throw <| IO.userError "noncanonical NTT coordinate"
    values := values.push (KoalaBear.Fast.ofField (v : KoalaBear.Field))
  return values

/-- Export the certified root or time a transform on two varying fixture inputs. -/
def main (args : List String) : IO UInt32 := do
  if let ["--root", size] := args then
    let some logN := size.toNat? | throw <| IO.userError "invalid log size"
    if h : logN ≤ KoalaBear.twoAdicity then
      IO.println (CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN h).omega.toNat
      return 0
    else throw <| IO.userError "unsupported domain"
  let [path, size, direction, validate] := args |
    throw <| IO.userError "usage: CompPolyNTTBench FIXTURE LOG_N forward|inverse true|false"
  let some logN := size.toNat? | throw <| IO.userError "invalid log size"
  if direction != "forward" && direction != "inverse" then
    throw <| IO.userError "invalid direction"
  if validate != "true" && validate != "false" then throw <| IO.userError "invalid validation flag"
  if h : logN ≤ KoalaBear.twoAdicity then
    let domain := CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN h
    let plan := CPolynomial.NTTFast.NaturalPlan.ofDomain domain
    let n := 2 ^ logN
    let values ← nttCoordinates (← IO.FS.readBinFile path)
    if values.size != 1 + 2 * n then throw <| IO.userError "incorrect NTT fixture length"
    if values.getD 0 0 != domain.omega then throw <| IO.userError "incorrect NTT root"
    let inputs := #[values.extract 1 (n + 1), values.extract (n + 1) (2 * n + 1)]
    let workers := ((← IO.getEnv "LEAN_NUM_THREADS").bind String.toNat?).getD 16
    if workers == 0 then throw <| IO.userError "LEAN_NUM_THREADS must be positive"
    let logWorkers := workers.log2
    validateOnlyRef.set (validate == "true")
    let row ← runTimedSpec
      { name := s!"ntt-koalabear-{logN}-{direction}-fast", representation := "Array",
        method := "proved parallel radix-4, natural order", field := "koalabear",
        inputShape := s!"{n} elements",
        digestIterations := 2, digestClass := direction }
      .medium
      (fun i ↦
        let input := inputs[i % 2]!
        if direction == "forward" then plan.forwardParallel input logWorkers
        else plan.inverseParallel input logWorkers)
      (checksumArray checksumKoalaBearFast)
      (sink := arraySampleSink (fun x ↦ x.toNat.toUInt64))
    let record : BenchRecord := { row with groupKey := s!"ntt-koalabear-{logN}-{direction}" }
    IO.println record.toJsonLine
    return 0
  else throw <| IO.userError "unsupported domain"
