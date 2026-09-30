/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Fields.Binary.Tower.Scalar

/-!
# Field comparison inputs

Export the exact operand pools and chain parameters used by the existing field groups.
Rust consumes these before timing; cross-language result digests catch workload drift.
-/

public section

open Lean CompPoly CompPolyBench

/-- Fixed-width little-endian coordinate bytes, independent of runtime representation. -/
def canonicalBytes (width value : Nat) : Array Nat :=
  (Array.range width).map fun i ↦ (value >>> (8 * i)) % 256

/-- Export the selected groups as JSONL on stdout. -/
def main : IO Unit := do
  for (field, tag, modulus, width, operations) in [
      ("koalabear", "koalabear", KoalaBear.fieldSize, 4, ["add", "mul", "inv", "pow"]),
      ("mersenne31", "mersenne31", Mersenne31.fieldSize, 4, ["add", "mul", "inv", "pow"]),
      ("goldilocks", "goldilocks", Goldilocks.fieldSize, 8, ["add", "mul", "inv", "pow"]),
      ("bn254-scalar", "bn254", BN254.scalarFieldSize, 32, ["add", "mul", "inv", "pow"])] do
    for operation in operations do
      let key := s!"fields-{tag}-{operation}"
      let (values, _) := (zmodArray modulus fieldPoolSize false).run (genFor key)
      let inputs := values.map fun x ↦ canonicalBytes width (if x.val = 0 then 1 else x.val)
      let json := Lean.Json.mkObj [
        ("encoding", toJson "field-coordinates-le-v1"),
        ("basis", toJson "canonical-integer"),
        ("group_key", toJson key), ("field", toJson field),
        ("operation", toJson operation), ("modulus", toJson (canonicalBytes width modulus)),
        ("inputs", toJson inputs), ("exponent", toJson powExponent),
        ("latency_rounds", toJson
          (if operation == "inv" || operation == "pow" then expChainRounds
           else if tag == "bn254" then heavyChainRounds else chainRounds)),
        ("throughput_rounds", toJson
          (if tag == "bn254" then 160 else throughputRounds))]
      IO.println json.compress
  for bits in [8, 64, 128] do
    for operation in ["add", "mul", "square", "inv"] do
      let field := s!"tower-bt{bits}"
      let key := s!"fields-{field}-{operation}"
      let (values, _) := if operation == "add" then towerAddPool bits (genFor key)
        else towerBenchPool bits (genFor key)
      IO.println <| (Lean.Json.mkObj [
        ("encoding", toJson "field-coordinates-le-v1"),
        ("basis", toJson "fan-paar-tower"),
        ("group_key", toJson key), ("field", toJson field),
        ("operation", toJson operation), ("modulus", toJson (#[] : Array Nat)),
        ("inputs", toJson (values.map (canonicalBytes (bits / 8)))),
        ("exponent", toJson (0 : Nat)),
        ("latency_rounds", toJson
          (if operation == "add" then 0 else if operation == "square" then 63 else 64 : Nat)),
        ("throughput_rounds", toJson (if operation == "add" then 1024 else 32 : Nat))]).compress
