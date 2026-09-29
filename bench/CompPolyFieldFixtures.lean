/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Fields.Arith

/-!
# Field comparison inputs

Export the exact operand pools and chain parameters used by the existing field groups.
Rust consumes these before timing; cross-language result digests catch workload drift.
-/

public section

open Lean CompPoly CompPolyBench

/-- Fixed-width little-endian canonical integer bytes, independent of runtime representation. -/
def canonicalBytes (width value : Nat) : Array Nat :=
  (Array.range width).map fun i ↦ (value >>> (8 * i)) % 256

/-- Export the selected groups as JSONL on stdout. -/
def main : IO Unit := do
  for (field, tag, modulus, width, operations) in [
      ("koalabear", "koalabear", KoalaBear.fieldSize, 4, ["add", "mul", "inv", "pow"]),
      ("mersenne31", "mersenne31", Mersenne31.fieldSize, 4, ["add", "mul", "inv", "pow"]),
      ("goldilocks", "goldilocks", Goldilocks.fieldSize, 8, ["add", "mul", "inv", "pow"]),
      ("bn254-scalar", "bn254", BN254.scalarFieldSize, 32, ["mul"])] do
    for operation in operations do
      let key := s!"fields-{tag}-{operation}"
      let (values, _) := (zmodArray modulus fieldPoolSize false).run (genFor key)
      let inputs := values.map fun x ↦ canonicalBytes width (if x.val = 0 then 1 else x.val)
      let json := Lean.Json.mkObj [
        ("encoding", toJson "canonical-le-bytes-v1"),
        ("group_key", toJson key), ("field", toJson field),
        ("operation", toJson operation), ("modulus", toJson (canonicalBytes width modulus)),
        ("inputs", toJson inputs), ("exponent", toJson powExponent),
        ("latency_rounds", toJson
          (if tag == "bn254" then heavyChainRounds
           else if operation == "add" || operation == "mul" then chainRounds else expChainRounds)),
        ("throughput_rounds", toJson
          (if tag == "bn254" then heavyThroughputRounds else throughputRounds))]
      IO.println json.compress
