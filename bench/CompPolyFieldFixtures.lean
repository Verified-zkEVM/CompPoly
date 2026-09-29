/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Fields.Arith

/-!
# Small-field comparison inputs

Export the exact operand pools and chain parameters used by the existing field groups.
Rust consumes these before timing; cross-language result digests catch workload drift.
-/

public section

open Lean CompPoly CompPolyBench

/-- Export the twelve selected groups as JSONL on stdout. -/
def main : IO Unit := do
  for (field, modulus) in [
      ("koalabear", KoalaBear.fieldSize),
      ("mersenne31", Mersenne31.fieldSize),
      ("goldilocks", Goldilocks.fieldSize)] do
    for operation in ["add", "mul", "inv", "pow"] do
      let key := s!"fields-{field}-{operation}"
      let (values, _) := (zmodArray modulus fieldPoolSize false).run (genFor key)
      let inputs := values.map fun x ↦ if x.val = 0 then 1 else x.val
      let json := Lean.Json.mkObj [
        ("group_key", toJson key), ("field", toJson field),
        ("operation", toJson operation), ("modulus", toJson modulus),
        ("inputs", toJson inputs), ("exponent", toJson powExponent),
        ("latency_rounds", toJson
          (if operation == "add" || operation == "mul" then chainRounds else expChainRounds)),
        ("throughput_rounds", toJson throughputRounds)]
      IO.println json.compress
