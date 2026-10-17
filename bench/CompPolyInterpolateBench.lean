/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Common
public import CompPoly.Fields.KoalaBear.InterpolateCosetPacked
public import CompPoly.Univariate.NTT.KoalaBear

/-! # KoalaBear coset interpolation against Plonky3's `interpolate_coset` -/

public section
open CompPoly CompPolyBench

/-- Read canonical 32-bit coordinates without silently reducing malformed fixtures. -/
def interpolateCoordinates (bytes : ByteArray) : IO (Array KoalaBear.Fast.Field) := do
  if bytes.size % 4 != 0 then throw <| IO.userError "unaligned interpolation fixture"
  let mut values := Array.mkEmpty (bytes.size / 4)
  for i in [:bytes.size / 4] do
    let mut v := 0
    for j in [:4] do
      v := v * 256 + bytes[4 * i + (3 - j)]!.toNat
    if v ≥ 2130706433 then throw <| IO.userError "noncanonical interpolation coordinate"
    values := values.push (KoalaBear.Fast.ofField (v : KoalaBear.Field))
  return values

/-- The digest of all output coordinates, in the order Plonky3 lists them. -/
def checksumExt4Array (xs : Array KoalaBear.Fast.Ext4) : Nat :=
  xs.foldl (fun acc e ↦ [e.c0, e.c1, e.c2, e.c3].foldl
    (fun acc c ↦ mixChecksum acc (checksumKoalaBearFast c)) acc) 0

/-- Time `interpolateCosetPacked` or the proved reference `interpolateCoset` on a fixture: root,
shift, two points, then the row-major matrix. -/
def main (args : List String) : IO UInt32 := do
  let [path, size, widthArg, validate, impl] := args |
    throw <| IO.userError
      "usage: CompPolyInterpolateBench FIXTURE LOG_N WIDTH true|false packed|reference"
  if impl != "packed" && impl != "reference" then throw <| IO.userError "invalid implementation"
  let some logN := size.toNat? | throw <| IO.userError "invalid log size"
  let some width := widthArg.toNat? | throw <| IO.userError "invalid width"
  if validate != "true" && validate != "false" then throw <| IO.userError "invalid validation flag"
  if h : logN ≤ KoalaBear.twoAdicity then
    let n := 2 ^ logN
    let words ← interpolateCoordinates (← IO.FS.readBinFile path)
    if words.size != 10 + n * width then throw <| IO.userError "incorrect fixture length"
    let ω := (CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN h).omega
    if words.getD 0 0 != ω then throw <| IO.userError "incorrect root"
    let shift := words.getD 1 0
    let point (k : Nat) : KoalaBear.Fast.Ext4 :=
      ⟨words.getD (2 + 4 * k) 0, words.getD (3 + 4 * k) 0, words.getD (4 + 4 * k) 0,
        words.getD (5 + 4 * k) 0⟩
    let points := #[point 0, point 1]
    let evals := words.extract 10 words.size
    -- The packed path reads Montgomery words, like Plonky3's matrix storage.
    let packed := evals.foldl (fun b (x : KoalaBear.Fast.Field) ↦
      let w := x.val
      b.push w.toUInt8 |>.push (w >>> 8).toUInt8 |>.push (w >>> 16).toUInt8
        |>.push (w >>> 24).toUInt8) (ByteArray.emptyWithCapacity (4 * evals.size))
    validateOnlyRef.set (validate == "true")
    let spec : BenchSpec := if impl == "packed" then
      { name := s!"interpolate-koalabear-{logN}-{width}-packed", representation := "ByteArray",
        method := "base-field weights in blocks, lazy column sums, parallel row ranges",
        field := "koalabear", inputShape := s!"{n} rows × {width} columns",
        digestIterations := 2, digestClass := "interpolate" }
    else
      { name := s!"interpolate-koalabear-{logN}-{width}-reference",
        representation := "Array KoalaBear.Fast.Field",
        method := "proved reference: batch inversion, per-column sums", field := "koalabear",
        inputShape := s!"{n} rows × {width} columns", digestIterations := 2,
        digestClass := "interpolate" }
    let run : Nat → Array KoalaBear.Fast.Ext4 := if impl == "packed" then
      fun i ↦ KoalaBear.Fast.interpolateCosetPacked logN ω shift width packed points[i % 2]!
    else fun i ↦ KoalaBear.Fast.interpolateCoset logN ω shift width evals points[i % 2]!
    let row ← runTimedSpec spec .large run checksumExt4Array
      (sink := fun xs ↦ (xs[0]!.c0.val.toUInt64) ^^^ (xs.size.toUInt64 <<< 32))
    let record : BenchRecord := { row with groupKey := s!"interpolate-koalabear-{logN}-{width}" }
    IO.println record.toJsonLine
    return 0
  else throw <| IO.userError "unsupported domain"
