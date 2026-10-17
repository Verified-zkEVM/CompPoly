/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPolyBench.Univariate.Common
public import CompPoly.Univariate.NTTFast.Packed.CosetLde
public import CompPoly.Univariate.NTT.KoalaBear

/-! # KoalaBear coset low-degree extension against Plonky3's `coset_lde_batch` -/

public section
open CompPoly CompPolyBench

/-- Read canonical 32-bit coordinates without silently reducing malformed fixtures. -/
def ldeCoordinates (bytes : ByteArray) : IO (Array KoalaBear.Fast.Field) := do
  if bytes.size % 4 != 0 then throw <| IO.userError "unaligned LDE fixture"
  let mut values := Array.mkEmpty (bytes.size / 4)
  for i in [:bytes.size / 4] do
    let mut v := 0
    for j in [:4] do
      v := v * 256 + bytes[4 * i + (3 - j)]!.toNat
    if v ≥ 2130706433 then throw <| IO.userError "noncanonical LDE coordinate"
    values := values.push (KoalaBear.Fast.ofField (v : KoalaBear.Field))
  return values

/-- Time `cosetLde` on a fixture: the root of the extended domain, the shift, then two row-major
matrices. -/
def main (args : List String) : IO UInt32 := do
  let [path, logRows, widthArg, bitsArg, validate] := args |
    throw <| IO.userError "usage: CompPolyLdeBench FIXTURE LOG_H WIDTH ADDED_BITS true|false"
  let some logH := logRows.toNat? | throw <| IO.userError "invalid log height"
  let some width := widthArg.toNat? | throw <| IO.userError "invalid width"
  let some bits := bitsArg.toNat? | throw <| IO.userError "invalid added bits"
  if validate != "true" && validate != "false" then throw <| IO.userError "invalid validation flag"
  if h : logH + bits ≤ KoalaBear.twoAdicity then
    let domain := CPolynomial.NTT.KoalaBear.fastDomainOfLogN (logH + bits) h
    let rows := 2 ^ logH
    let words ← ldeCoordinates (← IO.FS.readBinFile path)
    if words.size != 2 + 2 * rows * width then throw <| IO.userError "incorrect fixture length"
    if words.getD 0 0 != domain.omega then throw <| IO.userError "incorrect root"
    have h32 : domain.logN ≤ 32 := by
      change logH + bits ≤ 32
      have : KoalaBear.twoAdicity = 24 := rfl
      omega
    have hu : 4 * domain.n < USize.size := by
      have hp : 2 ^ (logH + bits) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h
      have := USize.le_size
      change 4 * 2 ^ (logH + bits) < USize.size
      omega
    let plan := CPolynomial.NTTFast.Packed.LdePlan.ofDomain domain bits
      (by change bits ≤ logH + bits; omega) (words.getD 1 0) h32 hu
    -- The matrices are packed outside timing, as Montgomery words like Plonky3's storage.
    let inputs := #[words.extract 2 (2 + rows * width), words.extract (2 + rows * width)
      words.size].map CPolynomial.NTTFast.Packed.Native.encodeFields
    let word (b : ByteArray) (i : Nat) : UInt64 :=
      (CPolynomial.NTTFast.Packed.Native.read b i).toUInt64
    validateOnlyRef.set (validate == "true")
    let spec : BenchSpec :=
      { name := s!"lde-koalabear-{logH}-{width}-{bits}-packed",
        representation := "Array ByteArray (row chunks)",
        method := "transposed columns, inverse then per-coset DIF transforms, parallel tasks",
        field := "koalabear", inputShape := s!"{rows} rows × {width} columns, blowup 2^{bits}",
        digestIterations := 2, digestClass := "lde" }
    -- The digest reads the joined rows, outside timing.
    let row ← runTimedSpec spec .large
      (fun i ↦ CPolynomial.NTTFast.Packed.Native.cosetLde plan width inputs[i % 2]!)
      (fun cs ↦ checksumArray checksumKoalaBearFast (CompPoly.PackedRepr.decode
        (R := KoalaBear.Fast.Field) (CPolynomial.NTTFast.Packed.Native.joinRows cs)))
      (sink := fun cs ↦ sinkStep (word cs[0]! 0) cs.size.toUInt64)
    let record : BenchRecord := { row with groupKey := s!"lde-koalabear-{logH}-{width}-{bits}" }
    IO.println record.toJsonLine
    return 0
  else throw <| IO.userError "unsupported domain"
