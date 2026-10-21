/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.BabyBear.InterpolateCoset
public import CompPoly.Fields.KoalaBear.InterpolateCoset
public import CompPoly.Univariate.NTT.BabyBear
public import CompPoly.Univariate.NTT.KoalaBear

/-! # Packed coset interpolation over KoalaBear and BabyBear

`interpolateCosetPacked` is generic over `Mont32Field p` with a quartic binomial extension; these
checks run its compiled KoalaBear and BabyBear instances against the reference
`interpolateCoset` on `2 ^ 10` rows and five columns, which exercises the four-column and
single-column sums and two tasks. The packed words go through the inline C of the `ByteArray`
word accessors, so the checks run compiled, in `lake exe CompPolyNativeSmoke`.
-/

public section
namespace CompPolyTests.Fields.Montgomery.InterpolateCosetPacked

open CompPoly Montgomery.Native32

/-- Packed and reference interpolation agree on a deterministic matrix. -/
def agrees (p : ℕ) [Mont32Field p] [Binomial4 p] [PackedInterpolation p] (ω : FastField p) :
    Bool :=
  let logN := 10
  let width := 5
  let values : Array (FastField p) := Array.ofFn fun i : Fin (2 ^ logN * width) ↦
    ((i.val * 7919 + 13) ^ 3 : ℕ)
  let words := PackedRepr.encode values
  let s : FastField p := 3
  let z : Ext4 p := ⟨5, 6, 7, 8⟩
  interpolateCosetPacked logN ω s width words z ==
    interpolateCoset logN ω s width (decodeWords p words) z

/-- Check the KoalaBear and BabyBear instances. -/
def run : IO Unit := do
  unless agrees _ (CPolynomial.NTT.KoalaBear.fastDomainOfLogN 10 (by decide)).omega do
    throw <| IO.userError "packed interpolation mismatch: KoalaBear"
  unless agrees _ (CPolynomial.NTT.BabyBear.fastDomainOfLogN 10 (by decide)).omega do
    throw <| IO.userError "packed interpolation mismatch: BabyBear"
  IO.println "packed coset interpolation: KoalaBear and BabyBear checks passed"

end CompPolyTests.Fields.Montgomery.InterpolateCosetPacked
