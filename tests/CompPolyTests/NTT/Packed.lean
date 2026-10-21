/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Instances
public import CompPoly.Univariate.NTT.BabyBear
public import CompPoly.Univariate.NTT.KoalaBear

/-! # Packed transforms over KoalaBear and BabyBear

The packed plan is generic over `Mont32Field p`; these checks run its compiled KoalaBear and
BabyBear instances. Small sizes are compared with the DFT specification, covering the scalar
leaf and the fused final layers; `2 ^ 15` points exercise the column-parallel path, against the
sequential leaf and through a round trip. The packed words go through the inline C of the
`ByteArray` word accessors, so the checks run compiled, in `lake exe CompPolyNativeSmoke`.
-/

public section
namespace CompPolyTests.NTT.Packed

open CompPoly CompPoly.CPolynomial
open Montgomery.Native32 (Mont32Field FastField)
open CompPoly.CPolynomial.NTTFast.Packed (Plan PackedNTT)
open CompPoly.PackedRepr (encode)

/-- A deterministic input of `n` elements. -/
def input (p : ℕ) [Mont32Field p] (n : ℕ) : Array (FastField p) :=
  Array.ofFn fun i : Fin n ↦ ((i.val * 7919 + 13) ^ 3 : ℕ)

theorem hu {n : ℕ} (h : n ≤ 27) : 4 * 2 ^ n < USize.size := by
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
  have := USize.le_size
  omega

/-- Forward and inverse packed transforms agree with the specification. -/
def agreesWithSpec (p : ℕ) [Mont32Field p] [PackedNTT p] (D : NTT.Domain (FastField p))
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) : Bool :=
  let P := Plan.ofDomain D h32 hu
  let a := input p D.n
  P.forwardPacked (encode a) == encode (NTT.Forward.forwardSpec D a) &&
    P.inversePacked (encode a) == encode (NTT.Inverse.inverseSpec D a)

/-- The column-parallel transform agrees with the sequential one and inverts. -/
def parallelAgrees (p : ℕ) [Mont32Field p] [PackedNTT p] (D : NTT.Domain (FastField p))
    (h32 : D.logN ≤ 32) (hu : 4 * D.n < USize.size) : Bool :=
  let P := Plan.ofDomain D h32 hu
  let a := encode (input p D.n)
  let y := P.forwardPacked a true
  y == P.forwardPacked a false && P.inversePacked y true == a

def koalaBear (logN : ℕ) (h : logN ≤ KoalaBear.twoAdicity) : NTT.Domain KoalaBear.Fast.Field :=
  NTT.KoalaBear.fastDomainOfLogN logN h

def babyBear (logN : ℕ) (h : logN ≤ BabyBear.twoAdicity) : NTT.Domain BabyBear.Fast.Field :=
  NTT.BabyBear.fastDomainOfLogN logN h

/-- Check the KoalaBear and BabyBear packed transforms. -/
def run : IO Unit := do
  let check (name : String) (ok : Bool) : IO Unit :=
    unless ok do throw <| IO.userError s!"packed NTT mismatch: {name}"
  check "KoalaBear 2^3" (agreesWithSpec _ (koalaBear 3 (by decide)) (by decide) (hu (by decide)))
  check "KoalaBear 2^8" (agreesWithSpec _ (koalaBear 8 (by decide)) (by decide) (hu (by decide)))
  check "KoalaBear 2^9" (agreesWithSpec _ (koalaBear 9 (by decide)) (by decide) (hu (by decide)))
  check "KoalaBear 2^15"
    (parallelAgrees _ (koalaBear 15 (by decide)) (by decide) (hu (by decide)))
  check "BabyBear 2^3" (agreesWithSpec _ (babyBear 3 (by decide)) (by decide) (hu (by decide)))
  check "BabyBear 2^8" (agreesWithSpec _ (babyBear 8 (by decide)) (by decide) (hu (by decide)))
  check "BabyBear 2^9" (agreesWithSpec _ (babyBear 9 (by decide)) (by decide) (hu (by decide)))
  check "BabyBear 2^15"
    (parallelAgrees _ (babyBear 15 (by decide)) (by decide) (hu (by decide)))
  IO.println "packed NTT: KoalaBear and BabyBear checks passed"

end CompPolyTests.NTT.Packed
