/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public meta import CompPoly.Fields.KoalaBear.InterpolateCoset

/-!
# Coset interpolation tests

Evaluate two polynomials of degree below 8 on the coset `3 · ⟨ω⟩` of the order-8 subgroup, run
`KoalaBear.Fast.interpolateCoset`, and compare with Horner evaluation of the same coefficients at
`z` in the spec field `KoalaBear.Ext4`.
-/

public meta section

namespace CompPolyTests.Fields.KoalaBear.InterpolateCoset

open CompPoly KoalaBear.Fast Montgomery.Native32

def logN : Nat := 3
def n : Nat := 2 ^ logN
def ω : Field := KoalaBear.Fast.twoAdicGenerators.getD logN 0
def s : Field := ofField 3
def z : Ext4 := ⟨ofField 5, ofField 6, ofField 7, ofField 8⟩

/-- Coefficients of the two column polynomials, low degree first. -/
def coeffs : Array (Array Nat) :=
  #[#[1, 2, 3, 4, 5, 6, 7, 8], #[2130706432, 0, 123456789, 42, 0, 0, 987654321, 5]]

def hornerBase (c : Array Nat) (x : Field) : Field :=
  c.foldr (fun (a : Nat) acc ↦ acc * x + ofField (a : KoalaBear.Field)) 0

/-- Row-major values: row `i` holds both polynomials at `s ωⁱ`. -/
def evals : Array Field := Id.run do
  let mut out := #[]
  for i in [:n] do
    let x := s * Montgomery.Native32.pow ω i
    for c in coeffs do
      out := out.push (hornerBase c x)
  return out

def hornerSpec (c : Array Nat) (x : KoalaBear.Ext4) : KoalaBear.Ext4 :=
  c.foldr (fun (a : Nat) acc ↦ acc * x + CompPoly.Extension.Ext.ofBase (a : KoalaBear.Field)) 0

def result : Array Ext4 := interpolateCoset logN ω s 2 evals z

#guard result.size == 2
#guard Ext4.toSpec result[0]! == hornerSpec coeffs[0]! (Ext4.toSpec z)
#guard Ext4.toSpec result[1]! == hornerSpec coeffs[1]! (Ext4.toSpec z)

end CompPolyTests.Fields.KoalaBear.InterpolateCoset
