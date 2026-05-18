/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Data.Nat.Bitwise

/-!
# Radix-2 NTTFast transform

This file defines the radix-2 transform primitives used by `NTTFast`, including
bit-reversal permutation, butterfly stages, and the stage loop.
-/

namespace CompPoly
namespace CPolynomial
namespace NTTFast
namespace Transform

variable {R : Type*} [Field R]

/-- Reverse the lowest `bits` bits of `i`. -/
def bitRevNat : Nat → Nat → Nat
  | 0, _ => 0
  | bits + 1, i => ((i &&& 1) <<< bits) ||| bitRevNat bits (i >>> 1)

/-- Apply bit-reversal permutation to an evaluation array. -/
def bitRevPermute (D : NTT.Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx ↦ a.getD (bitRevNat D.logN i.1) 0)

/-- One radix-2 butterfly update, together with the next twiddle power. -/
def butterflyInnerStep
    (blockSize half : Nat) (wm : R) (block j : Nat) (st : Array R × R) : Array R × R :=
  let acc := st.1
  let w := st.2
  let i0 := block * blockSize + j
  let i1 := i0 + half
  let u := acc.getD i0 0
  let t := w * acc.getD i1 0
  (((acc.set! i0 (u + t)).set! i1 (u - t)), w * wm)

/-- One butterfly stage of the iterative radix-2 transform. -/
def butterflyStage (D : NTT.Domain R) (stage : Nat) (a : Array R) : Array R := Id.run do
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  let mut acc := a
  for block in [0:D.n / blockSize] do
    let mut st : Array R × R := (acc, (1 : R))
    for j in [0:half] do
      st := butterflyInnerStep blockSize half wm block j st
    acc := st.1
  return acc

/-- Run all radix-2 butterfly stages. -/
def runStages (D : NTT.Domain R) (a : Array R) : Array R := Id.run do
  let mut acc := a
  for stage in [0:D.logN] do
    acc := butterflyStage D stage acc
  return acc

end Transform
end NTTFast
end CPolynomial
end CompPoly
