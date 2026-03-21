/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Data.Nat.Bitwise

/-!
# Forward NTT

This file provides spec-level forward NTT definitions together with an
iterative radix-2 implementation.
-/

open scoped BigOperators

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Forward

variable {R : Type*} [Field R]

/-- DFT/NTT formula at one output index. -/
@[inline] def nttAt (D : Domain R) (a : Array R) (k : D.Idx) : R :=
  ∑ j : D.Idx, a.getD j.1 0 * D.omega ^ ((k : Nat) * (j : Nat))

/-- Full forward transform specified directly from the NTT formula. -/
@[inline] def forwardSpec (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun k : D.Idx => nttAt D a k)

/-- Reverse the lowest `bits` bits of `i`. -/
def bitRevNat : Nat → Nat → Nat
  | 0, _ => 0
  | bits + 1, i => ((i &&& 1) <<< bits) ||| bitRevNat bits (i >>> 1)

/-- Apply bit-reversal permutation to an evaluation array. -/
def bitRevPermute (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD (bitRevNat D.logN i.1) 0)

/-- One butterfly stage of the iterative radix-2 transform. -/
def butterflyStage (D : Domain R) (stage : Nat) (a : Array R) : Array R := Id.run do
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omega ^ (D.n / blockSize)
  let mut acc := a
  for block in [0:D.n / blockSize] do
    let base := block * blockSize
    let mut w : R := 1
    for j in [0:half] do
      let i0 := base + j
      let i1 := i0 + half
      let u := acc.getD i0 0
      let t := w * acc.getD i1 0
      acc := acc.set! i0 (u + t)
      acc := acc.set! i1 (u - t)
      w := w * wm
  return acc

/-- Run all radix-2 butterfly stages (complexity: `O(n log n)`). -/
def runStages (D : Domain R) (a : Array R) : Array R := Id.run do
  let mut acc := a
  for stage in [0:D.logN] do
    acc := butterflyStage D stage acc
  return acc

/-- Intended fast implementation entry point for NTT. -/
@[inline] def forwardImpl (D : Domain R) (p : CPolynomial.Raw R) : Array R :=
  runStages D (bitRevPermute D p)

@[simp] theorem size_forwardSpec (D : Domain R) (a : Array R) :
    (forwardSpec D a).size = D.n := by
  simp [forwardSpec]

theorem forwardImpl_correct (D : Domain R) (p : CPolynomial.Raw R) :
    forwardImpl D p = forwardSpec D p := by
  -- TODO: Prove the iterative radix-2 implementation matches the direct NTT formula.
  sorry

end Forward
end NTT
end CPolynomial
end CompPoly
