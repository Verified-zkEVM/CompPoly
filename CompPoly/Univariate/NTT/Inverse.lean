/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
import CompPoly.Univariate.NTT.Domain
import CompPoly.Univariate.NTT.Forward

/-!
# Inverse NTT Scaffolding

This file provides placeholder inverse NTT APIs and correctness statement
targets for future implementation/proofs.
-/

open scoped BigOperators

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Inverse

variable {R : Type*} [Field R]

/-- Inverse NTT formula at one output index. -/
def inttAt (D : Domain R) (v : Array R) (k : D.Idx) : R :=
  D.nInv * ∑ j : D.Idx, v.getD j.1 0 * D.omegaInv ^ ((k : Nat) * (j : Nat))

/-- Full inverse transform on arrays, specified from `inttAt`. -/
def inverseArraySpec (D : Domain R) (v : Array R) : Array R :=
  Array.ofFn (fun k : D.Idx => inttAt D v k)

/-- Convert inverse-transform output array back to raw polynomial coefficients. -/
def inverseSpec (D : Domain R) (v : Array R) : CPolynomial.Raw R :=
  -- TODO: Revisit whether inverse output should be normalized/truncated here or at call sites.
  inverseArraySpec D v

/-- Apply bit-reversal permutation to an evaluation array. -/
def bitRevPermute (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => a.getD (Forward.bitRevNat D.logN i.1) 0)

/-- One butterfly stage of the iterative radix-2 inverse transform. -/
def butterflyStage (D : Domain R) (stage : Nat) (a : Array R) : Array R := Id.run do
  let blockSize : Nat := 2 ^ (stage + 1)
  let half : Nat := 2 ^ stage
  let wm := D.omegaInv ^ (D.n / blockSize)
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

/-- Run all radix-2 inverse butterfly stages. -/
def runStages (D : Domain R) (a : Array R) : Array R := Id.run do
  let mut acc := a
  for stage in [0:D.logN] do
    acc := butterflyStage D stage acc
  return acc

/-- Apply the final `n⁻¹` normalization for the inverse transform. -/
def normalize (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => D.nInv * a.getD i.1 0)

@[simp] theorem size_inverseArraySpec (D : Domain R) (v : Array R) :
    (inverseArraySpec D v).size = D.n := by
  simp [inverseArraySpec]

@[simp] theorem size_inverseSpec (D : Domain R) (v : Array R) :
    (inverseSpec D v).size = D.n := by
  simp [inverseSpec]

@[simp] theorem size_normalize (D : Domain R) (a : Array R) :
    (normalize D a).size = D.n := by
  simp [normalize]

/-- Placeholder inverse implementation returning coefficients. -/
def inverseImpl (D : Domain R) (v : Array R) : CPolynomial.Raw R :=
  normalize D (runStages D (bitRevPermute D v))

theorem inverseImpl_correct (D : Domain R) (v : Array R) :
    inverseImpl D v = inverseSpec D v := by
  -- TODO: Prove the iterative radix-2 inverse implementation matches the direct formula.
  sorry

end Inverse
end NTT
end CPolynomial
end CompPoly
