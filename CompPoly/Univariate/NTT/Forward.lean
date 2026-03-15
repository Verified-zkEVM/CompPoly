/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
import CompPoly.Univariate.NTT.Domain

/-!
# Forward NTT Scaffolding

This file provides spec-level forward NTT definitions together with placeholder
hooks for a future iterative radix-2 implementation.
-/

open scoped BigOperators

namespace CompPoly
namespace CPolynomial
namespace NTT
namespace Forward

variable {R : Type*} [Field R]

/-- Input coefficients packed as a fixed-size array over the domain. -/
@[inline] def inputArray (D : Domain R) (p : CPolynomial.Raw R) : Array R :=
  Array.ofFn (fun i : D.Idx => p.coeff i.1)

/-- DFT/NTT formula at one output index. -/
@[inline] def nttAt (D : Domain R) (a : Array R) (k : D.Idx) : R :=
  ∑ j : D.Idx, a.getD j.1 0 * D.omega ^ ((k : Nat) * (j : Nat))

/-- Full forward transform specified directly from the NTT formula. -/
@[inline] def forwardArraySpec (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun k : D.Idx => nttAt D a k)

/-- Spec-level forward NTT from a raw polynomial input. -/
@[inline] def forwardSpec (D : Domain R) (p : CPolynomial.Raw R) : Array R :=
  forwardArraySpec D (inputArray D p)

/-- Bit-reversal index map used by iterative Cooley-Tukey layouts. -/
def bitRevIndex (D : Domain R) (i : D.Idx) : D.Idx := by
  -- TODO: Implement bit-reversal on `D.logN` bits.
  sorry

/-- Apply bit-reversal permutation to an evaluation array. -/
def bitRevPermute (D : Domain R) (a : Array R) : Array R := by
  -- TODO: Implement permutation using `bitRevIndex`.
  sorry

/-- One butterfly stage of the iterative radix-2 transform. -/
def butterflyStage (D : Domain R) (stage : Nat) (a : Array R) : Array R := by
  -- TODO: Implement in-place/out-of-place stage update.
  sorry

/-- Run all radix-2 butterfly stages (target complexity: `O(n log n)`). -/
def runStages (D : Domain R) (a : Array R) : Array R :=
  Nat.rec a (fun stage acc => butterflyStage D stage acc) D.logN

/-- Intended fast implementation entry point. -/
@[inline] def forwardImpl (D : Domain R) (p : CPolynomial.Raw R) : Array R :=
  -- TODO: Replace this spec call with `runStages D (bitRevPermute D (inputArray D p))`
  -- once the dedicated radix-2 implementation is ready.
  forwardSpec D p

@[simp] theorem size_inputArray (D : Domain R) (p : CPolynomial.Raw R) :
    (inputArray D p).size = D.n := by
  simp [inputArray]

@[simp] theorem size_forwardArraySpec (D : Domain R) (a : Array R) :
    (forwardArraySpec D a).size = D.n := by
  simp [forwardArraySpec]

@[simp] theorem size_forwardSpec (D : Domain R) (p : CPolynomial.Raw R) :
    (forwardSpec D p).size = D.n := by
  simp [forwardSpec]

theorem forwardImpl_correct (D : Domain R) (p : CPolynomial.Raw R) :
    forwardImpl D p = forwardSpec D p := by
  rfl

end Forward
end NTT
end CPolynomial
end CompPoly
