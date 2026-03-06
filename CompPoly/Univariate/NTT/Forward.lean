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

variable {R : Type*} [Field R] [BEq R]

/-- Input coefficients packed as a fixed-size vector over the domain. -/
@[inline] def inputVec (D : Domain R) (p : CPolynomial.Raw R) : EvalVec R D :=
  Vector.ofFn (fun i : D.Idx => p.coeff i.1)

/-- DFT/NTT formula at one output index. -/
@[inline] def nttAtVec (D : Domain R) (a : EvalVec R D) (k : D.Idx) : R :=
  ∑ j : D.Idx, a.get j * D.omega ^ ((k : Nat) * (j : Nat))

/-- Full forward transform specified directly from the NTT formula. -/
@[inline] def forwardVecSpec (D : Domain R) (a : EvalVec R D) : EvalVec R D :=
  Vector.ofFn (fun k : D.Idx => nttAtVec D a k)

/-- Spec-level forward NTT from a raw polynomial input. -/
@[inline] def forwardSpec (D : Domain R) (p : CPolynomial.Raw R) : EvalVec R D :=
  forwardVecSpec D (inputVec D p)

/-- Bit-reversal index map used by iterative Cooley-Tukey layouts. -/
def bitRevIndex (D : Domain R) (i : D.Idx) : D.Idx := by
  -- TODO: Implement bit-reversal on `D.logN` bits.
  sorry

/-- Apply bit-reversal permutation to an evaluation vector. -/
def bitRevPermute (D : Domain R) (a : EvalVec R D) : EvalVec R D := by
  -- TODO: Implement permutation using `bitRevIndex`.
  sorry

/-- One butterfly stage of the iterative radix-2 transform. -/
def butterflyStage (D : Domain R) (stage : Nat) (a : EvalVec R D) : EvalVec R D := by
  -- TODO: Implement in-place/out-of-place stage update.
  sorry

/-- Run all radix-2 butterfly stages (target complexity: `O(n log n)`). -/
def runStages (D : Domain R) (a : EvalVec R D) : EvalVec R D :=
  Nat.rec a (fun stage acc => butterflyStage D stage acc) D.logN

/-- Intended fast implementation entry point. -/
@[inline] def forwardImpl (D : Domain R) (p : CPolynomial.Raw R) : EvalVec R D :=
  runStages D (bitRevPermute D (inputVec D p))

theorem forwardImpl_correct (D : Domain R) (p : CPolynomial.Raw R) :
    forwardImpl D p = forwardSpec D p := by
  sorry

end Forward
end NTT
end CPolynomial
end CompPoly
