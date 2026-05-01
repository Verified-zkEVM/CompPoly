/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salih Erdem Koçak, Doran Pamukçu
-/
import CompPoly.Univariate.NTT.Forward
import CompPoly.Univariate.NTT.Transform

/-!
# Inverse NTT

This file provides inverse NTT APIs and correctness statement.
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
def inverseSpec (D : Domain R) (v : Array R) : Array R :=
  Array.ofFn (fun k : D.Idx => inttAt D v k)

/-- Apply the final `n⁻¹` normalization for the inverse transform. -/
def normalize (D : Domain R) (a : Array R) : Array R :=
  Array.ofFn (fun i : D.Idx => D.nInv * a.getD i.1 0)

@[simp] theorem size_inverseSpec (D : Domain R) (v : Array R) :
    (inverseSpec D v).size = D.n := by
  simp [inverseSpec]

@[simp] theorem size_normalize (D : Domain R) (a : Array R) :
    (normalize D a).size = D.n := by
  simp [normalize]

theorem normalize_forwardSpec_inverse_eq_inverseSpec (D : Domain R) (v : Array R) :
    normalize D (Forward.forwardSpec D.inverse v) = inverseSpec D v := by
  apply Array.ext
  · simp [normalize, inverseSpec, Forward.forwardSpec]
  · intro i hi₁ hi₂
    simp [normalize, inverseSpec, inttAt, Forward.forwardSpec, Forward.nttAt,
      Domain.inverse, Domain.omegaInv]
    left
    rfl

/-- Intended fast implementation entry point for inverse NTT. -/
def inverseImpl (D : Domain R) (v : Array R) : CPolynomial.Raw R :=
  normalize D (Transform.runStages D.inverse (Transform.bitRevPermute D.inverse v))

theorem inverseImpl_correct (D : Domain R) (v : Array R) :
    inverseImpl D v = inverseSpec D v := by
  rw [inverseImpl]
  change normalize D (Forward.forwardImpl D.inverse v) = inverseSpec D v
  rw [Forward.forwardImpl_correct]
  exact normalize_forwardSpec_inverse_eq_inverseSpec D v

end Inverse
end NTT
end CPolynomial
end CompPoly
