/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.Deriv
import CompPoly.Bivariate.GuruswamiSudan.Compose
import CompPoly.Bivariate.GuruswamiSudan.Polynomial
import CompPoly.LinearAlgebra.Dense

/-!
# Guruswami-Sudan Backend Contexts

Explicit executable contexts for the CompPoly Guruswami-Sudan core. The
contexts package replaceable operations together with the contracts used by the
public correctness theorems.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Parameters for the CompPoly interpolation step. -/
structure GSInterpParams where
  messageDegree : Nat
  multiplicity : Nat
  weightedDegreeBound : Nat
deriving Repr, BEq, DecidableEq

/-- The GS weighted degree uses weights `(1, messageDegree - 1)`. -/
def yWeight (params : GSInterpParams) : Nat :=
  params.messageDegree - 1

/-- `p.degree < k`, treating the zero polynomial as degree `bot`. -/
def degreeLt {F : Type*} [Zero F] (p : CPolynomial F) (k : Nat) : Prop :=
  p.degree < (k : WithBot Nat)

/-- Packed input points have no duplicate `x`-coordinates. -/
def DistinctXCoordinates {F : Type*} (points : Array (Prod F F)) : Prop :=
  (points.toList.map fun point ↦ point.1).Nodup

/-- Semantic interpolation witness used by backend contracts and core
completeness statements. -/
def ValidInterpolationWitness {F : Type*}
    [CommSemiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (points : Array (Prod F F)) (params : GSInterpParams) (Q : CBivariate F) : Prop :=
  Q ≠ 0 ∧
    CBivariate.natWeightedDegree Q 1 (yWeight params) ≤ params.weightedDegreeBound ∧
      ∀ point, point ∈ points.toList →
        CBivariate.hasMultiplicity Q params.multiplicity point.1 point.2

/-- A dense homogeneous linear-kernel backend.

The operation returns a nonzero kernel witness in the backend's chosen
normalization when it can find one. Completeness is stated in the negative form
needed by dense interpolation systems: if no witness is returned, no nonzero
homogeneous solution exists.
-/
structure LinearKernelContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  homogeneousWitness : DenseMatrix F → Option (Array F)
  witness_width :
    ∀ {M : DenseMatrix F} {v : Array F},
      homogeneousWitness M = some v →
        DenseMatrix.VectorWidth M v
  witness_sound :
    ∀ {M : DenseMatrix F} {v : Array F},
      DenseMatrix.WellFormed M →
        homogeneousWitness M = some v →
          DenseMatrix.IsHomogeneousSolution M v
  witness_nonzero :
    ∀ {M : DenseMatrix F} {v : Array F},
      homogeneousWitness M = some v →
        DenseMatrix.NonzeroVector v
  witness_complete :
    ∀ {M : DenseMatrix F},
      DenseMatrix.WellFormed M →
        homogeneousWitness M = none →
          ∀ v,
            DenseMatrix.VectorWidth M v →
              DenseMatrix.IsHomogeneousSolution M v →
                ¬ (DenseMatrix.NonzeroVector v)

/-- The dense Gaussian-elimination homogeneous-kernel backend. -/
def denseLinearKernelContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] :
    LinearKernelContext F where
  homogeneousWitness := DenseMatrix.homogeneousWitness
  witness_width := by
    intro M v h
    exact DenseMatrix.homogeneousWitness_width h
  witness_sound := by
    intro M v hM h
    exact (DenseMatrix.homogeneousWitness_sound hM h).2.1
  witness_nonzero := by
    intro M v h
    exact DenseMatrix.homogeneousWitness_nonzero h
  witness_complete := by
    intro M hM h v hvw hv
    exact DenseMatrix.homogeneousWitness_none_complete hM h v hvw hv

/-- Guruswami-Sudan-facing interpolation backend.

The backend packages the executable interpolation operation together with the
contract fields used by callers, using the explicit context style used by
univariate multiplication and remainder backends.
-/
structure GSInterpContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] where
  interpolate : Array (Prod F F) → GSInterpParams → Option (CBivariate F)
  sound :
    ∀ points params Q,
      interpolate points params = some Q →
        ValidInterpolationWitness points params Q
  complete :
    ∀ points params,
      DistinctXCoordinates points →
      (exists Q, ValidInterpolationWitness points params Q) →
        exists Q, interpolate points params = some Q

/-- Executable root finder for univariate field polynomials.

Completeness is only required for nonzero polynomials. A zero univariate
polynomial vanishes on every field element, so an unconditional array-valued
complete root finder would have to enumerate the whole field.
-/
structure FieldRootContext (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  rootsInField : CPolynomial F → Array F
  sound :
    ∀ p a,
      a ∈ (rootsInField p).toList →
        CPolynomial.eval a p = 0
  complete :
    ∀ p a,
      p ≠ 0 →
      CPolynomial.eval a p = 0 →
        a ∈ (rootsInField p).toList

/-- Guruswami-Sudan-facing bounded-degree root backend.

Completeness is only required for nonzero bivariate input. The zero bivariate
polynomial has every degree-bounded univariate polynomial as a root, which is not
a finite output contract for large fields.
-/
structure GSRootContext (F : Type*) [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] where
  rootsYDegreeLt : CBivariate F → Nat → Array (CPolynomial F)
  sound :
    ∀ Q k p,
      p ∈ (rootsYDegreeLt Q k).toList →
        degreeLt p k ∧ CBivariate.composeY Q p = 0
  complete :
    ∀ Q k p,
      Q ≠ 0 →
      degreeLt p k →
      CBivariate.composeY Q p = 0 →
        p ∈ (rootsYDegreeLt Q k).toList

end GuruswamiSudan

end CompPoly
