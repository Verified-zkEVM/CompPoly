/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.Univariate.CoefficientInterpolation
import CompPoly.Univariate.Context
import CompPoly.Univariate.Vanishing

/-!
# Divisibility-Based Interpolation Witness Checking

A fast full recognizer for the Guruswami-Sudan multiplicity constraints.

The pointwise check (`CBivariate.satisfiesMultiplicityConstraintsBool`)
evaluates every Hasse derivative of order below `m` at every interpolation
point, costing `O(n * m^2 * terms(Q))` field operations. For point sets with
distinct `x`-coordinates the same property has a module-theoretic
characterization: writing `Q = Σ_t c_t * (Y - R)^t` for the base-`(Y - R)`
expansion of `Q`, where `R` interpolates the points, `Q` has a zero of
multiplicity at least `m` at every point if and only if
`G^(m - t) ∣ c_t` for all `t < m`, with `G = Π_i (X - x_i)` the vanishing
polynomial of the `x`-coordinates.

`satisfiesMultiplicityConstraintsViaDivisibilityBool` checks the right-hand
side directly: it peels `m` digits off `Q` by synthetic division by `Y - R`
and tests each digit for divisibility by the corresponding power of `G` with
a monic remainder. With NTT-backed multiplication and remainder contexts the
whole check is quasi-linear in the input size, with no per-point loop.

`interpolationWitnessIsValidViaDivisibilityBool` combines the divisibility
check with the nonzero and weighted-degree witness conditions, mirroring
`interpolationWitnessIsValidBool`.
-/

namespace CompPoly

namespace CBivariate

/-- `divByLinearY` with the inner univariate products supplied by an explicit
multiplication context, for callers that want NTT-backed Horner steps. -/
def divByLinearYWith {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (M : CPolynomial.MulContext R) (Q : CBivariate R) (f : CPolynomial R) :
    CBivariate R × CPolynomial R :=
  let n := natDegreeY Q
  if n = 0 then (0, CPolynomial.coeff Q 0)
  else
    let a : ℕ → CPolynomial R := fun j => CPolynomial.coeff Q j
    let b_init := a n
    let (b_last, coeffs) := (List.range (n - 1)).foldl
      (fun (b, acc) k =>
        let bj := a (n - 1 - k) + M.mul f b
        (bj, acc.push bj))
      (b_init, #[b_init])
    let rem := a 0 + M.mul f b_last
    let quotArr : CPolynomial.Raw (CPolynomial R) := coeffs.reverse
    (⟨quotArr.trim, CPolynomial.Raw.Trim.isCanonical_trim quotArr⟩, rem)

/-- The context-parametric synthetic division agrees with `divByLinearY`. -/
theorem divByLinearYWith_eq_divByLinearY {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (M : CPolynomial.MulContext R) (Q : CBivariate R) (f : CPolynomial R) :
    divByLinearYWith M Q f = divByLinearY Q f := by
  unfold divByLinearYWith divByLinearY
  simp only [M.mul_eq_mul]

end CBivariate

namespace GuruswamiSudan

/-- Divisibility form of the multiplicity constraints: the digit `c_t` of the
base-`(Y - R)` expansion of `Q` must be divisible by `G^(m - t)` for every
`t < m`. The recursion peels one digit per step by synthetic division, so the
step at recursion depth `t` checks `G^(m - t) ∣ c_t` on the running quotient.

For `G` the vanishing polynomial of the (distinct) `x`-coordinates of a point
set and `R` its interpolant, this is equivalent to
`CBivariate.satisfiesMultiplicityConstraintsBool` on the same point set; see
`satisfiesMultiplicityConstraintsViaDivisibilityBool_eq`. -/
def satisfiesMultiplicityConstraintsViaDivisibilityBool {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (Mul : CPolynomial.MulContext F) (Mod : CPolynomial.ModContext F)
    (G R : CPolynomial F) : Nat → CBivariate F → Bool
  | 0, _ => true
  | m + 1, Q =>
      let step := CBivariate.divByLinearYWith Mul Q R
      Mod.modByMonic step.2 (G ^ (m + 1)) == 0 &&
        satisfiesMultiplicityConstraintsViaDivisibilityBool Mul Mod G R m step.1

/-- Divisibility-based recognizer for the semantic interpolation witness
contract, agreeing with `interpolationWitnessIsValidBool` on point sets with
distinct `x`-coordinates but avoiding its per-point Hasse derivative loop. -/
def interpolationWitnessIsValidViaDivisibilityBool {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (Mul : CPolynomial.MulContext F) (Mod : CPolynomial.ModContext F)
    (points : Array (F × F)) (params : GSInterpParams) (Q : CBivariate F) : Bool :=
  let G := V.vanishingPolynomial (points.map fun point ↦ point.1)
  let R := CPolynomial.interpolateCoefficientFormWithVanishing E G points
  !(Q == 0) &&
    decide
      (CBivariate.natWeightedDegree Q 1 (yWeight params) ≤
        params.weightedDegreeBound) &&
      satisfiesMultiplicityConstraintsViaDivisibilityBool Mul Mod G R
        params.multiplicity Q

end GuruswamiSudan

end CompPoly
