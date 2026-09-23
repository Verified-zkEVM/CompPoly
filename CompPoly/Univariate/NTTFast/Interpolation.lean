/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import CompPoly.Univariate.NTT.Interpolation
public import CompPoly.Univariate.NTTFast.Correctness.Pipeline

/-!
# NTTFast and Interpolation

Bridge theorem declarations deriving NTTFast interpolation facts from the shared
NTT specification layer.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

namespace Plan

/--
A well-formed planned inverse interpolates the natural-order values when called on
the corresponding bit-reversed value array.
-/
theorem inverseImpl_interpolatePow_eq [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (values : Array R) :
    CPolynomial.Raw.trim (inverseImpl P (NTT.Transform.bitRevPermute P.domain values)) =
      (CLagrange.interpolatePow P.domain.omega
        (NTT.loadNaturalVector P.domain values)).val := by
  rw [inverseImpl_correct P hP values]
  exact NTT.Inverse.inverseSpec_interpolatePow_eq P.domain values

/-- Pointwise form of `inverseImpl_interpolatePow_eq` for a well-formed planned inverse. -/
theorem inverseImpl_eval_node_eq
    (P : Plan R) (hP : WellFormed P) (values : Array R) (k : P.domain.Idx) :
    CPolynomial.Raw.eval (P.domain.node k)
      (inverseImpl P (NTT.Transform.bitRevPermute P.domain values)) = values.getD k.1 0 := by
  rw [inverseImpl_correct P hP values]
  exact NTT.Inverse.inverseSpec_eval_node_eq P.domain values k

/-- A well-formed planned inverse evaluates back to the natural-order input values. -/
theorem inverseImpl_evalOnDomain_eq
    (P : Plan R) (hP : WellFormed P) (values : Array R) :
    NTT.evalOnDomain P.domain (inverseImpl P (NTT.Transform.bitRevPermute P.domain values)) =
      NTT.loadNaturalArray P.domain values := by
  rw [inverseImpl_correct P hP values]
  exact NTT.Inverse.inverseSpec_evalOnDomain_eq P.domain values

/-- Interpolate natural-order values on the plan's domain with the cached inverse transform.

The planned counterpart of `NTT.interpolate`: for a well-formed plan it is
`CLagrange.interpolatePow` on the domain root (`interpolate_eq_interpolatePow`). -/
def interpolate [BEq R] [LawfulBEq R] (P : Plan R) (values : Vector R P.domain.n) :
    CPolynomial R :=
  let raw := inverseImpl P (NTT.Transform.bitRevPermute P.domain values.toArray)
  ⟨raw.trim, CPolynomial.Raw.Trim.isCanonical_trim raw⟩

/-- A well-formed plan's interpolation agrees with the unplanned `NTT.interpolate`. -/
theorem interpolate_eq_ntt_interpolate [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (values : Vector R P.domain.n) :
    interpolate P values = NTT.interpolate P.domain values := by
  apply Subtype.ext
  simp only [interpolate, NTT.interpolate, inverseImpl_correct P hP,
    NTT.Inverse.inverseImpl_correct]

/-- A well-formed plan interpolates by Lagrange's formula on the powers of the domain root. -/
theorem interpolate_eq_interpolatePow [BEq R] [LawfulBEq R]
    (P : Plan R) (hP : WellFormed P) (values : Vector R P.domain.n) :
    interpolate P values = CLagrange.interpolatePow P.domain.omega values := by
  rw [interpolate_eq_ntt_interpolate P hP, NTT.interpolate_eq_interpolatePow]

end Plan
end NTTFast
end CPolynomial
end CompPoly
