/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm

/-!
# Roth-Ruckenstein Root Correctness

Correctness statements for the Roth-Ruckenstein root backend.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Soundness of Roth-Ruckenstein root filtering. -/
theorem rothRuckensteinRootsYDegreeLt_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootBackend F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (h : p ∈ (rothRuckensteinRootsYDegreeLt fieldRoots Q k).toList) :
    degreeLt p k ∧ CBivariate.composeY Q p = 0 := by
  sorry

/-- Normalizing a nonzero bivariate polynomial exposes a nonzero initial
coefficient equation for the residual-transform RR step. -/
theorem initialCoefficientPolynomial_stripXAdicFactor_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} (hQ : Q ≠ 0) :
    initialCoefficientPolynomial (CBivariate.stripXAdicFactor Q) ≠ 0 := by
  sorry

/-- Completeness of Roth-Ruckenstein root finding from a complete field-root backend.

The theorem is stated for nonzero bivariate input, matching the finite-output
root contract.
-/
theorem rothRuckensteinRootsYDegreeLt_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootBackend F}
    {Q : CBivariate F} {k : Nat} {p : CPolynomial F}
    (hQ : Q ≠ 0) (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (rothRuckensteinRootsYDegreeLt fieldRoots Q k).toList := by
  sorry

/-- Roth-Ruckenstein roots packaged with an explicit univariate field-root backend. -/
def rothRuckensteinRootBackend (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootBackend F) : GSRootBackend F where
  rootsYDegreeLt := rothRuckensteinRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    exact rothRuckensteinRootsYDegreeLt_sound h
  complete := by
    intro Q k p hQ hdegree hroot
    exact rothRuckensteinRootsYDegreeLt_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot

/-- Residual-transform Roth-Ruckenstein roots packaged as a backend. -/
def transformedRothRuckensteinRootBackend (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootBackend F) : GSRootBackend F where
  rootsYDegreeLt := transformedRothRuckensteinRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    sorry
  complete := by
    intro Q k p hQ hdegree hroot
    sorry

end GuruswamiSudan

end CompPoly
