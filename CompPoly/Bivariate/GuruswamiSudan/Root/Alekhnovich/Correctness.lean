/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Lemmas

/-!
# Alekhnovich Root Search Correctness

Public correctness surface for the Alekhnovich bounded bivariate root backend.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Soundness of Alekhnovich root filtering. -/
theorem alekhnovichRootsYDegreeLt_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (h : p ∈ (alekhnovichRootsYDegreeLt fieldRoots Q k).toList) :
    degreeLt p k ∧ CBivariate.composeY Q p = 0 := by
  rw [alekhnovichRootsYDegreeLt] at h
  by_cases hzero : Q == 0
  · simp [hzero] at h
  · exact rootsYDegreeLtFromCandidates_eraseDups_sound (by
      simpa [hzero] using h)

/-- The exact final filter keeps any true bounded root that the Alekhnovich
candidate generator has already produced. -/
theorem alekhnovichRootsYDegreeLt_complete_of_candidate_mem {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (hQ : Q ≠ 0)
    (hmem : p ∈ (alekhnovichRootCandidates fieldRoots Q k).toList)
    (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootsYDegreeLt fieldRoots Q k).toList := by
  rw [alekhnovichRootsYDegreeLt]
  have hzero : (Q == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hQ (beq_iff_eq.mp htrue)
  rw [hzero]
  exact rootsYDegreeLtFromCandidates_eraseDups_complete_of_mem
    hmem hdegree hroot

/-- Shifted substitution preserves modular roots below `N` before truncation. -/
theorem RootMod.substituteYPolynomialPlusXPowerY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {f g : CPolynomial F} {t N : Nat}
    (hroot : RootMod Q (f + shiftPolynomialByXPower g t) N) :
    RootMod (substituteYPolynomialPlusXPowerY Q f t) g N := by
  intro i hi
  rw [composeY_substituteYPolynomialPlusXPowerY]
  simpa [shiftPolynomialByXPower] using hroot i hi

/-- Truncated shifted substitution has the same coefficients below `N` as exact
shifted substitution, so it preserves modular roots below `N`. -/
theorem RootMod.substituteYPolynomialPlusXPowerYTruncated {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {f g : CPolynomial F} {t N : Nat}
    (hroot : RootMod Q (f + shiftPolynomialByXPower g t) N) :
    RootMod (substituteYPolynomialPlusXPowerYTruncated Q f t N) g N := by
  sorry

/-- Stripping a visible `X`-adic valuation transports a modular root of `Q` to
a shorter modular root of the stripped residual. -/
theorem RootMod.stripXAdicFactor {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {s N : Nat}
    (horder : CBivariate.xAdicOrder? Q = some s)
    (hroot : RootMod Q p (s + N)) :
    RootMod (CBivariate.stripXAdicFactor Q) p N := by
  sorry

/-- Recursive Alekhnovich prefix coverage for modular roots. -/
theorem alekhnovichRootPrefixesWithFuel_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {N fuel : Nat}
    {p : CPolynomial F}
    (hfuel : N < fuel)
    (hroot : RootMod Q p N) :
    ∃ rootPrefix,
      rootPrefix ∈ (alekhnovichRootPrefixesWithFuel fieldRoots fuel Q N).toList ∧
        MatchesRootPrefix p rootPrefix ∧
          N ≤ rootPrefix.precision := by
  sorry

/-- Candidate generation coverage for the Alekhnovich-only recursive suffix
completion. -/
theorem alekhnovichRootCandidatesWithFuel_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k fuel : Nat}
    {p : CPolynomial F}
    (hfuel : k < fuel)
    (hQ : Q ≠ 0)
    (hdegree : degreeLt p k)
    (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootCandidatesWithFuel fieldRoots fuel Q k).toList := by
  sorry

/-- The finite modular-root predicate is exact once the substitution degree is
bounded below the checked precision. -/
theorem composeY_eq_zero_of_rootMod_of_substitutionDegreeBound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F]
    {Q : CBivariate F} {p : CPolynomial F} {k N : Nat}
    (hbound : SubstitutionDegreeBound Q k N)
    (hdegree : degreeLt p k)
    (hroot : RootMod Q p N) :
    CBivariate.composeY Q p = 0 := by
  sorry

/-- Completeness of Alekhnovich candidate generation for exact bounded roots. -/
theorem alekhnovichRootCandidates_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F} {Q : CBivariate F} {k : Nat}
    {p : CPolynomial F}
    (hQ : Q ≠ 0)
    (hdegree : degreeLt p k)
    (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootCandidates fieldRoots Q k).toList := by
  unfold alekhnovichRootCandidates
  exact alekhnovichRootCandidatesWithFuel_complete
    (fieldRoots := fieldRoots) (Q := Q) (k := k) (fuel := k + 1) (p := p)
    (by omega) hQ hdegree hroot

/-- Completeness of Alekhnovich bounded-degree root finding from a complete
field-root backend. -/
theorem alekhnovichRootsYDegreeLt_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {fieldRoots : FieldRootContext F}
    {Q : CBivariate F} {k : Nat} {p : CPolynomial F}
    (hQ : Q ≠ 0) (hdegree : degreeLt p k) (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (alekhnovichRootsYDegreeLt fieldRoots Q k).toList :=
  alekhnovichRootsYDegreeLt_complete_of_candidate_mem hQ
    (alekhnovichRootCandidates_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot)
    hdegree hroot

/-- Alekhnovich roots packaged with an explicit univariate field-root backend. -/
def alekhnovichRootContext (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (fieldRoots : FieldRootContext F) : GSRootContext F where
  rootsYDegreeLt := alekhnovichRootsYDegreeLt fieldRoots
  sound := by
    intro Q k p h
    exact alekhnovichRootsYDegreeLt_sound h
  complete := by
    intro Q k p hQ hdegree hroot
    exact alekhnovichRootsYDegreeLt_complete
      (fieldRoots := fieldRoots) hQ hdegree hroot

end GuruswamiSudan

end CompPoly
