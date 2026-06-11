/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Polynomial

/-!
# Shifted Substitution for Guruswami-Sudan Root Search

Executable substitution of `Y = f(X) + X^t Y` in bivariate polynomials.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Multiply a univariate polynomial by `X^t`. -/
def shiftPolynomialByXPower {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (p : CPolynomial F) (t : Nat) : CPolynomial F :=
  CPolynomial.X ^ t * p

/-- The contribution of one `Y^y` coefficient to `Y^r` after substituting
`Y = f(X) + X^t Y`. -/
def shiftedSubstitutionCoeffTerm {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (coeffY f : CPolynomial F) (t y r : Nat) : CPolynomial F :=
  coeffY * CPolynomial.C (Nat.choose y r : F) * f ^ (y - r) *
    CPolynomial.X ^ (t * r)

/-- Substitute `Y = f(X) + X^t Y` into a bivariate polynomial. -/
def substituteYPolynomialPlusXPowerY {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) (t : Nat) : CBivariate F :=
  (List.range' 0 Q.val.size).foldl
    (fun (out : CBivariate F) (y : Nat) ↦
      let coeffY := Q.val.coeff y
      out + (List.range (y + 1)).foldl
        (fun (out : CBivariate F) (r : Nat) ↦
          let contribution : CBivariate F := CPolynomial.monomial r
            (shiftedSubstitutionCoeffTerm coeffY f t y r)
          out + contribution)
        0)
    (0 : CBivariate F)

/-- Truncated substitution `Y = f(X) + X^t Y`, keeping only `X`-degree `< N`
after each accumulated `Y`-coefficient contribution. -/
def substituteYPolynomialPlusXPowerYTruncated {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f : CPolynomial F) (t N : Nat) : CBivariate F :=
  (List.range' 0 Q.val.size).foldl
    (fun (out : CBivariate F) (y : Nat) ↦
      let coeffY := Q.val.coeff y
      (List.range (y + 1)).foldl
        (fun (out : CBivariate F) (r : Nat) ↦
          let term := CPolynomial.truncate
            (shiftedSubstitutionCoeffTerm coeffY f t y r) N
          let contribution : CBivariate F := CPolynomial.monomial r term
          CBivariate.truncateX (out + contribution) N)
        out)
    (0 : CBivariate F)

end GuruswamiSudan

end CompPoly
