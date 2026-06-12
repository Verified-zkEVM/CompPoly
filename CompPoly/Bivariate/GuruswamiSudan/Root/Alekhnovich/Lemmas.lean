/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Root.ShiftedSubstitution.Lemmas

/-!
# Alekhnovich Root Search Lemmas

Proof support for the Alekhnovich bounded bivariate root backend.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- `p` is a root of `Q` modulo `X^N`, stated as finitely many coefficient
equalities. -/
def RootMod {F : Type*}
    [Semiring F] [BEq F] [LawfulBEq F] [Nontrivial F]
    (Q : CBivariate F) (p : CPolynomial F) (N : Nat) : Prop :=
  ∀ i, i < N → (CBivariate.composeY Q p).coeff i = 0

/-- `f` matches the first `t` coefficients of `p`. -/
def MatchesPrefix {F : Type*} [Zero F] [BEq F] [LawfulBEq F]
    (p f : CPolynomial F) (t : Nat) : Prop :=
  polynomialPrefix p t = f

/-- `rp` is a root-prefix record matching the first `rp.precision` coefficients
of `p`. -/
def MatchesRootPrefix {F : Type*} [Zero F] [BEq F] [LawfulBEq F]
    (p : CPolynomial F) (rp : RootPrefix F) : Prop :=
  MatchesPrefix p rp.prefixPoly rp.precision

/-- Logical exactness bound for substituting any `degree < k` univariate
polynomial into `Q`. -/
def SubstitutionDegreeBound {F : Type*} [Zero F] [BEq F]
    (Q : CBivariate F) (k N : Nat) : Prop :=
  ∀ j, j < Q.val.size → (Q.val.coeff j).natDegree + j * (k - 1) < N

end GuruswamiSudan

end CompPoly
