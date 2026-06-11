/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Root.ShiftedSubstitution

/-!
# Shifted Substitution Lemmas

Semantic proof surface for the generic shifted substitution. The executable
operation is available independently of these heavier algebraic facts.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- The univariate coefficient sum produced by one `Y`-coefficient in shifted
substitution composes to the corresponding binomial expansion. -/
theorem shiftedSubstitutionCoeffTerm_sum {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (coeffY f g : CPolynomial F) (t y : Nat) :
    (List.range (y + 1)).foldl
        (fun acc r ↦ acc + shiftedSubstitutionCoeffTerm coeffY f t y r * g ^ r)
        0 =
      coeffY * (f + CPolynomial.X ^ t * g) ^ y := by
  rw [list_foldl_add_eq_sum]
  rw [list_sum_map_range_eq_finset_sum]
  simp only [zero_add]
  rw [show f + CPolynomial.X ^ t * g = CPolynomial.X ^ t * g + f by ring]
  rw [add_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold shiftedSubstitutionCoeffTerm
  rw [mul_pow, pow_mul]
  rw [CPolynomial.natCast_eq_C]
  ring

/-- Composing the bivariate contribution from one `Y`-coefficient gives the
corresponding univariate shifted-substitution term. -/
theorem composeY_shiftedSubstitutionCoeffFold {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (coeffY f g : CPolynomial F) (t y : Nat) :
    CBivariate.composeY
        ((List.range (y + 1)).foldl
          (fun (out : CBivariate F) r ↦
            let contribution : CBivariate F := CPolynomial.monomial r
              (shiftedSubstitutionCoeffTerm coeffY f t y r)
            out + contribution)
          0)
        g =
      (List.range (y + 1)).foldl
        (fun acc r ↦ acc + shiftedSubstitutionCoeffTerm coeffY f t y r * g ^ r)
        0 := by
  let contribution : Nat → CBivariate F := fun r ↦
    CPolynomial.monomial r (shiftedSubstitutionCoeffTerm coeffY f t y r)
  let term : Nat → CPolynomial F := fun r ↦
    shiftedSubstitutionCoeffTerm coeffY f t y r * g ^ r
  have hfold : ∀ (rs : List Nat) (out : CBivariate F) (acc : CPolynomial F),
      CBivariate.composeY out g = acc →
        CBivariate.composeY (rs.foldl (fun out r ↦ out + contribution r) out) g =
          rs.foldl (fun acc r ↦ acc + term r) acc := by
    intro rs
    induction rs with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons r rs ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [contribution, term]
        rw [composeY_add, hacc, composeY_outer_monomial]
  exact hfold (List.range (y + 1)) 0 0 (composeY_zero g)

/-- Semantic correctness of the shifted substitution `Y = f(X) + X^t Y`. -/
theorem composeY_substituteYPolynomialPlusXPowerY {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (f g : CPolynomial F) (t : Nat) :
    CBivariate.composeY (substituteYPolynomialPlusXPowerY Q f t) g =
      CBivariate.composeY Q (f + CPolynomial.X ^ t * g) := by
  let q := f + CPolynomial.X ^ t * g
  let contribution : Nat → CBivariate F := fun y ↦
    let coeffY := Q.val.coeff y
    (List.range (y + 1)).foldl
      (fun (out : CBivariate F) r ↦
        let term : CBivariate F := CPolynomial.monomial r
          (shiftedSubstitutionCoeffTerm coeffY f t y r)
        out + term)
      0
  let coeffStep : CPolynomial F → Nat → CPolynomial F :=
    fun acc y ↦ acc + Q.val.coeff y * q ^ y
  have hfold : ∀ (ys : List Nat) (out : CBivariate F) (acc : CPolynomial F),
      CBivariate.composeY out g = acc →
        CBivariate.composeY (ys.foldl (fun out y ↦ out + contribution y) out) g =
          ys.foldl coeffStep acc := by
    intro ys
    induction ys with
    | nil =>
        intro out acc hacc
        simpa using hacc
    | cons y ys ih =>
        intro out acc hacc
        simp only [List.foldl_cons]
        apply ih
        dsimp [contribution, coeffStep, q]
        rw [composeY_add, hacc]
        rw [composeY_shiftedSubstitutionCoeffFold]
        rw [shiftedSubstitutionCoeffTerm_sum]
  unfold substituteYPolynomialPlusXPowerY
  change CBivariate.composeY
      ((List.range' 0 Q.val.size).foldl (fun out y ↦ out + contribution y) 0) g =
    CBivariate.composeY Q q
  rw [hfold (List.range' 0 Q.val.size) 0 0 (composeY_zero g)]
  rw [← composeY_eq_range_fold Q q]

end GuruswamiSudan

end CompPoly
