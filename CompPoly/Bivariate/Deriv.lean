/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Univariate.Deriv

/-!
# Partial Derivatives of Computable Bivariate Polynomials

Defines `partialDerivX`, `partialDerivY`, iterated and mixed partial
derivatives, and the `hasMultiplicity` predicate used in Guruswami–Sudan
interpolation.
-/

namespace CompPoly

namespace CBivariate

/-- `CBivariate.coeff` as two composed `CPolynomial.coeff`. -/
@[simp]
lemma coeff_eq_coeff_coeff [Zero R] (f : CBivariate R) (i j : ℕ) :
  CBivariate.coeff f i j = CPolynomial.coeff (CPolynomial.coeff f j) i := rfl

/-- Partial derivative with respect to X: differentiate each Y-coefficient in X. -/
def partialDerivX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) : CBivariate R :=
  (CPolynomial.support f).sum fun j ↦
    CPolynomial.monomial j (CPolynomial.derivative (f.val.coeff j))

/-- Partial derivative with respect to Y: differentiate in the outer variable. -/
def partialDerivY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CBivariate R) : CBivariate R :=
  CPolynomial.derivative f

/-- Coefficient formula for the X-partial derivative. -/
theorem coeff_partialDerivX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) (i j : ℕ) :
    CBivariate.coeff (partialDerivX f) i j =
      CBivariate.coeff f (i + 1) j * (↑(i + 1) : R) := by
  unfold partialDerivX
  simp only [coeff_eq_coeff_coeff]
  erw [CPolynomial.coeff_finset_sum]
  simp only [CPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]; erw [CPolynomial.coeff_derivative]
  · intro b _ hbj; simp [Ne.symm hbj]
  · intro hj; simp only [ite_true]
    rw [CPolynomial.mem_support_iff, not_not] at hj
    change (CPolynomial.coeff f j).derivative = 0
    rw [hj]; exact CPolynomial.derivative_zero

/-- Coefficient formula for the Y-partial derivative. -/
theorem coeff_partialDerivY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f : CBivariate R) (i j : ℕ) :
    CBivariate.coeff (partialDerivY f) i j =
      CBivariate.coeff f i (j + 1) * (↑(j + 1) : R) := by
  unfold partialDerivY coeff
  simp only [CPolynomial.coeff_derivative]
  rw [(Nat.cast_commute (j + 1) (CPolynomial.coeff f (j + 1))).symm.eq,
    CPolynomial.natCast_eq_C, CPolynomial.coeff_C_mul]
  exact (Nat.cast_commute (j + 1) _).eq

/-- The X-partial derivative of zero is zero. -/
theorem partialDerivX_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] :
    partialDerivX (0 : CBivariate R) = 0 := by
  unfold partialDerivX
  convert Finset.sum_empty

/-- The Y-partial derivative of zero is zero. -/
theorem partialDerivY_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    partialDerivY (0 : CBivariate R) = 0 := by
  unfold partialDerivY
  exact CPolynomial.derivative_zero

/-- The X-partial derivative distributes over addition. -/
theorem partialDerivX_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f g : CBivariate R) :
    partialDerivX (f + g) = partialDerivX f + partialDerivX g := by
  sorry

/-- The Y-partial derivative distributes over addition. -/
theorem partialDerivY_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f g : CBivariate R) :
    partialDerivY (f + g) = partialDerivY f + partialDerivY g := by
  unfold partialDerivY
  exact CPolynomial.derivative_add f g

/-- Iterated partial derivative with respect to X. -/
def iterPartialDerivX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (n : ℕ) (f : CBivariate R) : CBivariate R :=
  n.iterate partialDerivX f

/-- Iterated partial derivative with respect to Y. -/
def iterPartialDerivY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (n : ℕ) (f : CBivariate R) : CBivariate R :=
  n.iterate partialDerivY f

/-- Mixed partial derivative: i-fold in X, then j-fold in Y. -/
def mixedPartialDeriv [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (i j : ℕ) (f : CBivariate R) : CBivariate R :=
  iterPartialDerivX i (iterPartialDerivY j f)

/-- Mixed partial derivatives commute. -/
theorem mixedPartials_comm [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (i j : ℕ) (f : CBivariate R) :
    mixedPartialDeriv i j f = mixedPartialDeriv j i f := by
  sorry

/-- A bivariate polynomial `Q` has multiplicity at least `r` at `(a, b)` if all
    mixed partial derivatives of total order less than `r` vanish at `(a, b)`. -/
def hasMultiplicity [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (r : ℕ) (a b : R) : Prop :=
  ∀ i j, i + j < r → evalEval a b (mixedPartialDeriv i j Q) = 0

/-- Decidable check for multiplicity. -/
def checkMultiplicity [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (r : ℕ) (a b : R) : Bool :=
  List.all (List.range r) fun k ↦
    List.all (List.range (k + 1)) fun i ↦
      CBivariate.evalEval a b (mixedPartialDeriv i (k - i) Q) == 0

/-- Every polynomial has multiplicity at least 0 at any point. -/
theorem hasMultiplicity_zero [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] (Q : CBivariate R) (a b : R) :
    hasMultiplicity Q 0 a b := by
  intro i j h; omega

/-- Multiplicity is monotone: higher multiplicity implies lower. -/
theorem hasMultiplicity_succ [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] (Q : CBivariate R) (r : ℕ) (a b : R) :
    hasMultiplicity Q (r + 1) a b → hasMultiplicity Q r a b := by
  intro h i j hij
  exact h i j (by omega)

end CBivariate

end CompPoly
