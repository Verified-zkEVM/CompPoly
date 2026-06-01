/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/

import CompPoly.Bivariate.Basic
import CompPoly.Bivariate.ToPoly
import CompPoly.Univariate.Deriv
import CompPoly.ToMathlib.Polynomial.BivariateMultiplicity
import Mathlib.Algebra.Polynomial.Derivative

open scoped Polynomial.Bivariate

/-!
# Partial Derivatives of Computable Bivariate Polynomials

Defines `partialDerivX`, `partialDerivY`, iterated and mixed partial
derivatives, and the `hasMultiplicity` predicate used in Guruswami–Sudan
interpolation.
-/

namespace CompPoly

namespace CPolynomial

/-- The computable Taylor shift matches `Polynomial.taylor` under `toPoly`. -/
theorem taylor_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) :
    (taylor a p).toPoly = Polynomial.taylor a p.toPoly := by
  unfold taylor
  rw [toPoly_sum, Polynomial.taylor_apply, Polynomial.comp, Polynomial.eval₂_eq_sum,
    Polynomial.sum, ← support_toPoly]
  apply Finset.sum_congr rfl
  intro m _
  rw [toPoly_mul, toPoly_pow, toPoly_add, C_toPoly, X_toPoly, C_toPoly, coeff_toPoly]

/-- The Taylor shift of zero is zero. -/
theorem taylor_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) : taylor a (0 : CPolynomial R) = 0 := by
  unfold taylor
  rw [(support_empty_iff 0).mpr rfl, Finset.sum_empty]

/-- The constant coefficient of the Taylor shift is evaluation at the shift point. -/
theorem taylor_coeff_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) : coeff (taylor a p) 0 = eval a p := by
  rw [coeff_toPoly, taylor_toPoly, Polynomial.taylor_coeff_zero, eval_toPoly]

end CPolynomial

namespace CBivariate

/-- `CBivariate.coeff` as two composed `CPolynomial.coeff`. -/
@[simp]
lemma coeff_eq_coeff_coeff [Zero R] (f : CBivariate R) (i j : ℕ) :
    CBivariate.coeff f i j = CPolynomial.coeff (CPolynomial.coeff f j) i := rfl

/-- Bivariate coefficient distributes over addition. -/
lemma coeff_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (f g : CBivariate R) (i j : ℕ) :
    CBivariate.coeff (f + g) i j = CBivariate.coeff f i j + CBivariate.coeff g i j := by
  simp only [coeff_eq_coeff_coeff]
  erw [CPolynomial.coeff_add, CPolynomial.coeff_add]

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
  unfold CBivariate
  rw [CPolynomial.eq_iff_coeff]
  intro j
  rw [CPolynomial.eq_iff_coeff]
  intro i
  simp only [← coeff_eq_coeff_coeff, coeff_partialDerivX]
  erw [coeff_add, coeff_add]
  simp only [coeff_partialDerivX]
  exact add_mul _ _ _

/-- The Y-partial derivative distributes over addition. -/
theorem partialDerivY_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f g : CBivariate R) :
    partialDerivY (f + g) = partialDerivY f + partialDerivY g := by
  unfold partialDerivY
  exact CPolynomial.derivative_add f g

/-- Outer coefficient of the X-partial derivative: differentiate the j-th Y-coefficient. -/
theorem outerCoeff_partialDerivX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) (j : ℕ) :
    CPolynomial.coeff (partialDerivX f) j =
      CPolynomial.derivative (CPolynomial.coeff f j) := by
  unfold partialDerivX
  erw [CPolynomial.coeff_finset_sum]
  simp only [CPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
  · intro b _ hbj; simp [Ne.symm hbj]
  · intro hj
    simp only [ite_true]
    rw [CPolynomial.mem_support_iff, not_not] at hj
    change (CPolynomial.coeff f j).derivative = 0
    rw [hj]; exact CPolynomial.derivative_zero

/-- The X-partial derivative differentiates each Y-coefficient under `toPoly`. -/
theorem partialDerivX_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) (j : ℕ) :
    (toPoly (partialDerivX f)).coeff j =
      Polynomial.derivative ((toPoly f).coeff j) := by
  rw [toPoly_coeff, toPoly_coeff, outerCoeff_partialDerivX]
  exact CPolynomial.derivative_toPoly _

/-- The Y-partial derivative corresponds to `Polynomial.derivative` under `toPoly`. -/
theorem partialDerivY_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) :
    toPoly (partialDerivY f) = Polynomial.derivative (toPoly f) := by
  rw [toPoly_eq_map, toPoly_eq_map]
  unfold partialDerivY
  rw [CPolynomial.derivative_toPoly]
  rw [Polynomial.derivative_map]

/-- The Y-partial derivative satisfies the Leibniz product rule. -/
theorem partialDerivY_mul [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f g : CBivariate R) :
    partialDerivY (f * g) = partialDerivY f * g + f * partialDerivY g := by
  unfold partialDerivY
  exact CPolynomial.derivative_mul f g

/-- The X-partial derivative satisfies the Leibniz product rule. -/
theorem partialDerivX_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f g : CBivariate R) :
    partialDerivX (f * g) = partialDerivX f * g + f * partialDerivX g := by
  apply CBivariate.ringEquiv.injective
  show toPoly (partialDerivX (f * g)) = toPoly (partialDerivX f * g + f * partialDerivX g)
  apply Polynomial.ext; intro j
  rw [partialDerivX_toPoly, toPoly_mul, Polynomial.coeff_mul,
    toPoly_add, Polynomial.coeff_add, toPoly_mul, toPoly_mul,
    Polynomial.coeff_mul, Polynomial.coeff_mul]
  simp_rw [partialDerivX_toPoly]
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Polynomial.derivative_mul

/-- Iterated partial derivative with respect to X. -/
def iterPartialDerivX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (n : ℕ) (f : CBivariate R) : CBivariate R :=
  n.iterate partialDerivX f

/-- Iterated partial derivative with respect to Y. -/
def iterPartialDerivY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (n : ℕ) (f : CBivariate R) : CBivariate R :=
  n.iterate partialDerivY f

/-- Iterated X-partial derivative differentiates each Y-coefficient under `toPoly`. -/
theorem iterPartialDerivX_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (n : ℕ) (f : CBivariate R) (j : ℕ) :
    (toPoly (iterPartialDerivX n f)).coeff j =
      Polynomial.derivative^[n] ((toPoly f).coeff j) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    show (toPoly (iterPartialDerivX n (partialDerivX f))).coeff j = _
    rw [ih, partialDerivX_toPoly, Function.iterate_succ, Function.comp]

/-- Iterated Y-partial derivative corresponds to `Polynomial.derivative^[n]` under `toPoly`. -/
theorem iterPartialDerivY_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (n : ℕ) (f : CBivariate R) :
    toPoly (iterPartialDerivY n f) = Polynomial.derivative^[n] (toPoly f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    show toPoly (iterPartialDerivY n (partialDerivY f)) = _
    rw [ih, partialDerivY_toPoly, Function.iterate_succ, Function.comp]

/-- Mixed partial derivative: i-fold in X, then j-fold in Y. -/
def mixedPartialDeriv [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (i j : ℕ) (f : CBivariate R) : CBivariate R :=
  iterPartialDerivX i (iterPartialDerivY j f)

/-- X and Y partial derivatives commute. -/
theorem partialDerivX_partialDerivY_comm [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] (f : CBivariate R) :
    partialDerivX (partialDerivY f) = partialDerivY (partialDerivX f) := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro j
    apply CPolynomial.eq_iff_coeff.mpr
    intro i
    simp only [← coeff_eq_coeff_coeff, coeff_partialDerivX, coeff_partialDerivY]
    rw [mul_assoc, mul_assoc]
    congr 1
    exact (Nat.cast_commute (j + 1) _).eq

/-- Mixed partial derivatives commute. -/
theorem mixedPartials_comm [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (i j : ℕ) (f : CBivariate R) :
    iterPartialDerivX i (iterPartialDerivY j f) =
      iterPartialDerivY j (iterPartialDerivX i f) := by
  exact Function.Commute.iterate_iterate
      (fun f => partialDerivX_partialDerivY_comm f) i j f

/-- Shift the outer `Y` variable: `Q(X, Y + b)`. -/
def shiftY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (b : R) (Q : CBivariate R) : CBivariate R :=
  CPolynomial.taylor (CPolynomial.C b) Q

/-- Shift the inner `X` variable: `Q(X + a, Y)`, Taylor-shifting each `Y`-coefficient. -/
def shiftX [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (Q : CBivariate R) : CBivariate R :=
  (CPolynomial.support Q).sum fun j =>
    CPolynomial.monomial j (CPolynomial.taylor a (Q.val.coeff j))

/-- The full shift `Q(X + a, Y + b)`. -/
def shiftC [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : R) (Q : CBivariate R) : CBivariate R :=
  shiftX a (shiftY b Q)


/-- `Q` has multiplicity at least `r` at `(a, b)`: every coefficient of the shifted
    polynomial `Q(X + a, Y + b)` of total degree `< r` vanishes. -/
def hasMultiplicity [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (r : ℕ) (a b : R) : Prop :=
  ∀ i j, i + j < r → CBivariate.coeff (shiftC a b Q) i j = 0

/-- Decidable check for multiplicity. -/
def checkMultiplicity [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (r : ℕ) (a b : R) : Bool :=
  List.all (List.range r) fun k ↦
    List.all (List.range (k + 1)) fun i ↦
      CBivariate.coeff (shiftC a b Q) i (k - i) == 0

/-- The outer (Y) shift corresponds to `Y ↦ Y + b` under `toPoly`. -/
theorem shiftY_toPoly [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (b : R) (Q : CBivariate R) :
    (shiftY b Q).toPoly = (Q.toPoly).comp (Polynomial.X + Polynomial.C (Polynomial.C b)) := by
  unfold shiftY
  rw [toPoly_eq_map, CPolynomial.taylor_toPoly, Polynomial.taylor_apply, Polynomial.map_comp,
    ← toPoly_eq_map]
  congr 1
  rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  congr 2
  show (CPolynomial.C b).toPoly = _
  rw [CPolynomial.C_toPoly]

/-- Outer coefficient of the X-shift: Taylor-shift the j-th Y-coefficient. -/
theorem outerCoeff_shiftX [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (P : CBivariate R) (j : ℕ) :
    CPolynomial.coeff (shiftX a P) j = CPolynomial.taylor a (CPolynomial.coeff P j) := by
  unfold shiftX
  erw [CPolynomial.coeff_finset_sum]
  simp only [CPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
  · intro b _ hbj; simp [Ne.symm hbj]
  · intro hj
    simp only [ite_true]
    rw [CPolynomial.mem_support_iff, not_not] at hj
    change CPolynomial.taylor a (CPolynomial.coeff P j) = 0
    rw [hj, CPolynomial.taylor_zero]

/-- The inner (X) shift corresponds to `X ↦ X + a` under `toPoly`. -/
theorem shiftX_toPoly [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (P : CBivariate R) :
    (shiftX a P).toPoly
      = (P.toPoly).map (Polynomial.compRingHom (Polynomial.X + Polynomial.C a)) := by
  apply Polynomial.ext
  intro j
  rw [toPoly_coeff, outerCoeff_shiftX, CPolynomial.taylor_toPoly, Polynomial.coeff_map,
    Polynomial.coe_compRingHom_apply, ← Polynomial.taylor_apply, toPoly_coeff]

/-- **Linchpin.** The computable shift matches Mathlib's `Polynomial.Bivariate.shift`,
    on which `rootMultiplicity` is built. -/
theorem shiftC_toPoly [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : R) (Q : CBivariate R) :
    (shiftC a b Q).toPoly = Polynomial.Bivariate.shift Q.toPoly a b := by
  unfold shiftC
  rw [shiftX_toPoly, shiftY_toPoly]
  rfl

/-- The (0,0) coefficient of the shift is evaluation at the point. -/
theorem coeff_shiftC_zero_zero [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : R) (Q : CBivariate R) :
    CBivariate.coeff (shiftC a b Q) 0 0 = evalEval a b Q := by
  rw [coeff_eq_coeff_coeff]
  unfold shiftC
  rw [outerCoeff_shiftX, CPolynomial.taylor_coeff_zero]
  unfold shiftY
  rw [CPolynomial.taylor_coeff_zero]
  rfl

/-- Multiplicity at least 1 is equivalent to vanishing at the point. -/
theorem hasMultiplicity_one_iff [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (Q : CBivariate R) (a b : R) :
    hasMultiplicity Q 1 a b ↔ evalEval a b Q = 0 := by
  unfold hasMultiplicity
  constructor
  · intro h; have := h 0 0 (by omega); rwa [coeff_shiftC_zero_zero] at this
  · intro h i j hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst hi; subst hj; rwa [coeff_shiftC_zero_zero]

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

/-- The decidable check agrees with the propositional multiplicity. -/
theorem hasMultiplicity_iff_check [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [DecidableEq R] (Q : CBivariate R) (r : ℕ) (a b : R) :
    hasMultiplicity Q r a b ↔ checkMultiplicity Q r a b = true := by
  unfold hasMultiplicity checkMultiplicity
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h k hk i hi
    exact h i (k - i) (by omega)
  · intro h i j hij
    have := h (i + j) (by omega) i (by omega)
    simp only [Nat.add_sub_cancel_left] at this
    exact this

end CBivariate

end CompPoly
