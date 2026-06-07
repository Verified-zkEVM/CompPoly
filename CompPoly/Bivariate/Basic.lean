/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen, Dimitris Mitsios
-/

import CompPoly.Univariate.Basic

/-!
# Computable Bivariate Polynomials

This file defines `CBivariate R`, the computable representation of bivariate polynomials with
coefficients in `R`. The type is `CPolynomial (CPolynomial R)`, i.e. polynomials in `Y` with
coefficients that are polynomials in `X`, matching Mathlib's `R[X][Y]`
(i.e. `Polynomial (Polynomial R)`).

The design is intended to be compatible with:
- Mathlib's `Polynomial.Bivariate` (see `CompPoly/Bivariate/ToPoly.lean`)
- ArkLib's `Polynomial.Bivariate` interface (see ArkLib/Data/Polynomial/Bivariate.lean and
  ArkLib/Data/CodingTheory/PolishchukSpielman/Degrees.lean, BCIKS20.lean, etc.)
-/

namespace CompPoly

/-- Computable bivariate polynomials: `F[X][Y]` as `CPolynomial (CPolynomial R)`.

  Each `p : CBivariate R` is a polynomial in `Y` whose coefficients are univariate polynomials
  in `X`. The outer structure is indexed by powers of `Y`, the inner by powers of `X`.
  -/
def CBivariate (R : Type*) [Zero R] :=
    CPolynomial (CPolynomial R)

namespace CBivariate

section ZeroOnly

variable {R : Type*} [Zero R]

/-- Extensionality: two bivariate polynomials are equal if their underlying values are. -/
@[ext] theorem ext {p q : CBivariate R} (h : p.val = q.val) : p = q :=
  CPolynomial.ext h

/-- Coerce to the underlying univariate polynomial (in Y) with polynomial coefficients. -/
instance : Coe (CBivariate R) (CPolynomial (CPolynomial R)) where coe := id

/-- The zero bivariate polynomial is canonical. -/
instance : Inhabited (CBivariate R) := inferInstanceAs (Inhabited (CPolynomial (CPolynomial R)))

instance [BEq R] : BEq (CBivariate R) :=
  inferInstanceAs (BEq (CPolynomial (CPolynomial R)))

instance [BEq R] [LawfulBEq R] : LawfulBEq (CBivariate R) :=
  inferInstanceAs (LawfulBEq (CPolynomial (CPolynomial R)))

instance [DecidableEq R] : DecidableEq (CBivariate R) :=
  inferInstanceAs (DecidableEq (CPolynomial (CPolynomial R)))

end ZeroOnly

section Semiring

variable {R : Type*}
variable [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Additive structure on CBivariate R -/
instance : AddCommMonoid (CBivariate R) :=
  inferInstanceAs (AddCommMonoid (CPolynomial (CPolynomial R)))

/-- Ring structure on CBivariate R (for ring equiv with Mathlib in ToPoly). -/
instance : Semiring (CBivariate R) :=
  inferInstanceAs (Semiring (CPolynomial (CPolynomial R)))

end Semiring

section CommSemiring

variable {R : Type*}
variable [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

instance : CommSemiring (CBivariate R) :=
  inferInstanceAs (CommSemiring (CPolynomial (CPolynomial R)))

end CommSemiring

section Ring

variable {R : Type*}
variable [Ring R] [BEq R] [LawfulBEq R] [Nontrivial R]

instance : Ring (CBivariate R) :=
  inferInstanceAs (Ring (CPolynomial (CPolynomial R)))

end Ring

section CommRing

variable {R : Type*}
variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

instance : CommRing (CBivariate R) :=
  inferInstanceAs (CommRing (CPolynomial (CPolynomial R)))

end CommRing

-- ---------------------------------------------------------------------------
-- Operation stubs (for ArkLib compatibility; proofs deferred)
-- ---------------------------------------------------------------------------
-- ArkLib's Polynomial.Bivariate uses: coeff, natDegreeY, degreeX, totalDegree,
-- evalX, evalY, leadingCoeffY, swap. These will be implemented and proven
-- equivalent to Mathlib/ArkLib via ToPoly.lean.
-- TODO: Add bridge lemmas/equivalences between `CBivariate R` and
--   `CMvPolynomial 2 R` for interoperability with the multivariate API.
-- ---------------------------------------------------------------------------

section Operations

/-- Constant as a bivariate polynomial. Mathlib: `Polynomial.Bivariate.CC`. -/
def CC {R : Type*} [Zero R] [BEq R] [LawfulBEq R] (r : R) : CBivariate R :=
  CPolynomial.C (CPolynomial.C r)

/-- The variable X (inner variable). As bivariate: polynomial in Y with single coeff `X` at Y^0. -/
def X {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : CBivariate R :=
  CPolynomial.C CPolynomial.X

/-- The variable Y (outer variable). Monomial `Y^1` with coefficient 1. -/
def Y {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R] :
    CBivariate R :=
  CPolynomial.monomial 1 (CPolynomial.C 1)

/-- Monomial `c * X^n * Y^m`. ArkLib: `Polynomial.Bivariate.monomialXY`. -/
def monomialXY {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (n m : ℕ) (c : R) : CBivariate R :=
  CPolynomial.monomial m (CPolynomial.monomial n c)

/-- Coefficient of `X^i Y^j` in the bivariate polynomial. Here `i` is the X-exponent (inner)
    and `j` is the Y-exponent (outer). ArkLib: `Polynomial.Bivariate.coeff f i j`. -/
def coeff {R : Type*} [Zero R] (f : CBivariate R) (i j : ℕ) : R :=
  (f.val.coeff j).coeff i

/-- The Y-support: indices j such that the coefficient of Y^j is nonzero. -/
def supportY {R : Type*} [Zero R] [BEq R] (f : CBivariate R) : Finset ℕ := CPolynomial.support f

/-- The X-support: indices i such that the coefficient of X^i is nonzero
    (i.e. some monomial X^i Y^j has nonzero coefficient). -/
def supportX {R : Type*} [Zero R] [BEq R] (f : CBivariate R) : Finset ℕ :=
  (CPolynomial.support f).biUnion (fun j ↦ CPolynomial.support (f.val.coeff j))

/-- The `Y`-degree (degree when viewed as a polynomial in `Y`).
    ArkLib: `Polynomial.Bivariate.natDegreeY`. -/
def natDegreeY {R : Type*} [Zero R] (f : CBivariate R) : ℕ :=
  f.natDegree

/-- The `X`-degree: maximum over all Y-coefficients of their degree in X.
    ArkLib: `Polynomial.Bivariate.natDegreeX`. -/
def natDegreeX {R : Type*} [Zero R] [BEq R] (f : CBivariate R) : ℕ :=
  (CPolynomial.support f).sup (fun n ↦ (f.val.coeff n).natDegree)

/-- Total degree: max over monomials of (deg_X + deg_Y).
    ArkLib: `Polynomial.Bivariate.totalDegree`. -/
def totalDegree {R : Type*} [Zero R] [BEq R] (f : CBivariate R) : ℕ :=
  (CPolynomial.support f).sup (fun m ↦ (f.val.coeff m).natDegree + m)

/-- The `(u, v)`-weighted degree: max over monomials of `u * deg_X + v * deg_Y`. -/
def natWeightedDegree {R : Type*} [Zero R] [BEq R] (f : CBivariate R) (u v : ℕ) : ℕ :=
  (CPolynomial.support f).sup (fun m ↦ u * (f.val.coeff m).natDegree + v * m)

/-- Evaluate in the first variable (X) at `a`, yielding a univariate polynomial in Y.
    ArkLib: `Polynomial.Bivariate.evalX`. -/
def evalX {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (a : R) (f : CBivariate R) : CPolynomial R :=
  (CPolynomial.support f).sum (fun j ↦ CPolynomial.monomial j (CPolynomial.eval a (f.val.coeff j)))

/-- Evaluate in the second variable (Y) at `a`, yielding a univariate polynomial in X.
    ArkLib: `Polynomial.Bivariate.evalY`.

    Folds the Y-coefficients of `f` with a raw Horner pattern (`smulRight a` then
    `addRaw`), trimming once at the end. This avoids paying one `CPolynomial.mul`
    and one `CPolynomial.add` trim per Y-coefficient. -/
def evalY {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a : R) (f : CBivariate R) : CPolynomial R :=
  ⟨(f.val.foldr
      (fun (c : CPolynomial R) (acc : CPolynomial.Raw R) =>
        (acc.smulRight a).addRaw c.val)
      (CPolynomial.Raw.mk #[])).trim,
   CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- Evaluate in the second variable (Y) at `a` using Horner's method,
    yielding a univariate polynomial in X. -/
def evalYHorner {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a : R) (p : CBivariate R) : CPolynomial R :=
  CPolynomial.evalHorner (CPolynomial.C a) p

/-- Full evaluation at `(x, y)`: `p(x, y)`. Inner variable X at `x`, outer variable Y at `y`.
    Equivalently `(evalY y f).eval x`. Mathlib: `Polynomial.evalEval`.

    See `CBivariate.eval_y_horner_eq_eval_y` in `CompPoly/Bivariate/ToPoly.lean` for
    agreement between `evalY` and `evalYHorner`. -/
def evalEval {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x y : R) (f : CBivariate R) : R :=
  CPolynomial.eval x (evalY y f)

/-- Full evaluation at `(x, y)` using Horner in Y, then Horner in X on the
    intermediate univariate polynomial. -/
def evalEvalHornerYThenX {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x y : R) (p : CBivariate R) : R :=
  CPolynomial.evalHorner x (evalYHorner y p)

/-- Full evaluation at `(x, y)` by evaluating each X-coefficient polynomial at
    `x`, then Horner-evaluating the resulting scalar polynomial in Y. -/
def evalEvalHornerXThenY {R : Type*} [Semiring R] (x y : R) (p : CBivariate R) : R :=
  p.val.foldr (fun c acc ↦ acc * y + CPolynomial.evalHorner x c) 0

/-- Swap the roles of X and Y.
    ArkLib/Mathlib: `Polynomial.Bivariate.swap`.
    TODO a more efficient implementation
    -/
def swap {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) : CBivariate R :=
  (f.supportY).sum (fun j ↦
    (CPolynomial.support (f.val.coeff j)).sum (fun i ↦
      CPolynomial.monomial i (CPolynomial.monomial j ((f.val.coeff j).coeff i))))

/-- Leading coefficient when viewed as a polynomial in Y.
    ArkLib: `Polynomial.Bivariate.leadingCoeffY`. -/
def leadingCoeffY {R : Type*} [Zero R] (f : CBivariate R) : CPolynomial R :=
  f.leadingCoeff

/-- Leading coefficient when viewed as a polynomial in X.
    The coefficient of X^(degreeX f): a polynomial in Y. -/
def leadingCoeffX {R : Type*} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (f : CBivariate R) : CPolynomial R :=
  (f.swap).leadingCoeffY

end Operations

section CoeffLemmas

variable {R : Type*}

/-- `CBivariate.coeff` as two composed `CPolynomial.coeff`. -/
@[simp]
theorem coeff_eq_coeff_coeff [Zero R] (f : CBivariate R) (i j : ℕ) :
    coeff f i j = CPolynomial.coeff (CPolynomial.coeff f j) i := rfl

/-- Bivariate coefficients are additive. -/
theorem coeff_add [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CBivariate R) (i j : ℕ) :
    coeff (p + q) i j = coeff p i j + coeff q i j := by
  simp only [coeff_eq_coeff_coeff]
  rw [show CPolynomial.coeff (p + q) j = CPolynomial.coeff p j + CPolynomial.coeff q j from
    CPolynomial.coeff_add p q j, CPolynomial.coeff_add]

/-- Bivariate coefficients distribute over finite sums. -/
theorem coeff_finset_sum [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → CBivariate R) (i j : ℕ) :
    coeff (s.sum f) i j = s.sum (fun t => coeff (f t) i j) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, coeff_eq_coeff_coeff,
      show CPolynomial.coeff (0 : CBivariate R) j = 0 from CPolynomial.coeff_zero j,
      CPolynomial.coeff_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [coeff_add, ih]

/-- Coefficient of a bivariate monomial `c * X^a * Y^b`. -/
theorem coeff_monomialXY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a b : ℕ) (c : R) (i j : ℕ) :
    coeff (monomialXY a b c) i j = if i = a ∧ j = b then c else 0 := by
  rw [coeff_eq_coeff_coeff]
  unfold monomialXY
  rw [CPolynomial.coeff_monomial]
  by_cases hj : j = b
  · rw [if_pos hj, CPolynomial.coeff_monomial]
    by_cases hi : i = a
    · rw [if_pos hi, if_pos ⟨hi, hj⟩]
    · rw [if_neg hi, if_neg (fun h => hi h.1)]
  · rw [if_neg hj, CPolynomial.coeff_zero, if_neg (fun h => hj h.2)]

/-- Coefficient of a `Y`-monomial `Y^m * c(X)` viewed bivariately. -/
theorem coeff_monomialY [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (m : ℕ) (c : CPolynomial R) (i j : ℕ) :
    coeff (CPolynomial.monomial m c) i j = if j = m then CPolynomial.coeff c i else 0 := by
  rw [coeff_eq_coeff_coeff, CPolynomial.coeff_monomial]
  by_cases hj : j = m
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj, CPolynomial.coeff_zero]

/-- Two bivariate polynomials are equal iff all their coefficients agree. -/
theorem eq_iff_coeff [Zero R] [BEq R] [LawfulBEq R] {p q : CBivariate R} :
    p = q ↔ ∀ i j, coeff p i j = coeff q i j := by
  constructor
  · intro h i j; rw [h]
  · intro h
    refine CPolynomial.eq_iff_coeff.2 (fun j => ?_)
    rw [CPolynomial.eq_iff_coeff]
    intro i
    exact h i j

end CoeffLemmas

section WeightedDegreeLemmas

variable {R : Type*} [BEq R] [LawfulBEq R] [Nontrivial R] [Semiring R]

omit [LawfulBEq R] [Nontrivial R] in
/-- The total degree is the `(1, 1)`-weighted degree. -/
theorem totalDegree_eq_natWeightedDegree (f : CBivariate R) :
    CBivariate.totalDegree (R := R) f = CBivariate.natWeightedDegree (R := R) f 1 1 := by
  simp [CBivariate.totalDegree, CBivariate.natWeightedDegree]

omit [LawfulBEq R] [Nontrivial R] in
/-- The X-degree is the `(1, 0)`-weighted degree. -/
theorem natDegreeX_eq_natWeightedDegree (f : CBivariate R) :
    CBivariate.natDegreeX (R := R) f = CBivariate.natWeightedDegree (R := R) f 1 0 := by
  simp [CBivariate.natDegreeX, CBivariate.natWeightedDegree]

omit [Nontrivial R] in
/-- The Y-degree is the `(0, 1)`-weighted degree. -/
theorem natDegreeY_eq_natWeightedDegree (f : CBivariate R) :
    CBivariate.natDegreeY (R := R) f = CBivariate.natWeightedDegree (R := R) f 0 1 := by
  simp [CBivariate.natDegreeY, CBivariate.natWeightedDegree]
  exact CPolynomial.natDegree_eq_support_sup f

/-- The weighted degree of a nonzero monomial `c * X^n * Y^m`
    is `u * n + v * m` where `u` is the weight of `X` and `v` the weight of `Y`. -/
theorem natWeightedDegree_monomialXY [DecidableEq R]
    {n m : ℕ} {c : R} (hc : c ≠ 0) (u v : ℕ) :
    CBivariate.natWeightedDegree
      (CBivariate.monomialXY n m c) u v
      = u * n + v * m := by
  have hmon : CPolynomial.monomial n c ≠ 0 := by
    rw [Ne, CPolynomial.eq_zero_iff_coeff_zero, not_forall]
    use n
    rw [CPolynomial.coeff_monomial]
    simp [hc]
  simp only [
    CBivariate.natWeightedDegree, CBivariate.monomialXY,
    CPolynomial.support_monomial hmon, Finset.sup_singleton,
    CPolynomial.coeff_monomial, if_pos,
    CPolynomial.natDegree_monomial hc]

/-- The weighted degree of the zero polynomial is zero. -/
theorem natWeightedDegree_zero (u v : ℕ) :
    CBivariate.natWeightedDegree (0 : CBivariate R) u v = 0 := by
  simp only [CBivariate.natWeightedDegree,
    show CPolynomial.support (0 : CBivariate R) = ∅ from
      (CPolynomial.support_empty_iff _).mpr rfl,
    Finset.sup_empty, bot_eq_zero]

omit [Nontrivial R] [LawfulBEq R] in
/-- The weighted degree is at most `d` iff every Y-support index
    satisfies the weighted bound. -/
theorem natWeightedDegree_le_iff (f : CBivariate R) (u v d : ℕ) :
    natWeightedDegree f u v ≤ d ↔
    ∀ j ∈ f.supportY , u * (f.val.coeff j).natDegree + v * j ≤ d := by
  simp [CBivariate.natWeightedDegree, CBivariate.supportY]

omit [Nontrivial R] in
/-- The weighted degree is at most `d` iff every monomial index
    satisfies the weighted bound. -/
theorem natWeightedDegree_le_iff_coeff (f : CBivariate R) (u v d : ℕ) :
    f.natWeightedDegree u v ≤ d ↔
    ∀ i j, CBivariate.coeff f i j ≠ 0 → u * i + v * j ≤ d := by
  rw [natWeightedDegree_le_iff]
  constructor
  · intro h i j hij
    have hj : j ∈ f.supportY := by
      rw [CBivariate.supportY, CPolynomial.mem_support_iff]
      intro heq
      apply hij
      show (CPolynomial.coeff f j).coeff i = 0
      rw [heq]
      exact CPolynomial.coeff_zero i
    have hi := CPolynomial.le_natDegree_of_ne_zero hij
    exact le_trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left u hi) _)
      (h j hj)
  · intro h j hj
    have hne := (CPolynomial.mem_support_iff f j).mp hj
    have hlc := CPolynomial.leadingCoeff_ne_zero hne
    rw [CPolynomial.leadingCoeff_eq_coeff_natDegree] at hlc
    exact h _ j hlc

omit [Nontrivial R] in
/-- The natWeightedDegree of a constant bivariate polynomial `CBivariate.CC` is zero. -/
theorem natWeightedDegree_CC {r : R} (u v : ℕ) :
    CBivariate.natWeightedDegree (CBivariate.CC r) u v = 0 := by
  simp only [CBivariate.natWeightedDegree, CBivariate.CC]
  by_cases hr : (CPolynomial.C r : CPolynomial R) = 0
  · rw [hr, CPolynomial.C_zero, (CPolynomial.support_empty_iff _).mpr rfl,
      Finset.sup_empty, bot_eq_zero]
  · rw [CPolynomial.support_C hr, Finset.sup_singleton]
    show u * (CPolynomial.coeff
      (CPolynomial.C (CPolynomial.C r)) 0).natDegree + v * 0 = 0
    rw [CPolynomial.coeff_C, if_pos rfl, CPolynomial.natDegree_C]
    ring

/-- The weighted degree of a sum is at most the max of the weighted degrees. -/
theorem natWeightedDegree_add_le [DecidableEq R] (p q : CBivariate R) (u v : ℕ) :
    CBivariate.natWeightedDegree (p + q) u v ≤
      max (CBivariate.natWeightedDegree p u v) (CBivariate.natWeightedDegree q u v) := by
  rw [natWeightedDegree_le_iff_coeff]
  intro i j hij
  have hcoeff : CBivariate.coeff (p + q) i j =
      CBivariate.coeff p i j + CBivariate.coeff q i j := by
      show ((p + q).val.coeff j).coeff i =
        (p.val.coeff j).coeff i + (q.val.coeff j).coeff i
      rw [show (p + q).val.coeff j = p.val.coeff j + q.val.coeff j from
        CPolynomial.coeff_add p q j]
      exact CPolynomial.coeff_add _ _ i
  rw [hcoeff] at hij
  rcases Decidable.em (CBivariate.coeff p i j = 0) with h0 | hp
  · have hq : CBivariate.coeff q i j ≠ 0 := by
        intro hq; exact hij (by rw [h0, hq, add_zero])
    exact le_trans ((natWeightedDegree_le_iff_coeff q u v _).mp le_rfl i j hq)
        (le_max_right _ _)
  · exact le_trans ((natWeightedDegree_le_iff_coeff p u v _).mp le_rfl i j hp)
      (le_max_left _ _)

end WeightedDegreeLemmas

end CBivariate

end CompPoly
