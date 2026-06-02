/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Filter
import CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree

/-!
# Guruswami-Sudan Core Correctness

Public correctness theorems for the backend-parametric CompPoly
Guruswami-Sudan core.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Every polynomial returned by `gsCore` is a bounded-degree root of the
interpolation polynomial produced by the interpolation backend. -/
theorem gsCore_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams}
    {p : CPolynomial F}
    (hp : p ∈ (gsCore points interpBackend rootBackend params).toList) :
    exists Q,
      interpBackend.interpolate points params = some Q ∧
        ValidInterpolationWitness points params Q ∧
          degreeLt p params.messageDegree ∧
            CBivariate.composeY Q p = 0 := by
  rw [gsCore] at hp
  split at hp
  · simp at hp
  · rename_i Q hQ
    refine ⟨Q, hQ, ?_⟩
    have hs := interpBackend.sound points params Q hQ
    have hr := rootBackend.sound Q params.messageDegree p hp
    exact ⟨hs, hr.1, hr.2⟩

/-- Completeness for the concrete interpolation polynomial returned by the
interpolation backend. -/
theorem gsCore_complete_of_interpolate {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams}
    {Q : CBivariate F} {p : CPolynomial F}
    (hQ : interpBackend.interpolate points params = some Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hroot : CBivariate.composeY Q p = 0) :
    p ∈ (gsCore points interpBackend rootBackend params).toList := by
  unfold gsCore
  rw [hQ]
  exact rootBackend.complete Q params.messageDegree p
    (interpBackend.sound points params Q hQ).1 hpdeg hroot

/-- Backend-parametric completeness for candidates that root every valid
interpolation witness. -/
theorem gsCore_complete_of_roots_all_valid_witnesses {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams}
    {p : CPolynomial F}
    (hInterpExists : exists Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hrootAll :
      ∀ Q,
        ValidInterpolationWitness points params Q →
          CBivariate.composeY Q p = 0) :
    p ∈ (gsCore points interpBackend rootBackend params).toList := by
  rcases interpBackend.complete points params hInterpExists with ⟨Q, hQ⟩
  exact gsCore_complete_of_interpolate (rootBackend := rootBackend) hQ hpdeg
    (hrootAll Q (interpBackend.sound points params Q hQ))

/-- The executable `(0, 0)` Hasse derivative is ordinary full evaluation. -/
private theorem hasseDerivativeEval_zero_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (x y : F) (Q : CBivariate F) :
    CBivariate.hasseDerivativeEval 0 0 x y Q = CBivariate.evalEval x y Q := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  congr
  rw [CBivariate.eq_iff_coeff]
  intro i j
  rw [CBivariate.hasseDerivative_coeff]
  simp

/-- Evaluating `Q(X, p(X))` at `x` agrees with full bivariate evaluation at
`(x, p(x))`. -/
private theorem eval_composeY_eq_evalEval {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (p : CPolynomial F) (x : F) :
    CPolynomial.eval x (CBivariate.composeY Q p) =
      CBivariate.evalEval x (CPolynomial.eval x p) Q := by
  rw [CPolynomial.eval_toPoly, composeY_toPoly, CBivariate.evalEval_toPoly]
  change (Polynomial.evalRingHom x)
      (Polynomial.eval₂ (RingHom.id (Polynomial F)) p.toPoly Q.toPoly) =
    (Polynomial.evalRingHom x)
      (Polynomial.eval₂ (RingHom.id (Polynomial F))
        (Polynomial.C (CPolynomial.eval x p)) Q.toPoly)
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂]
  simp [CPolynomial.eval_toPoly]

/-- A matched point satisfying a positive multiplicity constraint is a root of
the composed univariate polynomial. -/
private theorem eval_composeY_eq_zero_of_matched_point {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    {Q : CBivariate F} {p : CPolynomial F} {point : F × F}
    (hQ : ValidInterpolationWitness points params Q)
    (hpoint : point ∈ points.toList)
    (hmpos : 0 < params.multiplicity)
    (hmatch : CPolynomial.eval point.1 p = point.2) :
    CPolynomial.eval point.1 (CBivariate.composeY Q p) = 0 := by
  rcases hQ with ⟨_hQne, _hQdeg, hQmult⟩
  have hderiv := hQmult point hpoint 0 0 (by omega)
  rw [hasseDerivativeEval_zero_zero] at hderiv
  rw [eval_composeY_eq_evalEval, hmatch]
  exact hderiv

/-- The executable matching counter is the length of the filtered packed-point
list. -/
private theorem matchingPointCount_eq_filter_length {F : Type*} [Semiring F] [BEq F]
    (points : Array (F × F)) (p : CPolynomial F) :
    matchingPointCount points p =
      (points.toList.filter
        (fun point => CPolynomial.eval point.1 p == point.2)).length := by
  cases points with
  | mk data =>
      unfold matchingPointCount
      let pred : F × F → Bool := fun point => CPolynomial.eval point.1 p == point.2
      let step : Nat → F × F → Nat :=
        fun count point => if pred point then count + 1 else count
      have hfold : ∀ (xs : List (F × F)) acc,
          xs.foldl step acc = acc + (xs.filter pred).length := by
        intro xs
        induction xs with
        | nil =>
            intro acc
            simp
        | cons point tail ih =>
            intro acc
            simp only [List.foldl_cons]
            rw [ih]
            by_cases h : pred point = true
            · simp [step, pred, h, Nat.add_assoc, Nat.add_comm]
            · have hfalse : pred point = false := by
                cases hp : pred point <;> simp_all
              simp [step, pred, hfalse, Nat.add_comm]
      simpa [pred, step] using hfold data 0

/-- Filtering matching packed points preserves distinct `x`-coordinates. -/
private theorem matchedX_nodup {F : Type*} [Semiring F] [BEq F]
    {points : Array (F × F)} {p : CPolynomial F}
    (hdistinct : DistinctXCoordinates points) :
    ((points.toList.filter
      (fun point => CPolynomial.eval point.1 p == point.2)).map fun point => point.1).Nodup := by
  unfold DistinctXCoordinates at hdistinct
  exact hdistinct.sublist (List.Sublist.map _ List.filter_sublist)

/-- If `Q(X, p(X))` is nonzero, the number of matched distinct points is bounded
by its univariate degree. This is the simple-root part of the GS completeness
argument. -/
private theorem matchingPointCount_le_natDegree_composeY_of_ne_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    {Q : CBivariate F} {p : CPolynomial F}
    (hQ : ValidInterpolationWitness points params Q)
    (hdistinct : DistinctXCoordinates points)
    (hmpos : 0 < params.multiplicity)
    (hcomp : CBivariate.composeY Q p ≠ 0) :
    matchingPointCount points p ≤ (CBivariate.composeY Q p).toPoly.natDegree := by
  let matched := points.toList.filter fun point => CPolynomial.eval point.1 p == point.2
  let xs : Finset F := (matched.map fun point => point.1).toFinset
  have hxs_card : xs.card = matchingPointCount points p := by
    rw [matchingPointCount_eq_filter_length]
    dsimp [xs, matched]
    rw [List.toFinset_card_of_nodup]
    · simp
    · exact matchedX_nodup (points := points) (p := p) hdistinct
  have hpoly_ne : (CBivariate.composeY Q p).toPoly ≠ 0 := by
    exact (CPolynomial.toPoly_eq_zero_iff (CBivariate.composeY Q p)).not.mpr hcomp
  have hsub : xs.val ⊆ (CBivariate.composeY Q p).toPoly.roots := by
    intro x hx
    have hxfin : x ∈ xs := by simpa [xs] using hx
    rcases List.mem_toFinset.mp hxfin with hxlist
    rcases List.mem_map.mp hxlist with ⟨point, hpointMatched, rfl⟩
    have hpoint : point ∈ points.toList := (List.mem_filter.mp hpointMatched).1
    have hmatchBool : (CPolynomial.eval point.1 p == point.2) = true :=
      (List.mem_filter.mp hpointMatched).2
    have hmatch : CPolynomial.eval point.1 p = point.2 := LawfulBEq.eq_of_beq hmatchBool
    have hrootC := eval_composeY_eq_zero_of_matched_point hQ hpoint hmpos hmatch
    have hrootP : (CBivariate.composeY Q p).toPoly.eval point.1 = 0 := by
      rw [← CPolynomial.eval_toPoly]
      exact hrootC
    exact (Polynomial.mem_roots hpoly_ne).2 (by simpa [Polynomial.IsRoot] using hrootP)
  have hcard := Polynomial.card_le_degree_of_subset_roots
    (p := (CBivariate.composeY Q p).toPoly) (Z := xs) hsub
  omega

/-- `degreeLt p k` gives the Mathlib-side bound `natDegree p ≤ k - 1`. -/
private theorem toPoly_natDegree_le_pred_of_degreeLt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {k : Nat} (hp : degreeLt p k) :
    p.toPoly.natDegree ≤ k - 1 := by
  unfold degreeLt at hp
  by_cases hpzero : p = 0
  · rw [hpzero]
    have hzero : ((0 : CPolynomial F).toPoly) = 0 :=
      (CPolynomial.toPoly_eq_zero_iff (0 : CPolynomial F)).mpr rfl
    rw [hzero]
    simp
  · have hdegCp := CPolynomial.degree_toPoly p
    have hdeg : p.toPoly.degree < (k : WithBot Nat) := by
      rwa [← hdegCp]
    have hpoly_ne : p.toPoly ≠ 0 := (CPolynomial.toPoly_eq_zero_iff p).not.mpr hpzero
    have hnat_lt : p.toPoly.natDegree < k := by
      exact WithBot.coe_lt_coe.mp
        (by simpa [Polynomial.degree_eq_natDegree hpoly_ne] using hdeg)
    omega

/-- The composed univariate polynomial has degree bounded by the interpolation
witness weighted-degree bound. -/
private theorem natDegree_composeY_toPoly_le_weightedDegreeBound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (F × F)} {params : GSInterpParams}
    {Q : CBivariate F} {p : CPolynomial F}
    (hQ : ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree) :
    (CBivariate.composeY Q p).toPoly.natDegree ≤ params.weightedDegreeBound := by
  rcases hQ with ⟨_hQne, hQdeg, _hQmult⟩
  have hpN := toPoly_natDegree_le_pred_of_degreeLt hpdeg
  have hdeg := Polynomial.Bivariate.degree_eval_le_weightedDegree
    (Q := CBivariate.toPoly Q) (P := p.toPoly) (k := params.messageDegree) hpN
  rw [composeY_toPoly]
  rw [CBivariate.natWeightedDegree_toPoly] at hdeg
  exact le_trans hdeg hQdeg

/-- Hasse derivatives in the outer variable commute with Taylor shifting the
inner coefficients. -/
private theorem hasseDeriv_map_taylorAlgHom {F : Type*} [Field F]
    (P : Polynomial (Polynomial F)) (x : F) (b : Nat) :
  Polynomial.hasseDeriv b (P.map (Polynomial.taylorAlgHom x).toRingHom) =
      (Polynomial.hasseDeriv b P).map (Polynomial.taylorAlgHom x).toRingHom := by
  ext n
  simp [Polynomial.hasseDeriv_coeff, Polynomial.taylorAlgHom, Polynomial.taylor_apply]

/-- Evaluating after Taylor-shifting all inner coefficients is the Taylor shift
of the evaluated coefficient polynomial. -/
private theorem eval_map_taylorAlgHom {F : Type*} [Field F]
    (P : Polynomial (Polynomial F)) (x y : F) :
    Polynomial.eval (Polynomial.C y) (P.map (Polynomial.taylorAlgHom x).toRingHom) =
      Polynomial.taylor x (Polynomial.eval (Polynomial.C y) P) := by
  rw [Polynomial.eval_map]
  change P.eval₂ (Polynomial.taylorAlgHom x).toRingHom (Polynomial.C y) =
    (Polynomial.taylorAlgHom x).toRingHom
      (P.eval₂ (RingHom.id (Polynomial F)) (Polynomial.C y))
  rw [Polynomial.hom_eval₂]
  simp [Polynomial.taylorAlgHom]

/-- Hasse derivatives in `X` commute with multiplication by an `X`-constant
polynomial. -/
private theorem hasseDeriv_mul_C_pow {F : Type*} [Field F]
    (P : Polynomial F) (c : F) (n a : Nat) :
    Polynomial.hasseDeriv a (P * Polynomial.C c ^ n) =
      Polynomial.hasseDeriv a P * Polynomial.C c ^ n := by
  rw [show Polynomial.C c ^ n = Polynomial.C (c ^ n) by rw [Polynomial.C_pow]]
  ext d
  rw [Polynomial.hasseDeriv_coeff]
  rw [Polynomial.coeff_mul_C]
  rw [Polynomial.coeff_mul_C]
  rw [Polynomial.hasseDeriv_coeff]
  ring

/-- Hasse differentiating the inner-variable polynomial after evaluating the
outer variable at a constant equals evaluating the coefficientwise Hasse
derivative. -/
private theorem hasseDeriv_eval_C_eq_eval_coeffwise_hasseDeriv {F : Type*}
    [Field F] (P : Polynomial (Polynomial F)) (y : F) (a : Nat) :
    Polynomial.hasseDeriv a (Polynomial.eval (Polynomial.C y) P) =
      Polynomial.eval (Polynomial.C y)
        (P.sum fun j coeff => Polynomial.monomial j (Polynomial.hasseDeriv a coeff)) := by
  rw [Polynomial.eval_eq_sum]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.sum_add_index]
      rw [map_add]
      rw [hP, hQ]
      rw [Polynomial.sum_add_index]
      · simp
      · intro i
        simp
      · intro i p q
        simp
      · intro i
        simp
      · intro i p q
        simp [add_mul]
  | monomial n coeff =>
      simp [Polynomial.sum_monomial_index, hasseDeriv_mul_C_pow]

/-- The `j`-th coefficient of the coefficientwise Hasse-derivative outer sum is
the Hasse derivative of the `j`-th coefficient. -/
private theorem coeff_coeffwise_hasseDeriv_sum {F : Type*} [Field F]
    (P : Polynomial (Polynomial F)) (a j : Nat) :
    ((P.sum fun k coeff => Polynomial.monomial k (Polynomial.hasseDeriv a coeff)).coeff j) =
      Polynomial.hasseDeriv a (P.coeff j) := by
  rw [Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  by_cases hj : j ∈ P.support
  · rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro k _hk hkj
      rw [Polynomial.coeff_monomial, if_neg hkj]
    · intro hjnot
      contradiction
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hj]
      simp
    · intro k hk
      have hkj : k ≠ j := by
        intro h
        exact hj (h ▸ hk)
      rw [Polynomial.coeff_monomial, if_neg hkj]

/-- The executable bivariate Hasse derivative matches the Mathlib-side
coefficientwise inner Hasse derivative of the outer Hasse derivative. -/
private theorem toPoly_hasseDerivative_eq_coeffwise_hasseDeriv_hasseDeriv {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (a b : Nat) :
    (CBivariate.hasseDerivative a b Q).toPoly =
      (Polynomial.hasseDeriv b Q.toPoly).sum fun j coeff =>
        Polynomial.monomial j (Polynomial.hasseDeriv a coeff) := by
  ext j n
  rw [coeff_coeffwise_hasseDeriv_sum]
  simp [Polynomial.hasseDeriv_coeff, CBivariate.hasseDerivative_coeff,
    CBivariate.coeff_toPoly]
  ring

/-- Evaluating the univariate `X`-Hasse derivative of the evaluated `Y`-Hasse
derivative matches the executable bivariate Hasse derivative. -/
private theorem eval_hasseDeriv_eval_hasseDeriv_toPoly {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (x y : F) (a b : Nat) :
    Polynomial.eval x (Polynomial.hasseDeriv a
        (Polynomial.eval (Polynomial.C y) (Polynomial.hasseDeriv b Q.toPoly))) =
      CBivariate.hasseDerivativeEval a b x y Q := by
  rw [← CBivariate.hasseDerivative_eval_eq_eval]
  rw [CBivariate.evalEval_toPoly]
  rw [Polynomial.evalEval]
  rw [hasseDeriv_eval_C_eq_eval_coeffwise_hasseDeriv]
  rw [← toPoly_hasseDerivative_eq_coeffwise_hasseDeriv_hasseDeriv]

/-- The `(a, b)` coefficient of the two-variable Taylor shift of `Q` is the
executable Hasse derivative of order `(a, b)` at the shift point. -/
private theorem shifted_coeff_eq_hasseDerivativeEval {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (x y : F) (a b : Nat) :
    ((Polynomial.taylor (Polynomial.C y)
      ((CBivariate.toPoly Q).map (Polynomial.taylorAlgHom x).toRingHom)).coeff b).coeff a =
      CBivariate.hasseDerivativeEval a b x y Q := by
  rw [Polynomial.taylor_coeff]
  rw [hasseDeriv_map_taylorAlgHom]
  rw [eval_map_taylorAlgHom]
  rw [Polynomial.taylor_coeff]
  exact eval_hasseDeriv_eval_hasseDeriv_toPoly Q x y a b

/-- Taylor shifting `Q(X, p(X))` at `x` is the same as shifting `Q` in both
variables and substituting the positive-order part of `p(X + x)`. -/
private theorem taylor_composeY_toPoly_eq {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    (Q : CBivariate F) (p : CPolynomial F) (x y : F)
    (_hmatch : CPolynomial.eval x p = y) :
    Polynomial.taylor x (CBivariate.composeY Q p).toPoly =
      (Polynomial.taylor (Polynomial.C y)
        ((CBivariate.toPoly Q).map (Polynomial.taylorAlgHom x).toRingHom)).eval
          (Polynomial.taylor x p.toPoly - Polynomial.C y) := by
  rw [composeY_toPoly]
  change (Polynomial.taylorAlgHom x).toRingHom
      (Polynomial.eval₂ (RingHom.id (Polynomial F)) p.toPoly Q.toPoly) = _
  rw [Polynomial.hom_eval₂]
  simp [Polynomial.eval_map, Polynomial.taylorAlgHom, Polynomial.taylor_apply]

/-- If `P(x) = y`, the nonconstant Taylor tail `P(X + x) - y` is divisible by
`X`. -/
private theorem X_dvd_taylor_sub_C_eval {F : Type*} [Field F]
    (P : Polynomial F) (x y : F) (h : P.eval x = y) :
    Polynomial.X ∣ Polynomial.taylor x P - Polynomial.C y := by
  rw [Polynomial.X_dvd_iff]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff_zero, Polynomial.coeff_C_zero]
  rw [h, sub_self]

/-- If the `b`-th coefficient of a shifted bivariate polynomial has no terms
below `X^(m - b)` and `U` is divisible by `X`, then the `b`-th evaluated term is
divisible by `X^m`. -/
private theorem X_pow_dvd_mul_pow_of_total_coeff_zero {F : Type*} [Field F]
    {A U : Polynomial F} {m b : Nat}
    (hU : Polynomial.X ∣ U)
    (hzero : ∀ a, a + b < m → A.coeff a = 0) :
    Polynomial.X ^ m ∣ A * U ^ b := by
  by_cases hb : b < m
  · have hA : Polynomial.X ^ (m - b) ∣ A := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      exact hzero d (by omega)
    have hUb : Polynomial.X ^ b ∣ U ^ b := by
      exact pow_dvd_pow_of_dvd hU b
    rcases hA with ⟨A', hA'⟩
    rcases hUb with ⟨U', hU'⟩
    refine ⟨A' * U', ?_⟩
    rw [hA', hU']
    ring_nf
    rw [← pow_add]
    have hmb : m - b + b = m := by omega
    rw [hmb]
  · have hbm : m ≤ b := Nat.le_of_not_gt hb
    have hXb : (Polynomial.X : Polynomial F) ^ m ∣ (Polynomial.X : Polynomial F) ^ b := by
      exact pow_dvd_pow (Polynomial.X : Polynomial F) hbm
    have hUb : Polynomial.X ^ b ∣ U ^ b := by
      exact pow_dvd_pow_of_dvd hU b
    exact dvd_mul_of_dvd_right (dvd_trans hXb hUb) A

/-- A bivariate polynomial with no shifted terms of total degree `< m` evaluates
to a univariate polynomial divisible by `X^m` after substituting any `U`
divisible by `X` for `Y`. -/
private theorem X_pow_dvd_eval_of_total_coeff_zero {F : Type*} [Field F]
    {B : Polynomial (Polynomial F)} {U : Polynomial F} {m : Nat}
    (hU : Polynomial.X ∣ U)
    (hzero : ∀ a b, a + b < m → (B.coeff b).coeff a = 0) :
    Polynomial.X ^ m ∣ B.eval U := by
  rw [Polynomial.eval_eq_sum]
  apply Finset.dvd_sum
  intro b _hb
  exact X_pow_dvd_mul_pow_of_total_coeff_zero (m := m) (b := b) hU
    (fun a ha => hzero a b ha)

/-- Bivariate Hasse multiplicity at a matched point transfers to univariate root
multiplicity of `Q(X, p(X))` at the matching `x`-coordinate. -/
private theorem rootMultiplicity_composeY_toPoly_of_matched_point {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {Q : CBivariate F} {p : CPolynomial F} {x y : F} {m : Nat}
    (hmult : CBivariate.HasMultiplicityAtLeast Q x y m)
    (hmatch : CPolynomial.eval x p = y)
    (hcomp : CBivariate.composeY Q p ≠ 0) :
    m ≤ (CBivariate.composeY Q p).toPoly.rootMultiplicity x := by
  let R : Polynomial F := (CBivariate.composeY Q p).toPoly
  have hRne : R ≠ 0 := by
    exact (CPolynomial.toPoly_eq_zero_iff (CBivariate.composeY Q p)).not.mpr hcomp
  have hRtaylor_ne : Polynomial.taylor x R ≠ 0 := by
    exact (Polynomial.taylor_eq_zero x R).not.mpr hRne
  rw [Polynomial.rootMultiplicity_eq_rootMultiplicity (p := R) (t := x)]
  rw [show R.comp (Polynomial.X + Polynomial.C x) = Polynomial.taylor x R by rfl]
  rw [Polynomial.le_rootMultiplicity_iff hRtaylor_ne]
  have hmatchPoly : p.toPoly.eval x = y := by
    rw [← CPolynomial.eval_toPoly]
    exact hmatch
  have hU : Polynomial.X ∣ Polynomial.taylor x p.toPoly - Polynomial.C y :=
    X_dvd_taylor_sub_C_eval p.toPoly x y hmatchPoly
  rw [taylor_composeY_toPoly_eq Q p x y hmatch]
  simpa using X_pow_dvd_eval_of_total_coeff_zero
    (B := Polynomial.taylor (Polynomial.C y)
      ((CBivariate.toPoly Q).map (Polynomial.taylorAlgHom x).toRingHom))
    (U := Polynomial.taylor x p.toPoly - Polynomial.C y) (m := m) hU
    (by
      intro a b hab
      rw [shifted_coeff_eq_hasseDerivativeEval]
      exact hmult a b hab)

/-- A finite set whose points all occur with root multiplicity at least `m`
contributes at least `m * card` roots, counted with multiplicity. -/
private theorem finset_mul_card_le_natDegree_of_rootMultiplicity_ge {F : Type*}
    [Field F] [DecidableEq F] (R : Polynomial F) (xs : Finset F) (m : Nat)
    (hmult : ∀ x, x ∈ xs → m ≤ R.rootMultiplicity x) :
    m * xs.card ≤ R.natDegree := by
  classical
  have hsum_le_roots : ∑ x ∈ xs, m ≤ R.roots.card := by
    calc
      ∑ x ∈ xs, m ≤ ∑ x ∈ xs, Multiset.count x R.roots := by
        exact Finset.sum_le_sum fun x hx => by
          simpa [Polynomial.count_roots] using hmult x hx
      _ ≤ ∑ x ∈ xs ∪ R.roots.toFinset, Multiset.count x R.roots := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact Finset.mem_union.mpr (Or.inl hx)
        · intro x _ _
          exact Nat.zero_le _
      _ = R.roots.card := by
        rw [Multiset.sum_count_eq_card]
        intro x hx
        exact Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hx))
  have hroots_le : R.roots.card ≤ R.natDegree := Polynomial.card_roots' R
  simpa [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using
    le_trans hsum_le_roots hroots_le

/-- If a bounded-degree candidate agrees with enough distinct packed
multiplicity-constrained points, it roots any valid interpolation witness. -/
theorem composeY_eq_zero_of_enough_matching_multiplicity_points {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)} {params : GSInterpParams}
    {Q : CBivariate F} {p : CPolynomial F}
    (hQ : ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches :
      params.weightedDegreeBound <
        params.multiplicity * matchingPointCount points p) :
    CBivariate.composeY Q p = 0 := by
  by_cases hcomp : CBivariate.composeY Q p = 0
  · exact hcomp
  have hmpos : 0 < params.multiplicity := by
    by_contra hnot
    have hmzero : params.multiplicity = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hmzero, zero_mul] at hmatches
    omega
  have hcount_le :=
    matchingPointCount_le_natDegree_composeY_of_ne_zero
      hQ hdistinct hmpos hcomp
  have hdegree_le :=
    natDegree_composeY_toPoly_le_weightedDegreeBound hQ hpdeg
  by_cases hmle : params.multiplicity ≤ 1
  · have hmone : params.multiplicity = 1 := by omega
    rw [hmone, one_mul] at hmatches
    omega
  · let matched := points.toList.filter fun point => CPolynomial.eval point.1 p == point.2
    let xs : Finset F := (matched.map fun point => point.1).toFinset
    have hxs_card : xs.card = matchingPointCount points p := by
      rw [matchingPointCount_eq_filter_length]
      dsimp [xs, matched]
      rw [List.toFinset_card_of_nodup]
      · simp
      · exact matchedX_nodup (points := points) (p := p) hdistinct
    have hmult : ∀ x, x ∈ xs →
        params.multiplicity ≤ (CBivariate.composeY Q p).toPoly.rootMultiplicity x := by
      intro x hx
      rcases List.mem_toFinset.mp hx with hxlist
      rcases List.mem_map.mp hxlist with ⟨point, hpointMatched, rfl⟩
      have hpoint : point ∈ points.toList := (List.mem_filter.mp hpointMatched).1
      have hmatchBool : (CPolynomial.eval point.1 p == point.2) = true :=
        (List.mem_filter.mp hpointMatched).2
      have hmatch : CPolynomial.eval point.1 p = point.2 := LawfulBEq.eq_of_beq hmatchBool
      exact rootMultiplicity_composeY_toPoly_of_matched_point
        (hQ.2.2 point hpoint) hmatch hcomp
    have hmul_degree :
        params.multiplicity * matchingPointCount points p ≤
          (CBivariate.composeY Q p).toPoly.natDegree := by
      have hmul_xs := finset_mul_card_le_natDegree_of_rootMultiplicity_ge
        (R := (CBivariate.composeY Q p).toPoly) (xs := xs)
        (m := params.multiplicity) hmult
      simpa [hxs_card] using hmul_xs
    omega

/-- Packed-point semantic completeness for the algebraic GS core. -/
theorem gsCore_complete_of_enough_matches {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]
    {points : Array (Prod F F)}
    {interpBackend : GSInterpBackend F} {rootBackend : GSRootBackend F}
    {params : GSInterpParams}
    {p : CPolynomial F}
    (hInterpExists : exists Q, ValidInterpolationWitness points params Q)
    (hpdeg : degreeLt p params.messageDegree)
    (hdistinct : DistinctXCoordinates points)
    (hmatches :
      params.weightedDegreeBound <
        params.multiplicity * matchingPointCount points p) :
    p ∈ (gsCore points interpBackend rootBackend params).toList := by
  apply gsCore_complete_of_roots_all_valid_witnesses
      (rootBackend := rootBackend) hInterpExists hpdeg
  intro Q hQ
  exact composeY_eq_zero_of_enough_matching_multiplicity_points hQ hpdeg hdistinct hmatches

end GuruswamiSudan

end CompPoly
