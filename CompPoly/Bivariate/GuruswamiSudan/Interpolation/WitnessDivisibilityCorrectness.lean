/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Interpolation.WitnessDivisibility
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Koetter.Correctness.Combinations
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Basis
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness.Divisibility

/-!
# Correctness of Divisibility-Based Witness Checking

`satisfiesMultiplicityConstraintsViaDivisibilityBool` agrees with the
pointwise Hasse checker `CBivariate.satisfiesMultiplicityConstraintsBool`
on point sets with distinct `x`-coordinates, and consequently
`interpolationWitnessIsValidViaDivisibilityBool` agrees with
`interpolationWitnessIsValidBool`.

The proof peels one base-`(Y - R)` digit per multiplicity level.

* Soundness: from `Q = C c + (Y - R) * Q'` with `c = W * G^(m+1)`, the digit
  term gains multiplicity `m + 1` from the `G`-power
  (`hasMultiplicityAtLeast_ofYConstant_pow_mul_eval_zero`), the quotient term
  gains one from `Y - R` (`hasMultiplicityAtLeast_linearYDivisor_mul`) on top
  of the inductive hypothesis, and multiplicity is closed under addition.

* Completeness: the quotient `Q'` keeps multiplicity `m` at every point
  (`witness_hasMultiplicity_quot`, by a strong induction on the
  `X`-coefficients of the Taylor-shifted division identity), so the digit
  `C c = Q - (Y - R) * Q'` has multiplicity `m + 1` with `Y`-degree zero, and
  `coeffY_dvd_vanishingPolynomial_pow_of_multiplicity` forces
  `G^(m+1) ∣ c`.
-/

namespace CompPoly

namespace GuruswamiSudan

open CBivariate

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F]

/-! ### Generic helpers -/

private theorem witness_cpoly_eq_of_toPoly_eq {R : Type*}
    [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R}
    (h : p.toPoly = q.toPoly) : p = q := by
  rw [CPolynomial.eq_iff_coeff]
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, h]

omit [Nontrivial F] [DecidableEq F] in
private theorem witness_linearFactor_toPoly (x : F) :
    (CPolynomial.linearFactor x).toPoly =
      (Polynomial.X - Polynomial.C x : Polynomial F) := by
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly, Polynomial.C_neg]
  ring

omit [Nontrivial F] [DecidableEq F] in
private theorem witness_foldl_linearFactor_monic (l : List F) (acc : CPolynomial F)
    (hacc : acc.toPoly.Monic) :
    (l.foldl (fun acc x ↦ acc * CPolynomial.linearFactor x) acc).toPoly.Monic := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      rw [CPolynomial.toPoly_mul, witness_linearFactor_toPoly]
      exact hacc.mul (Polynomial.monic_X_sub_C x)

omit [DecidableEq F] in
/-- The vanishing polynomial of a node array is monic. -/
private theorem witness_vanishing_monic (xs : Array F) :
    (CPolynomial.vanishingPolynomialArray xs).monic := by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.vanishingPolynomialArray,
    ← Array.foldl_toList]
  exact witness_foldl_linearFactor_monic xs.toList 1
    (by rw [CPolynomial.toPoly_one]; exact Polynomial.monic_one)

omit [DecidableEq F] in
private theorem witness_monic_pow {g : CPolynomial F} (hg : g.monic) (k : Nat) :
    (g ^ k).monic := by
  rw [CPolynomial.monic_toPoly_iff] at hg ⊢
  rw [CPolynomial.toPoly_pow]
  exact hg.pow k

omit [DecidableEq F] in
/-- Remainder by a monic divisor vanishes exactly on multiples. -/
private theorem witness_modByMonic_eq_zero_iff {c g : CPolynomial F}
    (hg : g.monic) :
    CPolynomial.modByMonic c g = 0 ↔ ∃ W : CPolynomial F, c = W * g := by
  have hgPoly : g.toPoly.Monic := (CPolynomial.monic_toPoly_iff g).mp hg
  constructor
  · intro h
    have hmod : c.toPoly %ₘ g.toPoly = 0 := by
      rw [← CPolynomial.modByMonic_toPoly_eq_modByMonic c g hg, h]
      exact (CPolynomial.toPoly_eq_zero_iff _).mpr rfl
    rcases (Polynomial.modByMonic_eq_zero_iff_dvd hgPoly).mp hmod with ⟨w, hw⟩
    refine ⟨⟨w.toImpl, CPolynomial.Raw.isCanonical_toImpl w⟩, ?_⟩
    apply witness_cpoly_eq_of_toPoly_eq
    rw [CPolynomial.toPoly_mul]
    have hWto : CPolynomial.toPoly
        (⟨w.toImpl, CPolynomial.Raw.isCanonical_toImpl w⟩ : CPolynomial F) = w :=
      CPolynomial.Raw.toPoly_toImpl
    rw [hWto, hw]
    ring
  · rintro ⟨W, rfl⟩
    have hmod : (W * g).toPoly %ₘ g.toPoly = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hgPoly).mpr
        ⟨W.toPoly, by rw [CPolynomial.toPoly_mul]; ring⟩
    apply witness_cpoly_eq_of_toPoly_eq
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hg, hmod]
    exact ((CPolynomial.toPoly_eq_zero_iff _).mpr rfl).symm

/-! ### The division identity -/

/-- Euclidean identity of `divByLinearY` at the `CBivariate` level. -/
private theorem witness_divByLinearY_decomposition (Q : CBivariate F)
    (R : CPolynomial F) :
    Q = CBivariate.ofYConstant (CBivariate.divByLinearY Q R).2 +
      CBivariate.linearYDivisor R * (CBivariate.divByLinearY Q R).1 := by
  apply witness_cpoly_eq_of_toPoly_eq (R := CPolynomial F)
  erw [CPolynomial.toPoly_add, CPolynomial.toPoly_mul]
  exact (CBivariate.divByLinearY_euclid_toPoly Q R).symm

/-! ### The shifted division identity -/

private theorem witness_taylor_neg (x : F) (u : CPolynomial F) :
    CPolynomial.taylor x (-u) = -CPolynomial.taylor x u := by
  apply witness_cpoly_eq_of_toPoly_eq
  rw [CPolynomial.taylor_toPoly, CPolynomial.toPoly_neg, CPolynomial.toPoly_neg,
    CPolynomial.taylor_toPoly, map_neg]

private theorem witness_taylor_one (x : F) :
    CPolynomial.taylor x (1 : CPolynomial F) = 1 := by
  apply witness_cpoly_eq_of_toPoly_eq
  simp [CPolynomial.taylor_toPoly, CPolynomial.toPoly_one]

private theorem witness_taylor_sub_C (x y : F) (R : CPolynomial F) :
    CPolynomial.taylor x (R - CPolynomial.C y) =
      CPolynomial.taylor x R - CPolynomial.C y := by
  apply witness_cpoly_eq_of_toPoly_eq
  rw [CPolynomial.taylor_toPoly, CPolynomial.toPoly_sub, CPolynomial.toPoly_sub,
    CPolynomial.taylor_toPoly, CPolynomial.C_toPoly, map_sub, Polynomial.taylor_C]

/-- Outer (`Y`) coefficients of the linear divisor `Y - u`. -/
private theorem witness_coeff_linearYDivisor (u : CPolynomial F) (j : Nat) :
    CPolynomial.coeff (CBivariate.linearYDivisor u) j =
      if j = 0 then -u else if j = 1 then (1 : CPolynomial F) else 0 := by
  rw [CPolynomial.coeff_toPoly, CBivariate.linearYDivisor_toPoly,
    Polynomial.coeff_sub, Polynomial.coeff_C]
  rcases j with _ | _ | j <;>
    simp [Polynomial.coeff_X]

/-- The outer (`Y`) shift maps `Y - R` to `Y - (R - C y)`. -/
private theorem witness_shiftY_linearYDivisor (y : F) (R : CPolynomial F) :
    CBivariate.shiftY y (CBivariate.linearYDivisor R) =
      CBivariate.linearYDivisor (R - CPolynomial.C y) := by
  apply witness_cpoly_eq_of_toPoly_eq (R := CPolynomial F)
  rw [CBivariate.shiftY, CPolynomial.taylor_toPoly,
    CBivariate.linearYDivisor_toPoly, CBivariate.linearYDivisor_toPoly,
    map_sub, Polynomial.taylor_X, Polynomial.taylor_C, map_sub]
  ring

/-- The inner (`X`) shift maps `Y - u` to `Y - taylor x u`. -/
private theorem witness_shiftX_linearYDivisor (x : F) (u : CPolynomial F) :
    CBivariate.shiftX x (CBivariate.linearYDivisor u) =
      CBivariate.linearYDivisor (CPolynomial.taylor x u) := by
  refine (CPolynomial.eq_iff_coeff (R := CPolynomial F)).mpr fun j ↦ ?_
  rw [CBivariate.outerCoeff_shiftX, witness_coeff_linearYDivisor,
    witness_coeff_linearYDivisor]
  rcases j with _ | _ | j
  · simpa using witness_taylor_neg x u
  · simpa using witness_taylor_one x
  · simpa using CPolynomial.taylor_zero x

/-- The full Taylor shift maps `Y - R` to `Y - (taylor x R - C y)`. -/
private theorem witness_shiftC_linearYDivisor (x y : F) (R : CPolynomial F) :
    CBivariate.shiftC x y (CBivariate.linearYDivisor R) =
      CBivariate.linearYDivisor (CPolynomial.taylor x R - CPolynomial.C y) := by
  show CBivariate.shiftX x (CBivariate.shiftY y (CBivariate.linearYDivisor R)) = _
  rw [witness_shiftY_linearYDivisor, witness_shiftX_linearYDivisor,
    witness_taylor_sub_C]

/-- Positive-`Y` outer coefficients of the shift of a `Y`-constant vanish. -/
private theorem witness_outerCoeff_shiftC_C (x y : F) (c : CPolynomial F)
    (j : Nat) :
    CPolynomial.coeff (CBivariate.shiftC x y (CBivariate.ofYConstant c))
      (j + 1) = 0 := by
  have hY : CBivariate.shiftY y (CBivariate.ofYConstant c) =
      CBivariate.ofYConstant c := by
    apply witness_cpoly_eq_of_toPoly_eq (R := CPolynomial F)
    show CPolynomial.toPoly
        (CPolynomial.taylor (CPolynomial.C y) (CPolynomial.C c)) =
      CPolynomial.toPoly (CPolynomial.C c)
    rw [CPolynomial.taylor_toPoly, CPolynomial.C_toPoly, Polynomial.taylor_C]
  show CPolynomial.coeff
    (CBivariate.shiftX x (CBivariate.shiftY y (CBivariate.ofYConstant c)))
      (j + 1) = 0
  rw [hY]
  show CPolynomial.coeff
    (CBivariate.shiftX x (CPolynomial.C c)) (j + 1) = 0
  rw [CBivariate.outerCoeff_shiftX, CPolynomial.coeff_C]
  simp [CPolynomial.taylor_zero]

/-! ### The quotient keeps multiplicity -/

omit [Nontrivial F] [DecidableEq F] in
/-- Univariate coefficients of a difference. -/
private theorem witness_coeff_sub (p q : CPolynomial F) (i : Nat) :
    CPolynomial.coeff (p - q) i =
      CPolynomial.coeff p i - CPolynomial.coeff q i := by
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly,
    CPolynomial.toPoly_sub, Polynomial.coeff_sub]

/-- Outer (`Y`) coefficients of a product with the linear divisor `Y - u`. -/
private theorem witness_outerCoeff_linearYDivisor_mul (u : CPolynomial F)
    (P : CBivariate F) (j : Nat) :
    CPolynomial.coeff (CBivariate.linearYDivisor u * P) (j + 1) =
      CPolynomial.coeff P j - u * CPolynomial.coeff P (j + 1) := by
  rw [CPolynomial.coeff_toPoly]
  erw [CPolynomial.toPoly_mul]
  rw [CBivariate.linearYDivisor_toPoly, mul_comm,
    Polynomial.coeff_mul_X_sub_C, CPolynomial.coeff_toPoly,
    CPolynomial.coeff_toPoly]
  ring

/-- Core coefficient induction: if every positive-`Y`-row low coefficient of
`(Y - u) * P` vanishes and `u` has no constant term, then every low
coefficient of `P` vanishes. -/
private theorem witness_coeff_low_vanish
    {u : CPolynomial F} (hu : CPolynomial.coeff u 0 = 0)
    {P : CBivariate F} {m : Nat}
    (h : ∀ i j, i + j + 1 < m + 1 →
      CBivariate.coeff (CBivariate.linearYDivisor u * P) i (j + 1) = 0) :
    ∀ i j, i + j < m → CBivariate.coeff P i j = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hij
    have hprod := h i j (by omega)
    rw [CBivariate.coeff_eq_coeff_coeff, witness_outerCoeff_linearYDivisor_mul,
      witness_coeff_sub] at hprod
    have hmul : CPolynomial.coeff (u * CPolynomial.coeff P (j + 1)) i = 0 := by
      rw [CPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      intro k hk
      have hkle : k ≤ i := by
        have := Finset.mem_range.mp hk
        omega
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [hu, zero_mul]
      · have hcoeff : CPolynomial.coeff (CPolynomial.coeff P (j + 1)) (i - k) = 0 := by
          have hlow := ih (i - k) (by omega) (j + 1) (by omega)
          rw [CBivariate.coeff_eq_coeff_coeff] at hlow
          exact hlow
        rw [hcoeff, mul_zero]
    rw [hmul, sub_zero] at hprod
    rw [CBivariate.coeff_eq_coeff_coeff]
    exact hprod

/-- Dividing by `Y - R` through a point of multiplicity `m + 1` leaves a
quotient of multiplicity `m` there. -/
private theorem witness_hasMultiplicity_quot
    {Q : CBivariate F} {R : CPolynomial F} {x y : F} {m : Nat}
    (hxy : CPolynomial.eval x R = y)
    (hQ : CBivariate.hasMultiplicity Q (m + 1) x y) :
    CBivariate.hasMultiplicity (CBivariate.divByLinearY Q R).1 m x y := by
  set c := (CBivariate.divByLinearY Q R).2 with hc
  set Q' := (CBivariate.divByLinearY Q R).1 with hq'
  have hu0 : CPolynomial.coeff (CPolynomial.taylor x R - CPolynomial.C y) 0 = 0 := by
    rw [witness_coeff_sub, CPolynomial.taylor_coeff_zero, CPolynomial.coeff_C,
      hxy]
    simp
  have hshift : CBivariate.shiftC x y Q =
      CBivariate.shiftC x y (CBivariate.ofYConstant c) +
        CBivariate.linearYDivisor (CPolynomial.taylor x R - CPolynomial.C y) *
          CBivariate.shiftC x y Q' := by
    conv_lhs => rw [witness_divByLinearY_decomposition Q R]
    rw [CBivariate.shiftC_add, CBivariate.shiftC_mul,
      witness_shiftC_linearYDivisor]
  intro i j hij
  refine witness_coeff_low_vanish hu0 (P := CBivariate.shiftC x y Q') ?_ i j hij
  intro i' j' hij'
  have h0 : CBivariate.coeff (CBivariate.shiftC x y Q) i' (j' + 1) = 0 :=
    hQ i' (j' + 1) (by omega)
  rw [hshift, CBivariate.coeff_add] at h0
  have hCc : CBivariate.coeff
      (CBivariate.shiftC x y (CBivariate.ofYConstant c)) i' (j' + 1) = 0 := by
    rw [CBivariate.coeff_eq_coeff_coeff, witness_outerCoeff_shiftC_C]
    exact CPolynomial.coeff_zero i'
  rw [hCc, zero_add] at h0
  exact h0

/-! ### Multiplicity closure helpers -/

omit [BEq F] [LawfulBEq F] [Nontrivial F] [DecidableEq F] in
private theorem witness_hasMultiplicityAtLeast_zero (P : CBivariate F) (x y : F) :
    CBivariate.HasMultiplicityAtLeast P x y 0 :=
  fun _ _ hab ↦ absurd hab (by omega)

private theorem witness_hasMultiplicityAtLeast_add
    {P S : CBivariate F} {x y : F} {m : Nat}
    (hP : CBivariate.HasMultiplicityAtLeast P x y m)
    (hS : CBivariate.HasMultiplicityAtLeast S x y m) :
    CBivariate.HasMultiplicityAtLeast (P + S) x y m := by
  intro a b hab
  rw [CBivariate.hasseDerivativeEval_add, hP a b hab, hS a b hab, add_zero]

private theorem witness_hasMultiplicityAtLeast_sub
    {P S : CBivariate F} {x y : F} {m : Nat}
    (hP : CBivariate.HasMultiplicityAtLeast P x y m)
    (hS : CBivariate.HasMultiplicityAtLeast S x y m) :
    CBivariate.HasMultiplicityAtLeast (P - S) x y m := by
  intro a b hab
  rw [CBivariate.hasseDerivativeEval_sub, hP a b hab, hS a b hab, sub_zero]

omit [DecidableEq F] in
private theorem witness_ofYConstant_pow (G : CPolynomial F) (k : Nat) :
    CBivariate.ofYConstant (G ^ k) = (CBivariate.ofYConstant G) ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      apply witness_cpoly_eq_of_toPoly_eq (R := CPolynomial F)
      show (CPolynomial.C (1 : CPolynomial F)).toPoly =
        CPolynomial.toPoly (1 : CPolynomial (CPolynomial F))
      rw [CPolynomial.C_toPoly, CPolynomial.toPoly_one, Polynomial.C_1]
  | succ k ih =>
      rw [pow_succ, pow_succ, ofYConstant_mul, ih]

/-- A multiple of `G^k` viewed as a `Y`-constant has multiplicity `k` at every
point whose `x`-coordinate is a node of `G`. -/
private theorem witness_hasMultiplicityAtLeast_C_of_dvd
    {points : Array (F × F)} {point : F × F} (hpoint : point ∈ points.toList)
    (W : CPolynomial F) (k : Nat) :
    CBivariate.HasMultiplicityAtLeast
      (CBivariate.ofYConstant (W *
        (CPolynomial.vanishingPolynomialArray (points.map fun p ↦ p.1)) ^ k))
      point.1 point.2 k := by
  set G := CPolynomial.vanishingPolynomialArray (points.map fun p ↦ p.1) with hG
  have hEval : CPolynomial.eval point.1 G = 0 := by
    apply CPolynomial.eval_vanishingPolynomialArray_eq_zero_of_mem
    rw [Array.toList_map]
    exact List.mem_map.mpr ⟨point, hpoint, rfl⟩
  have hsplit : CBivariate.ofYConstant (W * G ^ k) =
      (CBivariate.ofYConstant G) ^ k * CBivariate.ofYConstant W := by
    rw [ofYConstant_mul, witness_ofYConstant_pow]
    ring
  rw [hsplit]
  have := LeeOSullivan.hasMultiplicityAtLeast_ofYConstant_pow_mul_eval_zero
    (F := F) G k (P := CBivariate.ofYConstant W) (x := point.1) (y := point.2)
    (m := 0) hEval (witness_hasMultiplicityAtLeast_zero _ _ _)
  simpa using this

/-! ### Main equivalence -/

/-- The digit-divisibility recursion recognizes exactly the multiplicity
constraints, for `G` the vanishing polynomial of the distinct `x`-coordinates
and `R` any interpolant of the points. -/
private theorem witness_viaDivisibility_iff
    (Mul : CPolynomial.MulContext F) (Mod : CPolynomial.ModContext F)
    {points : Array (F × F)} (R : CPolynomial F)
    (hdistinct : DistinctXCoordinates points)
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2)
    (m : Nat) (Q : CBivariate F) :
    satisfiesMultiplicityConstraintsViaDivisibilityBool Mul Mod
        (CPolynomial.vanishingPolynomialArray (points.map fun p ↦ p.1)) R m Q
          = true ↔
      CBivariate.SatisfiesMultiplicityConstraints Q points m := by
  set G := CPolynomial.vanishingPolynomialArray (points.map fun p ↦ p.1) with hG
  induction m generalizing Q with
  | zero =>
      simp only [satisfiesMultiplicityConstraintsViaDivisibilityBool]
      constructor
      · intro _ point _
        exact witness_hasMultiplicityAtLeast_zero Q point.1 point.2
      · intro _
        trivial
  | succ m ih =>
      have hGpow : (G ^ (m + 1)).monic :=
        witness_monic_pow (by simpa [hG] using
          witness_vanishing_monic (points.map fun p ↦ p.1)) (m + 1)
      set c := (CBivariate.divByLinearY Q R).2 with hc
      set Q' := (CBivariate.divByLinearY Q R).1 with hq'
      have hstep : satisfiesMultiplicityConstraintsViaDivisibilityBool Mul Mod
          G R (m + 1) Q =
            ((CPolynomial.modByMonic c (G ^ (m + 1)) == 0) &&
              satisfiesMultiplicityConstraintsViaDivisibilityBool Mul Mod
                G R m Q') := by
        simp only [satisfiesMultiplicityConstraintsViaDivisibilityBool,
          CBivariate.divByLinearYWith_eq_divByLinearY,
          Mod.modByMonic_eq_modByMonic, hc, hq']
      rw [hstep, Bool.and_eq_true, beq_iff_eq,
        witness_modByMonic_eq_zero_iff hGpow]
      constructor
      · rintro ⟨⟨W, hW⟩, hrest⟩
        have hQ' : CBivariate.SatisfiesMultiplicityConstraints Q' points m :=
          (ih Q').mp hrest
        intro point hpoint
        have hCc : CBivariate.HasMultiplicityAtLeast
            (CBivariate.ofYConstant c) point.1 point.2 (m + 1) := by
          rw [hW, hG]
          exact witness_hasMultiplicityAtLeast_C_of_dvd hpoint W (m + 1)
        have hLin : CBivariate.HasMultiplicityAtLeast
            (CBivariate.linearYDivisor R * Q') point.1 point.2 (m + 1) :=
          LeeOSullivan.hasMultiplicityAtLeast_linearYDivisor_mul R
            (hR point hpoint) (hQ' point hpoint)
        have hsum := witness_hasMultiplicityAtLeast_add hCc hLin
        rwa [← witness_divByLinearY_decomposition Q R] at hsum
      · intro hQ
        have hQ' : CBivariate.SatisfiesMultiplicityConstraints Q' points m := by
          intro point hpoint
          have hquot := witness_hasMultiplicity_quot (hR point hpoint)
            ((CBivariate.hasMultiplicity_iff_hasMultiplicityAtLeast Q (m + 1)
              point.1 point.2).mpr (hQ point hpoint))
          exact (CBivariate.hasMultiplicity_iff_hasMultiplicityAtLeast Q' m
            point.1 point.2).mp hquot
        refine ⟨?_, (ih Q').mpr hQ'⟩
        have hCc : CBivariate.SatisfiesMultiplicityConstraints
            (CBivariate.ofYConstant c) points (m + 1) := by
          intro point hpoint
          have hLin : CBivariate.HasMultiplicityAtLeast
              (CBivariate.linearYDivisor R * Q') point.1 point.2 (m + 1) :=
            LeeOSullivan.hasMultiplicityAtLeast_linearYDivisor_mul R
              (hR point hpoint) (hQ' point hpoint)
          have hsub := witness_hasMultiplicityAtLeast_sub
            (hQ point hpoint) hLin
          have hdec : Q - CBivariate.linearYDivisor R * Q' =
              CBivariate.ofYConstant c := by
            conv_lhs => rw [witness_divByLinearY_decomposition Q R]
            ring
          rwa [hdec] at hsub
        have hY : ∀ j, 0 < j →
            (CBivariate.ofYConstant c).val.coeff j = 0 := by
          intro j hj
          have hcoeffj : CPolynomial.coeff (CBivariate.ofYConstant c) j = 0 := by
            show CPolynomial.coeff (CPolynomial.C c) j = 0
            rw [CPolynomial.coeff_C]
            simp [Nat.pos_iff_ne_zero.mp hj]
          exact hcoeffj
        have hdvd := LeeOSullivan.coeffY_dvd_vanishingPolynomial_pow_of_multiplicity
          (CPolynomial.VanishingPolynomialContext.direct (F := F))
          (P := CBivariate.ofYConstant c) (m := m + 1) (n := 0)
          hdistinct (by omega) hY hCc
        rcases hdvd with ⟨W, hW⟩
        refine ⟨W, ?_⟩
        have hcoeff0 : (CBivariate.ofYConstant c).val.coeff 0 = c := by
          have hcoeffc : CPolynomial.coeff (CBivariate.ofYConstant c) 0 = c := by
            show CPolynomial.coeff (CPolynomial.C c) 0 = c
            rw [CPolynomial.coeff_C]
            simp
          exact hcoeffc
        rw [hcoeff0] at hW
        simpa [hG, Nat.sub_zero] using hW

/-- The divisibility-based multiplicity checker agrees with the pointwise
Hasse checker on point sets with distinct `x`-coordinates. -/
theorem satisfiesMultiplicityConstraintsViaDivisibilityBool_eq
    (Mul : CPolynomial.MulContext F) (Mod : CPolynomial.ModContext F)
    {points : Array (F × F)} (R : CPolynomial F)
    (hdistinct : DistinctXCoordinates points)
    (hR : ∀ point, point ∈ points.toList → CPolynomial.eval point.1 R = point.2)
    (m : Nat) (Q : CBivariate F) :
    satisfiesMultiplicityConstraintsViaDivisibilityBool Mul Mod
        (CPolynomial.vanishingPolynomialArray (points.map fun p ↦ p.1)) R m Q =
      CBivariate.satisfiesMultiplicityConstraintsBool Q points m := by
  rw [Bool.eq_iff_iff, witness_viaDivisibility_iff Mul Mod R hdistinct hR m Q,
    CBivariate.satisfiesMultiplicityConstraintsBool_iff_hasMultiplicity,
    CBivariate.satisfiesMultiplicityConstraints_iff_hasMultiplicity]

/-- The divisibility-based witness recognizer agrees with
`interpolationWitnessIsValidBool` on point sets with distinct
`x`-coordinates. -/
theorem interpolationWitnessIsValidViaDivisibilityBool_eq
    (V : CPolynomial.VanishingPolynomialContext F)
    (E : CPolynomial.BatchEvalContext F)
    (Mul : CPolynomial.MulContext F) (Mod : CPolynomial.ModContext F)
    {points : Array (F × F)} (params : GSInterpParams)
    (hdistinct : DistinctXCoordinates points) (Q : CBivariate F) :
    interpolationWitnessIsValidViaDivisibilityBool V E Mul Mod points params Q =
      interpolationWitnessIsValidBool points params Q := by
  have hR : ∀ point, point ∈ points.toList →
      CPolynomial.eval point.1
        (CPolynomial.interpolateCoefficientFormWithVanishing E
          (CPolynomial.vanishingPolynomialArray
            (points.map fun point ↦ point.1)) points) =
        point.2 := by
    intro point hpoint
    have heval :=
      CPolynomial.interpolateCoefficientForm_eval_point V E hdistinct hpoint
    rw [CPolynomial.interpolateCoefficientForm, V.correct] at heval
    exact heval
  simp only [interpolationWitnessIsValidViaDivisibilityBool,
    interpolationWitnessIsValidBool, V.correct]
  rw [satisfiesMultiplicityConstraintsViaDivisibilityBool_eq Mul Mod _
    hdistinct hR params.multiplicity Q (points := points)]

end GuruswamiSudan

end CompPoly
