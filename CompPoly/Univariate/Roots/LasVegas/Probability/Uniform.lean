/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Probability.Basic

/-!
# Uniform Probe Distributions for Las Vegas Root Splitting

Idealized uniform sources for the Las Vegas probability story: uniform field
elements induced by a lazy enumeration, independent uniform coefficient arrays,
and the uniform probe-polynomial distribution they induce.

The deep target of this module is pair-evaluation uniformity: a uniform probe
with at least two sampled coefficients evaluates at two distinct field points
to a uniform pair on `F × F`.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Uniform sampling from enumeration indices. -/
noncomputable def uniformFieldIndexPMF {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    PMF (Fin enumeration.size) :=
  PMF.ofFinset
    (fun _ : Fin enumeration.size ↦ (enumeration.size : ℝ≥0∞)⁻¹)
    Finset.univ
    (by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hne : (enumeration.size : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt enumeration.size_pos
      simpa [Fintype.card_fin] using
        ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top enumeration.size))
    (by
      intro i hi
      exact (hi (Finset.mem_univ i)).elim)

/-- Uniform field-element sampling induced by a lazy enumeration. -/
noncomputable def uniformFieldElementPMF {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    PMF F :=
  (uniformFieldIndexPMF enumeration).map enumeration.elem

/-- Complete injective enumerations put every field element in the PMF support. -/
theorem uniformFieldElementPMF_support_eq_univ {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) :
    (uniformFieldElementPMF enumeration.toFieldEnumeration).support = Set.univ := by
  ext a
  simp [uniformFieldElementPMF, uniformFieldIndexPMF]
  exact enumeration.toFieldEnumeration.complete a

/-- Every field element has probability `1 / q` under a uniform field enumeration. -/
theorem uniformFieldElementPMF_apply {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) (a : F) :
    uniformFieldElementPMF enumeration.toFieldEnumeration a = (q : ℝ≥0∞)⁻¹ := by
  rcases enumeration.toFieldEnumeration.complete a with ⟨i, hi⟩
  simp [uniformFieldElementPMF, uniformFieldIndexPMF, enumeration.size_eq_q]
  trans ∑ j : Fin enumeration.toFieldEnumeration.size, if j = i then (q : ℝ≥0∞)⁻¹ else 0
  · apply Finset.sum_congr rfl
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [hi]
    · have hne : a ≠ enumeration.toFieldEnumeration.elem j := by
        intro haj
        apply hji
        apply enumeration.injective_elem
        rw [hi]
        exact haj.symm
      simp [hne, hji]
  · simp

/--
Uniform PMF over coefficient arrays of fixed length, sampled independently from
the supplied field enumeration.
-/
noncomputable def uniformCoefficientArrayPMF {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    Nat → PMF (Array F)
  | 0 => pure #[]
  | n + 1 => do
      let coeffs ← uniformCoefficientArrayPMF enumeration n
      let coeff ← uniformFieldElementPMF enumeration
      pure (coeffs.push coeff)

private theorem uniformCoefficientArrayPMF_support_size {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    ∀ coefficientCount {coeffs : Array F},
      coeffs ∈ (uniformCoefficientArrayPMF enumeration coefficientCount).support →
        coeffs.size = coefficientCount := by
  intro coefficientCount
  induction coefficientCount with
  | zero =>
      intro coeffs hcoeffs
      rw [uniformCoefficientArrayPMF] at hcoeffs
      have heq : coeffs = #[] :=
        (PMF.mem_support_pure_iff (a := (#[] : Array F)) (a' := coeffs)).mp hcoeffs
      simp [heq]
  | succ n ih =>
      intro coeffs hcoeffs
      rw [uniformCoefficientArrayPMF] at hcoeffs
      change coeffs ∈
        ((uniformCoefficientArrayPMF enumeration n).bind fun coeffs0 ↦
          (uniformFieldElementPMF enumeration).bind fun coeff ↦
            pure (coeffs0.push coeff)).support at hcoeffs
      rw [PMF.mem_support_bind_iff] at hcoeffs
      rcases hcoeffs with ⟨coeffs0, hcoeffs0, htail⟩
      rw [PMF.mem_support_bind_iff] at htail
      rcases htail with ⟨coeff, _hcoeff, hpush⟩
      have hpush_eq : coeffs = coeffs0.push coeff :=
        (PMF.mem_support_pure_iff (a := coeffs0.push coeff) (a' := coeffs)).mp hpush
      subst coeffs
      simp [ih hcoeffs0]

private theorem ofArray_natDegree_lt_size_or_eq_zero {F : Type*}
    [Zero F] [BEq F] [LawfulBEq F] (coeffs : Array F) :
    (CPolynomial.ofArray coeffs).natDegree < coeffs.size ∨ CPolynomial.ofArray coeffs = 0 := by
  cases hval : (CPolynomial.ofArray coeffs).val.size with
  | zero =>
      right
      apply CPolynomial.ext
      exact Array.eq_empty_of_size_eq_zero hval
  | succ n =>
      left
      have hnat : (CPolynomial.ofArray coeffs).natDegree = n := by
        simp [CPolynomial.natDegree, hval]
      have htrim_le : (CPolynomial.ofArray coeffs).val.size ≤ coeffs.size := by
        simpa [CPolynomial.ofArray] using
          CPolynomial.Raw.Trim.size_le_size (p := (coeffs : CPolynomial.Raw F))
      omega

/-- Uniform probe polynomial of degree bounded by the supplied coefficient count. -/
noncomputable def uniformProbePMF {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (coefficientCount : Nat) :
    PMF (CPolynomial F) :=
  (uniformCoefficientArrayPMF enumeration coefficientCount).map fun coeffs ↦
    CPolynomial.ofArray coeffs

/--
Probes sampled with `coefficientCount` coefficients have degree below that
bound, unless zero.
-/
theorem uniformProbePMF_support_natDegree_lt {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (coefficientCount : Nat)
    {probe : CPolynomial F}
    (hprobe : probe ∈ (uniformProbePMF enumeration coefficientCount).support) :
    CPolynomial.natDegree probe < coefficientCount ∨ probe = 0 := by
  rw [uniformProbePMF, PMF.mem_support_map_iff] at hprobe
  rcases hprobe with ⟨coeffs, hcoeffs, hprobe_eq⟩
  subst probe
  have hsize := uniformCoefficientArrayPMF_support_size enumeration coefficientCount hcoeffs
  simpa [hsize] using ofArray_natDegree_lt_size_or_eq_zero (F := F) coeffs

private theorem uniformCoefficientArrayPMF_zero {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) :
    uniformCoefficientArrayPMF enumeration 0 = PMF.pure #[] := by
  rw [uniformCoefficientArrayPMF]
  rfl

private theorem uniformCoefficientArrayPMF_succ {F : Type*} [Zero F]
    (enumeration : FieldEnumeration F) (n : Nat) :
    uniformCoefficientArrayPMF enumeration (n + 1) =
      (uniformCoefficientArrayPMF enumeration n).bind fun coeffs ↦
        (uniformFieldElementPMF enumeration).bind fun coeff ↦
          PMF.pure (coeffs.push coeff) := by
  rw [uniformCoefficientArrayPMF]
  rfl

/-- Appending a coefficient shifts the evaluation by the corresponding monomial. -/
private theorem eval_ofArray_push {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (coeffs : Array F) (c : F) (z : F) :
    CPolynomial.eval z (CPolynomial.ofArray (coeffs.push c)) =
      CPolynomial.eval z (CPolynomial.ofArray coeffs) + c * z ^ coeffs.size := by
  rw [CPolynomial.eval_toPoly, CPolynomial.eval_toPoly,
    CPolynomial.ofArray_toPoly, CPolynomial.ofArray_toPoly]
  have hpush : CPolynomial.Raw.toPoly (coeffs.push c) =
      CPolynomial.Raw.toPoly coeffs +
        Polynomial.C c * Polynomial.X ^ coeffs.size := by
    apply Polynomial.ext
    intro i
    rw [Polynomial.coeff_add, CPolynomial.Raw.coeff_toPoly, CPolynomial.Raw.coeff_toPoly,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    show (coeffs.push c).getD i 0 = coeffs.getD i 0 + c * if i = coeffs.size then 1 else 0
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push]
    by_cases hi : i = coeffs.size
    · subst hi
      simp
    · simp [hi]
  rw [hpush, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- Evaluation of the two-coefficient probe `c₀ + c₁ * X`. -/
private theorem eval_ofArray_pair {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (c0 c1 z : F) :
    CPolynomial.eval z (CPolynomial.ofArray #[c0, c1]) = c0 + c1 * z := by
  have hempty : CPolynomial.Raw.toPoly (#[] : Array F) = 0 := by
    apply Polynomial.ext
    intro i
    rw [CPolynomial.Raw.coeff_toPoly]
    simp [CPolynomial.Raw.coeff]
  have h1 : (#[c0, c1] : Array F) = ((#[] : Array F).push c0).push c1 := rfl
  rw [h1, eval_ofArray_push, eval_ofArray_push]
  rw [CPolynomial.eval_toPoly, CPolynomial.ofArray_toPoly, hempty]
  simp

private theorem toOuterMeasure_congr_on_support {α : Type*} (p : PMF α) {S T : Set α}
    (h : ∀ a ∈ p.support, (a ∈ S ↔ a ∈ T)) :
    p.toOuterMeasure S = p.toOuterMeasure T := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro a
  by_cases hz : p a = 0
  · rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp [hS, hT, hz]
  · rw [Set.indicator_apply, Set.indicator_apply,
      if_congr (h a ((p.mem_support_iff a).mpr hz)) rfl rfl]

/--
The two-coefficient uniform array hits any prescribed evaluation pair at two
distinct points with probability exactly `q⁻¹ * q⁻¹`.
-/
private theorem uniformCoefficientArrayPMF_two_eval_pair {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) {a b : F} (hab : a ≠ b) (x y : F) :
    eventProbability
        (uniformCoefficientArrayPMF enumeration.toFieldEnumeration 2)
        {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
          CPolynomial.eval b (CPolynomial.ofArray coeffs) = y} =
      (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  set c1s : F := (x - y) / (a - b) with hc1s
  set c0s : F := x - c1s * a with hc0s
  have harr : uniformCoefficientArrayPMF enumeration.toFieldEnumeration 2 =
      (uniformFieldElementPMF enumeration.toFieldEnumeration).bind fun c0 ↦
        (uniformFieldElementPMF enumeration.toFieldEnumeration).bind fun c1 ↦
          (PMF.pure #[c0, c1] : PMF (Array F)) := by
    rw [show (2 : Nat) = 1 + 1 from rfl, uniformCoefficientArrayPMF_succ,
      show (1 : Nat) = 0 + 1 from rfl, uniformCoefficientArrayPMF_succ,
      uniformCoefficientArrayPMF_zero]
    simp only [PMF.pure_bind, PMF.bind_bind]
    rfl
  have hmem : ∀ c0 c1 : F,
      ((#[c0, c1] : Array F) ∈
        {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
          CPolynomial.eval b (CPolynomial.ofArray coeffs) = y}) ↔
        (c0 = c0s ∧ c1 = c1s) := by
    intro c0 c1
    rw [Set.mem_setOf_eq, eval_ofArray_pair, eval_ofArray_pair]
    constructor
    · rintro ⟨hx, hy⟩
      have hc1 : c1 = c1s := by
        rw [hc1s, eq_div_iff hab']
        rw [← hx, ← hy]
        ring
      refine ⟨?_, hc1⟩
      rw [hc0s, ← hc1, ← hx]
      ring
    · rintro ⟨h0, h1⟩
      subst h0
      subst h1
      constructor
      · rw [hc0s]
        ring
      · rw [hc0s, hc1s]
        field_simp
        ring
  rw [eventProbability, harr, PMF.toOuterMeasure_bind_apply]
  have hstep : ∀ c0 : F,
      ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind fun c1 ↦
          (PMF.pure #[c0, c1] : PMF (Array F))).toOuterMeasure
        {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
          CPolynomial.eval b (CPolynomial.ofArray coeffs) = y} =
      if c0 = c0s then (q : ℝ≥0∞)⁻¹ else 0 := by
    intro c0
    rw [PMF.toOuterMeasure_bind_apply]
    by_cases hc0 : c0 = c0s
    · rw [if_pos hc0]
      calc (∑' c1 : F, uniformFieldElementPMF enumeration.toFieldEnumeration c1 *
              (PMF.pure #[c0, c1] : PMF (Array F)).toOuterMeasure
                {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
                  CPolynomial.eval b (CPolynomial.ofArray coeffs) = y})
          = ∑' c1 : F, if c1 = c1s then
              uniformFieldElementPMF enumeration.toFieldEnumeration c1 else 0 := by
            apply tsum_congr
            intro c1
            rw [PMF.toOuterMeasure_pure_apply]
            by_cases hc1 : c1 = c1s
            · rw [if_pos ((hmem c0 c1).2 ⟨hc0, hc1⟩), if_pos hc1]
              simp
            · rw [if_neg (fun hin ↦ hc1 ((hmem c0 c1).1 hin).2), if_neg hc1]
              simp
        _ = uniformFieldElementPMF enumeration.toFieldEnumeration c1s :=
            tsum_ite_eq c1s _
        _ = (q : ℝ≥0∞)⁻¹ := uniformFieldElementPMF_apply enumeration c1s
    · rw [if_neg hc0]
      calc (∑' c1 : F, uniformFieldElementPMF enumeration.toFieldEnumeration c1 *
              (PMF.pure #[c0, c1] : PMF (Array F)).toOuterMeasure
                {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
                  CPolynomial.eval b (CPolynomial.ofArray coeffs) = y})
          = ∑' _c1 : F, (0 : ℝ≥0∞) := by
            apply tsum_congr
            intro c1
            rw [PMF.toOuterMeasure_pure_apply,
              if_neg (fun hin ↦ hc0 ((hmem c0 c1).1 hin).1)]
            simp
        _ = 0 := tsum_zero
  calc (∑' c0 : F, uniformFieldElementPMF enumeration.toFieldEnumeration c0 *
          ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind fun c1 ↦
            (PMF.pure #[c0, c1] : PMF (Array F))).toOuterMeasure
            {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
              CPolynomial.eval b (CPolynomial.ofArray coeffs) = y})
      = ∑' c0 : F, if c0 = c0s then
          uniformFieldElementPMF enumeration.toFieldEnumeration c0 * (q : ℝ≥0∞)⁻¹
        else 0 := by
        apply tsum_congr
        intro c0
        rw [hstep c0]
        by_cases hc0 : c0 = c0s
        · rw [if_pos hc0, if_pos hc0]
        · rw [if_neg hc0, if_neg hc0]
          simp
    _ = uniformFieldElementPMF enumeration.toFieldEnumeration c0s * (q : ℝ≥0∞)⁻¹ :=
        tsum_ite_eq c0s _
    _ = (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
        rw [uniformFieldElementPMF_apply enumeration c0s]

/--
The uniform coefficient-array source hits any prescribed evaluation pair at two
distinct points with probability exactly `q⁻¹ * q⁻¹`, for any coefficient count
of at least two.
-/
private theorem uniformCoefficientArrayPMF_eval_pair {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) {a b : F} (hab : a ≠ b) :
    ∀ n : Nat, 2 ≤ n → ∀ x y : F,
      eventProbability
          (uniformCoefficientArrayPMF enumeration.toFieldEnumeration n)
          {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
            CPolynomial.eval b (CPolynomial.ofArray coeffs) = y} =
        (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro x y
      exact uniformCoefficientArrayPMF_two_eval_pair enumeration hab x y
  | succ n hn ih =>
      intro x y
      rw [eventProbability, uniformCoefficientArrayPMF_succ, PMF.bind_comm,
        PMF.toOuterMeasure_bind_apply]
      have hterm : ∀ c : F,
          ((uniformCoefficientArrayPMF enumeration.toFieldEnumeration n).bind
              fun coeffs ↦ (PMF.pure (coeffs.push c) : PMF (Array F))).toOuterMeasure
            {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
              CPolynomial.eval b (CPolynomial.ofArray coeffs) = y} =
          (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
        intro c
        have hmapped : ((uniformCoefficientArrayPMF enumeration.toFieldEnumeration n).bind
            fun coeffs ↦ (PMF.pure (coeffs.push c) : PMF (Array F))) =
            (uniformCoefficientArrayPMF enumeration.toFieldEnumeration n).map
              (fun coeffs ↦ coeffs.push c) := rfl
        have hcongr := toOuterMeasure_congr_on_support
          (p := uniformCoefficientArrayPMF enumeration.toFieldEnumeration n)
          (S := (fun coeffs : Array F ↦ coeffs.push c) ⁻¹'
            {coeffs : Array F | CPolynomial.eval a (CPolynomial.ofArray coeffs) = x ∧
              CPolynomial.eval b (CPolynomial.ofArray coeffs) = y})
          (T := {coeffs : Array F |
            CPolynomial.eval a (CPolynomial.ofArray coeffs) = x - c * a ^ n ∧
              CPolynomial.eval b (CPolynomial.ofArray coeffs) = y - c * b ^ n})
          (fun coeffs hsupp ↦ by
            have hsize := uniformCoefficientArrayPMF_support_size
              enumeration.toFieldEnumeration n hsupp
            rw [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_setOf_eq,
              eval_ofArray_push, eval_ofArray_push, hsize]
            constructor
            · rintro ⟨h1, h2⟩
              constructor
              · rw [← h1]; ring
              · rw [← h2]; ring
            · rintro ⟨h1, h2⟩
              rw [h1, h2]
              constructor <;> ring)
        rw [hmapped, PMF.toOuterMeasure_map_apply, hcongr]
        have hev := ih (x - c * a ^ n) (y - c * b ^ n)
        rw [eventProbability] at hev
        exact hev
      trans (∑' c : F, uniformFieldElementPMF enumeration.toFieldEnumeration c *
        ((q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹))
      · exact tsum_congr fun c ↦ by rw [hterm c]
      · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, _root_.one_mul]

/--
Pair-evaluation uniformity: a uniform probe with at least two sampled
coefficients evaluates at two distinct points to a uniform pair on `F × F`.

For a fixed coefficient tail, the map
`(c₀, c₁) ↦ (c₀ + c₁ * a + tail(a), c₀ + c₁ * b + tail(b))` is a bijection of
`F × F` because `a ≠ b`, so exactly one of the `q ^ 2` equally likely
`(c₀, c₁)` choices hits the target pair `(x, y)`.
-/
theorem uniformProbePMF_eval_pair_apply {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q)
    (coefficientCount : Nat) {a b : F} (x y : F)
    (hab : a ≠ b) (hcount : 2 ≤ coefficientCount) :
    eventProbability
        (uniformProbePMF enumeration.toFieldEnumeration coefficientCount)
        {h | CPolynomial.eval a h = x ∧ CPolynomial.eval b h = y} =
      (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
  rw [eventProbability, uniformProbePMF, PMF.toOuterMeasure_map_apply]
  have hev := uniformCoefficientArrayPMF_eval_pair enumeration hab
    coefficientCount hcount x y
  rw [eventProbability] at hev
  exact hev

/-- Independent uniform probe tables of a fixed length. -/
noncomputable def uniformProbeTablePMF {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (enumeration : FieldEnumeration F) (coefficientCount : Nat) :
    Nat → PMF (List (CPolynomial F))
  | 0 => PMF.pure []
  | attempts + 1 =>
      (uniformProbePMF enumeration coefficientCount).bind fun h ↦
        (uniformProbeTablePMF enumeration coefficientCount attempts).map (List.cons h)

/-- Every pair of field elements is equally likely under two independent uniform draws. -/
theorem uniformFieldElementPMF_pair_apply {F : Type*} [Zero F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) (xy : F × F) :
    ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind
      fun x ↦ (uniformFieldElementPMF enumeration.toFieldEnumeration).map
        fun y ↦ (x, y)) xy = (q : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹ := by
  obtain ⟨x, y⟩ := xy
  rw [PMF.bind_apply]
  have hxy : ∀ x' : F,
      ((uniformFieldElementPMF enumeration.toFieldEnumeration).map
        fun y' ↦ (x', y')) (x, y) =
      if x' = x then uniformFieldElementPMF enumeration.toFieldEnumeration y else 0 := by
    intro x'
    rw [PMF.map_apply]
    by_cases hx : x' = x
    · subst hx
      rw [if_pos rfl]
      trans (∑' y' : F, if y' = y then
          uniformFieldElementPMF enumeration.toFieldEnumeration y' else 0)
      · apply tsum_congr
        intro y'
        by_cases hy : y' = y
        · subst hy
          simp
        · rw [if_neg fun hp ↦ hy (Prod.ext_iff.mp hp).2.symm, if_neg hy]
      · exact tsum_ite_eq y _
    · rw [if_neg hx]
      trans (∑' _y' : F, (0 : ℝ≥0∞))
      · apply tsum_congr
        intro y'
        rw [if_neg fun hp ↦ hx ((Prod.ext_iff.mp hp).1.symm)]
      · exact tsum_zero
  trans (∑' x' : F, if x' = x then
      uniformFieldElementPMF enumeration.toFieldEnumeration x' *
        uniformFieldElementPMF enumeration.toFieldEnumeration y else 0)
  · apply tsum_congr
    intro x'
    rw [hxy x']
    by_cases hx : x' = x
    · rw [if_pos hx, if_pos hx]
    · rw [if_neg hx, if_neg hx]
      simp
  · rw [tsum_ite_eq x fun x' ↦ uniformFieldElementPMF enumeration.toFieldEnumeration x' *
        uniformFieldElementPMF enumeration.toFieldEnumeration y,
      uniformFieldElementPMF_apply enumeration x,
      uniformFieldElementPMF_apply enumeration y]

/--
The evaluation pair of a uniform probe at two distinct points pushes forward to
two independent uniform field elements.
-/
theorem uniformProbePMF_map_eval_pair {F : Type*}
    [Field F] [BEq F] [LawfulBEq F] {q : Nat}
    (enumeration : UniformFieldEnumeration F q) (coefficientCount : Nat) {a b : F}
    (hab : a ≠ b) (hcount : 2 ≤ coefficientCount) :
    (uniformProbePMF enumeration.toFieldEnumeration coefficientCount).map
        (fun h ↦ (CPolynomial.eval a h, CPolynomial.eval b h)) =
      (uniformFieldElementPMF enumeration.toFieldEnumeration).bind
        fun x ↦ (uniformFieldElementPMF enumeration.toFieldEnumeration).map
          fun y ↦ (x, y) := by
  apply PMF.ext
  intro xy
  rw [uniformFieldElementPMF_pair_apply enumeration xy]
  obtain ⟨x, y⟩ := xy
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre : ((fun h : CPolynomial F ↦
      (CPolynomial.eval a h, CPolynomial.eval b h)) ⁻¹' {(x, y)}) =
      {h : CPolynomial F | CPolynomial.eval a h = x ∧ CPolynomial.eval b h = y} := by
    ext h
    simp [Prod.ext_iff]
  rw [hpre]
  exact uniformProbePMF_eval_pair_apply enumeration coefficientCount x y hab hcount

/--
If every fiber of a classifier has at most `m` elements out of `q ≤ 2 * (q - m)`,
two independent uniform field values are separated by the classifier with
probability at least `1 / 2`.
-/
theorem uniformPair_separated_probability_ge_half_of_fiber_card_le {F : Type*}
    [Zero F] [Fintype F] {β : Type*} {q m : Nat}
    (enumeration : UniformFieldEnumeration F q) (f : F → β)
    (hcard : Fintype.card F = q)
    (hfiber : ∀ x : F, ∃ s : Finset F, (∀ y : F, f y = f x → y ∈ s) ∧ s.card ≤ m)
    (hhalf : q ≤ 2 * (q - m)) :
    (2 : ℝ≥0∞)⁻¹ ≤
      eventProbability
        ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind
          fun x ↦ (uniformFieldElementPMF enumeration.toFieldEnumeration).map
            fun y ↦ (x, y))
        {xy : F × F | f xy.1 ≠ f xy.2} := by
  have hq1 : 1 ≤ q := enumeration.q_pos
  have hqne : (q : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqnetop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  set u := uniformFieldElementPMF enumeration.toFieldEnumeration with hu
  have hN_ge : ∀ x : F, q - m ≤
      (Finset.univ.filter fun y : F ↦ f x ≠ f y).card := by
    intro x
    have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
      (fun y : F ↦ f x = f y)
    have hsame : (Finset.univ.filter fun y : F ↦ f x = f y).card ≤ m := by
      obtain ⟨s, hsub, hcard_s⟩ := hfiber x
      refine le_trans (Finset.card_le_card fun y hy ↦ ?_) hcard_s
      exact hsub y (Finset.mem_filter.mp hy).2.symm
    have hcardu : (Finset.univ : Finset F).card = q := by
      rw [Finset.card_univ, hcard]
    have hfeq : (Finset.univ.filter fun y : F ↦ f x ≠ f y) =
        Finset.univ.filter fun y : F ↦ ¬ f x = f y := by
      apply Finset.filter_congr
      intro y _
      exact Iff.rfl
    rw [hfeq]
    omega
  have hinner : ∀ x : F,
      u.toOuterMeasure {y : F | f x ≠ f y} =
        ((Finset.univ.filter fun y : F ↦ f x ≠ f y).card : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
    intro x
    rw [PMF.toOuterMeasure_apply, tsum_fintype, Finset.sum_indicator_eq_sum_filter]
    have hfeq : (Finset.univ.filter fun y : F ↦ y ∈ {y : F | f x ≠ f y}) =
        Finset.univ.filter fun y : F ↦ f x ≠ f y := by
      apply Finset.filter_congr
      intro y _
      exact Iff.rfl
    rw [hfeq]
    calc (∑ y ∈ Finset.univ.filter (fun y : F ↦ f x ≠ f y), u y)
        = ∑ _y ∈ Finset.univ.filter (fun y : F ↦ f x ≠ f y), (q : ℝ≥0∞)⁻¹ :=
          Finset.sum_congr rfl fun y _ ↦ by
            rw [hu]
            exact uniformFieldElementPMF_apply enumeration y
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmap : ∀ x : F,
      (u.map fun y ↦ (x, y)).toOuterMeasure {xy : F × F | f xy.1 ≠ f xy.2} =
        ((Finset.univ.filter fun y : F ↦ f x ≠ f y).card : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
    intro x
    rw [PMF.toOuterMeasure_map_apply]
    exact hinner x
  have hev : eventProbability (u.bind fun x ↦ u.map fun y ↦ (x, y))
      {xy : F × F | f xy.1 ≠ f xy.2} =
        ∑' x : F, u x *
          (((Finset.univ.filter fun y : F ↦ f x ≠ f y).card : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹) := by
    rw [eventProbability, PMF.toOuterMeasure_bind_apply]
    exact tsum_congr fun x ↦ by rw [hmap x]
  have hstepA : (2 : ℝ≥0∞)⁻¹ ≤ ((q - m : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hqne) (Or.inl hqnetop)]
    calc (2 : ℝ≥0∞)⁻¹ * q
        ≤ (2 : ℝ≥0∞)⁻¹ * ((2 * (q - m) : ℕ) : ℝ≥0∞) :=
          _root_.mul_le_mul_right (by exact_mod_cast hhalf) _
      _ = ((q - m : ℕ) : ℝ≥0∞) := by
          push_cast
          rw [← _root_.mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
            _root_.one_mul]
  rw [hev]
  calc (2 : ℝ≥0∞)⁻¹
      ≤ ((q - m : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := hstepA
    _ = ∑' _x : F, (q : ℝ≥0∞)⁻¹ * (((q - m : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
          ← _root_.mul_assoc, ENNReal.mul_inv_cancel hqne hqnetop, _root_.one_mul]
    _ ≤ ∑' x : F, u x *
          (((Finset.univ.filter fun y : F ↦ f x ≠ f y).card : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹) := by
        apply ENNReal.tsum_le_tsum
        intro x
        rw [hu, uniformFieldElementPMF_apply enumeration x]
        exact _root_.mul_le_mul_right
          (_root_.mul_le_mul_left (Nat.cast_le.mpr (hN_ge x)) _) _

end FiniteField

end Roots

end CPolynomial

end CompPoly
