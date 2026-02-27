/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.CategoryTheory.Category.Basic
import CompPoly.Univariate.ToPoly

/-!
  # Computable Division and Modulus of Polynomials

  This file defines the operations `CPolynomial.div` and `CPolynomial.mod` and
  proves their equivalence with respect to their mathlib's counterparts.

  Main definitions:
  - `CPolynomial.div`: the division between two canonical polynomials
  - `CPolynomial.mod`: the modulus between two canonical polynomials

  Main results:
  - `CPolynomial.div_toPoly`: ∀ p q, `CPolynomial.div p q` = `Polynomial.div p.toPoly q.toPoly`
  - `CPolynomial.mod_toPoly`: ∀ p q, `CPolynomial.mod p q` = `Polynomial.mod p.toPoly q.toPoly`
-/

open Polynomial

namespace CompPoly

namespace CPolynomial

section Operations

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

namespace Raw

/-! Lemmas required to prove the termination of CPolynomial.Raw.divModByMonicAux -/

omit [BEq R] [LawfulBEq R] in
/-- `toPoly` respects negation for Raw polynomials -/
lemma toPoly_neg (p : CPolynomial.Raw R) :
    (-p).toPoly = -p.toPoly := by
  ext n
  simp only [coeff_toPoly, Polynomial.coeff_neg]
  exact neg_coeff p n

/-- `toPoly` respects subtraction for Raw polynomials -/
lemma toPoly_sub (p q : CPolynomial.Raw R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  have h_sub : (p - q).toPoly = p.toPoly + (-q).toPoly := by
    have h_add : (p + (-q)).toPoly = p.toPoly + (-q).toPoly := by
      grind
    convert h_add using 1
  rw [ h_sub, toPoly_neg, sub_eq_add_neg ]

/-- `toPoly` respects multiplication for Raw polynomials -/
lemma toPoly_mul (p q : CPolynomial.Raw R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  convert toPoly_mul_coeff p q using 1
  simp [ Polynomial.ext_iff, Polynomial.coeff_mul ]

/-- `toPoly` respects exponentiation by naturals for Raw polynomials -/
lemma toPoly_pow (p : CPolynomial.Raw R) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := by
  induction' n with n ih generalizing p <;> simp_all [ pow_succ ]
  · convert toPoly_one <;> infer_instance
  · rw [ pow_succ', toPoly_mul, ih ]

/-- The trim of a Raw polynomial is empty if and only if it is `0` -/
lemma trim_size_zero_iff_toPoly_zero (p : CPolynomial.Raw R) :
    p.trim.size = 0 ↔ p.toPoly = 0 := by
  constructor <;> intro h
  · rw [ ← toPoly_trim ] ; aesop
  · have h_trim_zero : p.trim = 0 := by
      convert toImpl_toPoly p
      · convert toImpl_toPoly p |> Eq.symm
      · convert toImpl_toPoly p
        unfold toPoly at *; aesop
    aesop

/-- The trim of a Raw polynomial is not empty if and only if it is not `0` -/
lemma trim_size_pos_iff_toPoly_ne_zero (p : CPolynomial.Raw R) :
    0 < p.trim.size ↔ p.toPoly ≠ 0 := by
  constructor <;> intro h
  · contrapose! h
    convert trim_size_zero_iff_toPoly_zero p |>.2 h |> le_of_eq
  · contrapose! h
    convert trim_size_zero_iff_toPoly_zero p |>.1 ( le_antisymm h ( Nat.zero_le _ ) ) using 1

/-- The size of the trim of a Raw polynomial is equal to its `natDegree` plus 1 -/
lemma trim_size_eq_natDegree_succ (p : CPolynomial.Raw R) (hp : p.toPoly ≠ 0) :
    p.trim.size = p.toPoly.natDegree + 1 := by
  obtain ⟨q, hq⟩ : ∃ q : Polynomial R, p.toPoly = q ∧ q ≠ 0 := by
    use p.toPoly
  have h_trim_size_eq : p.toPoly.toImpl = p.trim := by
    exact toImpl_toPoly p
  rw [ ← h_trim_size_eq, hq.1 ]
  unfold Polynomial.toImpl
  cases h : q.degree <;> simp_all [ Polynomial.natDegree ]

/-- `toPoly` respects `leadingCoeff` for Raw polynomials -/
lemma leadingCoeff_toPoly (p : CPolynomial.Raw R) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  by_contra h_neq
  set q : Polynomial R := p.toPoly
  have hq : p.leadingCoeff = q.leadingCoeff := by
    by_cases hq : q = 0
    · convert trim_size_zero_iff_toPoly_zero p |>.2 hq |> fun h => ?_
      unfold leadingCoeff
      unfold Array.getLastD; aesop
    · have hq_deg : q.natDegree + 1 = p.trim.size := by
        convert trim_size_eq_natDegree_succ p hq
        · exact Eq.symm (trim_size_eq_natDegree_succ p hq)
        · convert trim_size_eq_natDegree_succ p hq
      have hq_coeff : q.coeff (q.natDegree) = p.trim.coeff (q.natDegree) := by
        rw [ ← coeff_toPoly ]
        rw [ toPoly_trim ]
      simp_all [ leadingCoeff ]
      convert h_neq ?_
      simp [ Array.getLastD, hq_deg.symm ]
  contradiction

/-- `toPoly` respects `natDegree` for Raw polynomials -/
lemma natDegree_eq_toPoly_natDegree (p : CPolynomial.Raw R) (hp : p.toPoly ≠ 0) :
    p.natDegree = p.toPoly.natDegree := by
  have h_def : p.natDegree = p.trim.size - 1 := by
    rw [ natDegree, trim ]
    cases h : p.lastNonzero <;> simp
  have h_toPoly_def : (p.toPoly).natDegree = p.trim.size - 1 := by
    have := trim_size_eq_natDegree_succ p hp
    rw [ this, Nat.add_sub_cancel ]
  rw [h_def, h_toPoly_def]

/-- `toPoly` respects `monic` for Raw polynomials -/
lemma monic_iff_toPoly_monic (q : CPolynomial.Raw R) :
    q.monic = true ↔ q.toPoly.Monic := by
  have h_leading_coeff : q.leadingCoeff = q.toPoly.leadingCoeff := leadingCoeff_toPoly q
  unfold monic
  simp_all only [beq_iff_eq]
  rfl

/-- Helper lemma for rewriting `toPoly` of a monomial -/
private lemma toPoly_monom (lc : R) (n : ℕ) :
    (C lc * X ^ n : CPolynomial.Raw R).toPoly = Polynomial.C lc * Polynomial.X ^ n := by
  rw [toPoly_mul (C lc) (X ^ n), toPoly_C lc, toPoly_pow X n, toPoly_X ]

/-- Helper lemma for rewriting `toPoly` in the argument of the recursive call of `divModByMonicAux` -/
private lemma toPoly_div_step (p q : CPolynomial.Raw R) :
    (p - q * (C p.leadingCoeff * (X : CPolynomial.Raw R) ^ (p.natDegree - q.natDegree))).toPoly =
    p.toPoly - q.toPoly * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree)) := by
  convert toPoly_sub p ( q * ( C p.leadingCoeff * (X : CPolynomial.Raw R) ^ ( p.natDegree - q.natDegree ) ) ) using 1
  have h_poly_mul : ∀ (p q : CPolynomial.Raw R), (p * q).toPoly = p.toPoly * q.toPoly := by
    exact fun p q => toPoly_mul p q
  convert rfl using 2
  convert h_poly_mul q ( C p.leadingCoeff * X ^ ( p.natDegree - q.natDegree ) ) using 1
  congr! 1
  convert toPoly_monom p.leadingCoeff ( p.natDegree - q.natDegree ) |> Eq.symm using 1

/-- The argument of the recursive call of `divModByMonicAux` has a `degree` smaller than the original argument  -/
lemma div_step_degree_lt (p q : CPolynomial.Raw R)
    (hp : p.toPoly ≠ 0) (hq : q.toPoly.Monic)
    (hdeg : Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly) :
    (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))).toPoly.degree <
      p.toPoly.degree := by
  norm_num at *
  have := @Polynomial.div_wf_lemma R
  convert this ⟨ hdeg, hp ⟩ hq using 1
  rw [ ← leadingCoeff_toPoly, ← natDegree_eq_toPoly_natDegree ]
  · convert congr_arg Polynomial.degree ( toPoly_div_step p q ) using 1
    rw [ show q.toPoly.natDegree = q.natDegree from ?_ ]
    by_cases hq_zero : q.toPoly = 0
    · simp_all [ Polynomial.Monic.def ]
      cases subsingleton_or_nontrivial R <;> simp_all [ eq_iff_true_of_subsingleton ]
    · rw [ ← natDegree_eq_toPoly_natDegree ]
      exact hq_zero
  · exact hp

/-- If `r` has a `degree` smaller than `p`, `trim r` is smaller than `trim p` -/
lemma trim_size_lt_of_degree_lt (r p : CPolynomial.Raw R)
    (hp : p.toPoly ≠ 0)
    (hdeg : r.toPoly.degree < p.toPoly.degree) :
    r.trim.size < p.trim.size := by
  by_cases hr : r.toPoly = 0
  · have := trim_size_zero_iff_toPoly_zero r
    exact this.mpr hr ▸ trim_size_pos_iff_toPoly_ne_zero p |>.2 hp
  · rw [ trim_size_eq_natDegree_succ, trim_size_eq_natDegree_succ ]
    · exact Nat.succ_lt_succ ( Polynomial.natDegree_lt_natDegree hr hdeg )
    · exact hp
    · exact hr

/-- If the size of `trim q` is smaller or equal to the size of `trim p` then `degree q` ≤ `degree p` -/
lemma degree_le_of_trim_size_le (p q : CPolynomial.Raw R)
    (h1 : q.trim.size ≤ p.trim.size) (h2 : 0 < p.trim.size) :
    Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly := by
  by_cases hp : p.toPoly = 0 <;> by_cases hq : q.toPoly = 0 <;> simp_all [ Polynomial.degree_eq_natDegree ]
  · have hp_zero : p.trim.size = 0 := (trim_size_zero_iff_toPoly_zero p).mpr hp
    linarith
  · have h_deg : q.trim.size = q.toPoly.natDegree + 1 ∧ p.trim.size = p.toPoly.natDegree + 1 := by
      exact ⟨ trim_size_eq_natDegree_succ q hq, trim_size_eq_natDegree_succ p hp ⟩
    linarith

/-- The argument of the recursive call of `divModByMonicAux` has a `trim` smaller than the original argument  -/
lemma divByMonic_wf_termination (p q : CPolynomial.Raw R)
    (hq : q.monic = true) (h1 : q.trim.size ≤ p.trim.size) (h2 : 0 < p.trim.size) :
    (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))).trim.size <
      p.trim.size := by
  have hp : p.toPoly ≠ 0 := (trim_size_pos_iff_toPoly_ne_zero p).mp h2
  have hq_monic : q.toPoly.Monic := (monic_iff_toPoly_monic q).mp hq
  have hdeg : Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly :=
    degree_le_of_trim_size_le p q h1 h2
  exact trim_size_lt_of_degree_lt _ p hp (div_step_degree_lt p q hp hq_monic hdeg)

/-- Division with remainder by a monic polynomial using polynomial long division. -/
def divModByMonicAux (p q : CPolynomial.Raw R) : CPolynomial.Raw R × CPolynomial.Raw R :=
  if hq : q.monic = true then
    go p q hq
  else ⟨0, 0⟩
where
  go (p q : CPolynomial.Raw R) (hq : q.monic = true) : CPolynomial.Raw R × CPolynomial.Raw R :=
    if h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size then
      let z := C p.leadingCoeff * X ^ (p.natDegree - q.natDegree)
      have _wf : (p - q * z).trim.size < p.trim.size :=
        divByMonic_wf_termination p q hq h.1 h.2
      let ⟨e, r⟩ := go (p - q * z) q hq
      ⟨z + e, r⟩
    else ⟨0, p⟩
  termination_by p.trim.size

/-- Division of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def divByMonic (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : CPolynomial.Raw R` by a monic `q : CPolynomial.Raw R`. -/
def modByMonic (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (divModByMonicAux p q).2

/-- Division of two `CPolynomial.Raw`s. -/
def div [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `CPolynomial.Raw`s. -/
def mod [Field R] (p q : CPolynomial.Raw R) : CPolynomial.Raw R :=
  p.modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [Field R] : Div (CPolynomial.Raw R) := ⟨div⟩
instance [Field R] : Mod (CPolynomial.Raw R) := ⟨mod⟩

end Raw

/-- Quotient of `p` by a monic polynomial `q`. Matches Mathlib's `Polynomial.divByMonic`. -/
def divByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.divByMonic p.val q.val).trim, by simpa using Raw.Trim.trim_twice (Raw.divByMonic p.val q.val)⟩

/-- Remainder of `p` modulo a monic polynomial `q`. Matches Mathlib's `Polynomial.modByMonic`. -/
def modByMonic (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.modByMonic p.val q.val).trim, by simpa using Raw.Trim.trim_twice (Raw.modByMonic p.val q.val)⟩

/-- Quotient of `p` by `q` (when `R` is a field). -/
def div [Field R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.div p.val q.val).trim, by simpa using Raw.Trim.trim_twice (Raw.div p.val q.val)⟩

/-- Remainder of `p` modulo `q` (when `R` is a field). -/
def mod [Field R] (p q : CPolynomial R) : CPolynomial R :=
  ⟨(Raw.mod p.val q.val).trim, by simpa using Raw.Trim.trim_twice (Raw.mod p.val q.val)⟩

instance [Field R] : Div (CPolynomial R) := ⟨div⟩
instance [Field R] : Mod (CPolynomial R) := ⟨mod⟩

end Operations

section ImplementationCorrectness

/- Proofs that `CPolynomial.div` and `CPolynomial.mod` match their mathlib's counterparts.  -/

section DivModByMonic

namespace Raw

variable {R : Type*} [Ring R] [BEq R] [LawfulBEq R]

/-- Unfolds the first projection of `CPolynomial.Raw.divModByMonicAux` -/
lemma divModByMonicAux_go_unfold_1 (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (divModByMonicAux.go p q hq).1 =
    if q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size then
      C p.leadingCoeff * X ^ (p.natDegree - q.natDegree) +
      (divModByMonicAux.go (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))) q hq).1
    else 0 := by
  rw [ divModByMonicAux.go ]
  split_ifs <;> aesop

/-- Unfolds the second projection of `CPolynomial.Raw.divModByMonicAux` -/
lemma divModByMonicAux_go_unfold_2 (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (divModByMonicAux.go p q hq).2 =
    if q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size then
      (divModByMonicAux.go (p - q * (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree))) q hq).2
    else p := by
  rw [ divModByMonicAux.go ]
  split_ifs <;> aesop

/-- The termination condition for `CPolynomial.Raw.divModByMonicAux` matches the one in `Polynomial.divModByMonicAux -/
lemma size_cond_iff_degree_cond (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic) :
    (q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size) ↔
    (Polynomial.degree q.toPoly ≤ Polynomial.degree p.toPoly ∧ p.toPoly ≠ 0) := by
  by_cases hp : p.toPoly ≠ 0 <;> by_cases hq : q.toPoly ≠ 0 <;> simp_all [ trim_size_pos_iff_toPoly_ne_zero ]
  · constructor <;> intro h
    · rw [ Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq ] ; norm_cast ; linarith [ trim_size_eq_natDegree_succ p hp, trim_size_eq_natDegree_succ q hq ]
    · rw [ trim_size_eq_natDegree_succ q hq, trim_size_eq_natDegree_succ p hp ]
      exact Nat.succ_le_succ ( Polynomial.natDegree_le_natDegree h )
  · cases subsingleton_or_nontrivial R <;> simp_all [ eq_iff_true_of_subsingleton ]

/-- Rewrites `toPoly` lemmas on the definition of `z` in `divModByMonicAux.go`  -/
lemma z_toPoly_eq (p q : CPolynomial.Raw R) (hp : p.toPoly ≠ 0) :
    (C p.leadingCoeff * X ^ (p.natDegree - q.natDegree)).toPoly =
    Polynomial.C p.toPoly.leadingCoeff * Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree) := by
  have h_deg : p.natDegree = p.toPoly.natDegree ∧ q.natDegree = q.toPoly.natDegree := by
    constructor <;> by_cases hq : q.toPoly = 0 <;> simp_all [ natDegree_eq_toPoly_natDegree ]
    rw [ natDegree ]
    cases h : q.lastNonzero <;> simp_all [ toPoly ]
    have h_deg : q.toPoly = 0 := by
      convert hq using 1
    generalize_proofs at *
    have h_deg : q.trim.size = 0 := by
      exact (trim_size_zero_iff_toPoly_zero q).mpr hq
    generalize_proofs at *
    cases h' : q.trim ; simp_all [ trim ]
  convert toPoly_monom p.leadingCoeff ( p.natDegree - q.natDegree ) using 1
  rw [ h_deg.1, h_deg.2, leadingCoeff_toPoly ]

/-- The result of `divModByMonic` if the condition is not met -/
lemma divModByMonic_of_not_cond (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : ¬(q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size)) :
    p.toPoly /ₘ q.toPoly = 0 ∧ p.toPoly %ₘ q.toPoly = p.toPoly := by
  simp_all [ Polynomial.divByMonic, Polynomial.modByMonic ]
  rw [ Polynomial.divModByMonicAux ]
  have := size_cond_iff_degree_cond p q hq
  aesop

/-- The unfolding of `Polynomila.divByMonic` -/
lemma divByMonic_unfold_step (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size) :
    p.toPoly /ₘ q.toPoly =
    Polynomial.C p.toPoly.leadingCoeff * Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree) +
    (p.toPoly - q.toPoly * (Polynomial.C p.toPoly.leadingCoeff *
      Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree))) /ₘ q.toPoly := by
  have h_eq : ∀ (p q : Polynomial R), q.Monic → q ≠ 0 → p.degree ≥ q.degree → p /ₘ q = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree) + (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))) /ₘ q := by
    intros p q hq hq' hpq
    rw [ Polynomial.divByMonic ]
    unfold Polynomial.divModByMonicAux
    split_ifs <;> simp_all [ Polynomial.divByMonic ]
  by_cases hq_zero : q.toPoly = 0
  · cases subsingleton_or_nontrivial R <;> aesop_cat
  · have := size_cond_iff_degree_cond p q hq; aesop

/-- The unfolding of `Polynomila.modByMonic` -/
lemma modByMonic_unfold_step (p q : CPolynomial.Raw R) (hq : q.toPoly.Monic)
    (h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size) :
    p.toPoly %ₘ q.toPoly =
    (p.toPoly - q.toPoly * (Polynomial.C p.toPoly.leadingCoeff *
      Polynomial.X ^ (p.toPoly.natDegree - q.toPoly.natDegree))) %ₘ q.toPoly := by
  have h_eq : ∀ (p q : Polynomial R), q.Monic → q ≠ 0 → p.degree ≥ q.degree →
      p %ₘ q = (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))) %ₘ q := by
    intros p q hq hq' hpq
    rw [ Polynomial.modByMonic ]
    unfold Polynomial.divModByMonicAux
    split_ifs <;> simp_all [ Polynomial.modByMonic ]
  by_cases hq_zero : q.toPoly = 0
  · cases subsingleton_or_nontrivial R <;> aesop_cat
  · have := size_cond_iff_degree_cond p q hq
    aesop

/-- The first projection of `Raw.divModByMonicAux.go` matches `Polyomial.divByMonic` with respect to `toPoly`  -/
lemma divModByMonicAux_go_toPoly_1 (p q : CPolynomial.Raw R)
    (hq : q.monic = true) :
    (divModByMonicAux.go p q hq).1.toPoly = p.toPoly /ₘ q.toPoly := by
  induction' n : p.trim.size using Nat.strong_induction_on with n ih generalizing p q hq
  by_cases h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size
  · rw [ divModByMonicAux_go_unfold_1 ]
    rw [ if_pos h, divByMonic_unfold_step p q ((monic_iff_toPoly_monic q).mp hq) h ]
    rw [ toPoly_add ]
    rw [ ih _ _ _ _ hq rfl ]
    · rw [ z_toPoly_eq p q ]
      · rw [ toPoly_sub, toPoly_mul ]
        rw [ z_toPoly_eq p q ]
        have := trim_size_zero_iff_toPoly_zero p; aesop
      · have := trim_size_zero_iff_toPoly_zero p; aesop
    · exact n ▸ divByMonic_wf_termination p q hq h.1 h.2
  · have h_div_zero : p.toPoly /ₘ q.toPoly = 0 := by
      apply (divModByMonic_of_not_cond p q ((monic_iff_toPoly_monic q).mp hq) h).1
    unfold divModByMonicAux.go; aesop

/-- The second projection of `Raw.divModByMonicAux.go` matches `Polyomial.modByMonic` with respect to `toPoly`  -/
lemma divModByMonicAux_go_toPoly_2 (p q : CPolynomial.Raw R) (hq : q.monic = true)  :
    (divModByMonicAux.go p q hq).2.toPoly = p.toPoly %ₘ q.toPoly := by
  induction' n : p.trim.size using Nat.strong_induction_on with n ih generalizing p q hq
  by_cases h : q.trim.size ≤ p.trim.size ∧ 0 < p.trim.size
  · rw [ divModByMonicAux_go_unfold_2 ]
    rw [ if_pos h, modByMonic_unfold_step p q ((monic_iff_toPoly_monic q).mp hq) h ]
    rw [ ih _ _ _ _ hq rfl ]
    · rw [ toPoly_sub, toPoly_mul, z_toPoly_eq p q ]
      have := trim_size_zero_iff_toPoly_zero p; aesop
    · exact n ▸ divByMonic_wf_termination p q hq h.1 h.2
  · have h_div_zero : p.toPoly %ₘ q.toPoly = p.toPoly :=
      (divModByMonic_of_not_cond p q ((monic_iff_toPoly_monic q).mp hq) h).2
    unfold divModByMonicAux.go; aesop

/-- `Raw.divByMonic` matches `Polynomial.divByMonic` with respect to `toPoly` -/
theorem divByMonic_toPoly (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (divByMonic p q).toPoly = Polynomial.divByMonic p.toPoly q.toPoly := by
  unfold divByMonic divModByMonicAux
  rw [dif_pos hq]
  exact divModByMonicAux_go_toPoly_1 p q hq

/-- `Raw.modByMonic` matches `Polynomial.modByMonic` with respect to `toPoly` -/
theorem modByMonic_toPoly (p q : CPolynomial.Raw R) (hq : q.monic = true) :
    (modByMonic p q).toPoly = Polynomial.modByMonic p.toPoly q.toPoly := by
  unfold modByMonic divModByMonicAux
  rw [dif_pos hq]
  exact divModByMonicAux_go_toPoly_2 p q hq

end Raw

end DivModByMonic

section DivMod

variable {R : Type*}
variable [Field R] [BEq R] [LawfulBEq R]

namespace Raw

/-- Multiplication by a constant commutes with `Polynomial.divByMonic` -/
lemma Polynomial.C_mul_divByMonic_eq {R : Type*} [Field R] (a : R) (p q : R[X]) (hq : q.Monic) :
    (Polynomial.C a * p) /ₘ q = Polynomial.C a * (p /ₘ q) := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (Polynomial.div_modByMonic_unique _ _ hq ⟨by
      calc Polynomial.C a * (p %ₘ q) + q * (Polynomial.C a * (p /ₘ q))
          = Polynomial.C a * ((p %ₘ q) + q * (p /ₘ q)) := by ring
        _ = Polynomial.C a * p := by rw [Polynomial.modByMonic_add_div p hq],
      by rw [Polynomial.degree_C_mul ha]; exact Polynomial.degree_modByMonic_lt p hq⟩).1

/-- The zero polynomial is not monic -/
private lemma not_monic_of_toPoly_zero (q : CPolynomial.Raw R)
    (hq' : q.toPoly = 0) : ¬ (C q.leadingCoeff⁻¹ * q).monic = true := by
  intro h
  have := (monic_iff_toPoly_monic _).mp h
  rw [toPoly_mul, toPoly_C,
      leadingCoeff_toPoly, hq'] at this
  simp [Polynomial.Monic] at this

/-- If `q` is not the zero Raw polynomial, multiplying it by the inverse of its leading coefficient results in a monic polynomial -/
private lemma monic_raw_of_toPoly_ne_zero (q : CPolynomial.Raw R)
    (hq' : q.toPoly ≠ 0) : (C q.leadingCoeff⁻¹ * q).monic = true := by
  rw [monic_iff_toPoly_monic, toPoly_mul, toPoly_C, leadingCoeff_toPoly]
  have := Polynomial.monic_mul_leadingCoeff_inv hq'
  rwa [_root_.mul_comm] at this

omit [BEq R] [LawfulBEq R] in
/-- If `q` is not the zero Rpolynomial, multiplying it by the inverse of its leading coefficient results in a monic polynomial -/
private lemma monic_poly_of_toPoly_ne_zero (q : CPolynomial.Raw R)
    (hq' : q.toPoly ≠ 0) :
    (Polynomial.C q.toPoly.leadingCoeff⁻¹ * q.toPoly).Monic := by
  have := Polynomial.monic_mul_leadingCoeff_inv hq'
  rwa [_root_.mul_comm] at this

/-- `Raw.div` matches `Polynomial.div` with respect to `toPoly` -/
theorem div_toPoly (p q : CPolynomial.Raw R) :
    (div p q).toPoly = (Polynomial.div p.toPoly q.toPoly) := by
  unfold div
  by_cases hq' : q.toPoly = 0
  · unfold divByMonic divModByMonicAux
    simp [not_monic_of_toPoly_zero q hq']
    change (0 : CPolynomial.Raw R).toPoly = _
    rw [toPoly_zero]
    simp [Polynomial.div, hq']
  · rw [show C q.leadingCoeff⁻¹ • p = C q.leadingCoeff⁻¹ * p from rfl]
    rw [divByMonic_toPoly _ _ (monic_raw_of_toPoly_ne_zero q hq')]
    rw [toPoly_mul, toPoly_C, toPoly_mul, toPoly_C, leadingCoeff_toPoly]
    rw [Polynomial.C_mul_divByMonic_eq _ _ _ (monic_poly_of_toPoly_ne_zero q hq')]
    show Polynomial.C q.toPoly.leadingCoeff⁻¹ *
        (p.toPoly /ₘ (Polynomial.C q.toPoly.leadingCoeff⁻¹ * q.toPoly)) = _
    simp only [Polynomial.div]
    ring_nf

/-- `Raw.mod` matches `Polynomial.mod` with respect to `toPoly` -/
theorem mod_toPoly (p q : CPolynomial.Raw R) (hq : q.toPoly ≠ 0) :
    (mod p q).toPoly = (Polynomial.mod p.toPoly q.toPoly) := by
  unfold mod
  rw [modByMonic_toPoly _ _ (monic_raw_of_toPoly_ne_zero q hq)]
  rw [toPoly_mul, toPoly_C, leadingCoeff_toPoly]
  simp only [Polynomial.mod]
  ring_nf

end Raw

/-- `div` matches `Polynomial.div` with respect to `toPoly` -/
theorem div_toPoly (p q : CPolynomial R) :
    (div p q).toPoly = (Polynomial.div p.toPoly q.toPoly) := by
  show (Raw.div p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  exact Raw.div_toPoly p.val q.val

/-- `mod` matches `Polynomial.mod` with respect to `toPoly` -/
theorem mod_toPoly (p q : CPolynomial R) (hq : q ≠ 0) :
    (mod p q).toPoly = (Polynomial.mod p.toPoly q.toPoly) := by
  show (Raw.mod p.val q.val).trim.toPoly = _
  rw [Raw.toPoly_trim]
  have hq_val : q.val.toPoly ≠ 0 := by
    intro h
    apply hq
    apply CPolynomial.ext
    have hsize := (Raw.trim_size_zero_iff_toPoly_zero q.val).mpr h
    rw [q.property] at hsize
    exact Array.eq_empty_of_size_eq_zero hsize
  exact Raw.mod_toPoly p.val q.val hq_val

end DivMod

end ImplementationCorrectness
