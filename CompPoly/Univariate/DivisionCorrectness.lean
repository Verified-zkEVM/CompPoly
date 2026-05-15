/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.Ring
import CompPoly.Univariate.ToPoly.Impl

/-!
# Univariate Division Correctness

Correctness theorems for division-style univariate polynomial algorithms.
-/

namespace CompPoly
namespace CPolynomial

open Raw
open Polynomial

variable {R : Type*}

section Division

variable [Field R] [BEq R] [LawfulBEq R]

private def LowEq (k : Nat) (p q : R[X]) : Prop :=
  ∀ i, i < k → p.coeff i = q.coeff i

omit [BEq R] [LawfulBEq R] in
private lemma toPoly_truncate_coeff (k : Nat) (p : Raw R) (i : Nat) :
    (truncate k p).toPoly.coeff i = if i < k then p.toPoly.coeff i else 0 := by
  rw [Raw.coeff_toPoly, Raw.truncate_coeff, Raw.coeff_toPoly]

omit [BEq R] [LawfulBEq R] in
private lemma toPoly_reverse_coeff (n : Nat) (p : Raw R) (i : Nat) :
    (reverse n p).toPoly.coeff i =
      if i < n then p.toPoly.coeff (n - 1 - i) else 0 := by
  rw [Raw.coeff_toPoly, Raw.reverse_coeff, Raw.coeff_toPoly]

private lemma toPoly_mulLow_coeff (M : MulLowContext R) (k : Nat)
    (p q : Raw R) (i : Nat) :
    (M.mulLow k p q).toPoly.coeff i =
      if i < k then (p.toPoly * q.toPoly).coeff i else 0 := by
  rw [Raw.coeff_toPoly, Raw.mulLow_coeff]
  by_cases hi : i < k
  · simpa [hi, Raw.coeff_toPoly] using (Raw.toPoly_mul_coeff p q i)
  · simp [hi]

omit [BEq R] [LawfulBEq R] in
private lemma toPoly_truncate_lowEq (k : Nat) (p : Raw R) :
    LowEq k (truncate k p).toPoly p.toPoly := by
  intro i hi
  simp [toPoly_truncate_coeff, hi]

private lemma toPoly_mulLow_lowEq (M : MulLowContext R) (k : Nat)
    (p q : Raw R) :
    LowEq k (M.mulLow k p q).toPoly (p.toPoly * q.toPoly) := by
  intro i hi
  simp [toPoly_mulLow_coeff, hi]

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.refl (k : Nat) (p : R[X]) : LowEq k p p := by
  intro _ _
  rfl

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.symm {k : Nat} {p q : R[X]} (h : LowEq k p q) :
    LowEq k q p := by
  intro i hi
  exact (h i hi).symm

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.trans {k : Nat} {p q r : R[X]} (hpq : LowEq k p q)
    (hqr : LowEq k q r) : LowEq k p r := by
  intro i hi
  exact (hpq i hi).trans (hqr i hi)

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.of_le {k l : Nat} {p q : R[X]} (hle : k ≤ l)
    (h : LowEq l p q) : LowEq k p q := by
  intro i hi
  exact h i (lt_of_lt_of_le hi hle)

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.add {k : Nat} {p₁ p₂ q₁ q₂ : R[X]}
    (h₁ : LowEq k p₁ q₁) (h₂ : LowEq k p₂ q₂) :
    LowEq k (p₁ + p₂) (q₁ + q₂) := by
  intro i hi
  simp [h₁ i hi, h₂ i hi]

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.neg {k : Nat} {p q : R[X]} (h : LowEq k p q) :
    LowEq k (-p) (-q) := by
  intro i hi
  simp [h i hi]

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.sub {k : Nat} {p₁ p₂ q₁ q₂ : R[X]}
    (h₁ : LowEq k p₁ q₁) (h₂ : LowEq k p₂ q₂) :
    LowEq k (p₁ - p₂) (q₁ - q₂) := by
  exact h₁.add h₂.neg

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.mul_left {k : Nat} {p q : R[X]} (r : R[X])
    (h : LowEq k p q) : LowEq k (r * p) (r * q) := by
  intro i hi
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rcases x with ⟨a, b⟩
  have hab : a + b = i := Finset.mem_antidiagonal.mp hx
  have hb : b < k := by omega
  rw [h b hb]

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.mul_right {k : Nat} {p q : R[X]} (r : R[X])
    (h : LowEq k p q) : LowEq k (p * r) (q * r) := by
  intro i hi
  calc
    (p * r).coeff i = (r * p).coeff i := by rw [_root_.mul_comm p r]
    _ = (r * q).coeff i := LowEq.mul_left (k := k) (p := p) (q := q) r h i hi
    _ = (q * r).coeff i := by rw [_root_.mul_comm q r]

omit [BEq R] [LawfulBEq R] in
private lemma polynomial_C_two : Polynomial.C (2 : R) = (2 : R[X]) := by
  exact Polynomial.C_eq_natCast 2

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.eq_one_of_sub {k : Nat} {p : R[X]}
    (h : LowEq k (p - 1) 0) : LowEq k p 1 := by
  intro i hi
  exact sub_eq_zero.mp (by simpa [Polynomial.coeff_sub] using h i hi)

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.mul_self_zero {n : Nat} {p : R[X]}
    (h : LowEq n p 0) : LowEq (2 * n) (p * p) 0 := by
  intro i hi
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rcases x with ⟨a, b⟩
  have hab : a + b = i := Finset.mem_antidiagonal.mp hx
  have hsmall : a < n ∨ b < n := by omega
  rcases hsmall with ha | hb
  · rw [h a ha]
    simp
  · rw [h b hb]
    simp

omit [BEq R] [LawfulBEq R] in
private lemma LowEq.newton_step {n next : Nat} {p g fg correction g' : R[X]}
    (hnext : next ≤ 2 * n)
    (hfg : LowEq next fg (p * g))
    (hcorrection : LowEq next correction (Polynomial.C (2 : R) - fg))
    (hg' : LowEq next g' (g * correction))
    (h : LowEq n (p * g) 1) :
    LowEq next (p * g') 1 := by
  have hpg : LowEq next (p * g') (p * (g * correction)) :=
    LowEq.mul_left p hg'
  have hcorrection' : LowEq next correction (Polynomial.C (2 : R) - p * g) := by
    intro i hi
    have h1 := hcorrection i hi
    have h2 := hfg i hi
    simp [h1, h2]
  have hpgcorrection :
      LowEq next (p * (g * correction)) ((p * g) * (Polynomial.C (2 : R) - p * g)) := by
    intro i hi
    rw [← _root_.mul_assoc p g correction]
    exact LowEq.mul_left (p * g) hcorrection' i hi
  have hE : LowEq n (p * g - 1) 0 := by
    intro i hi
    have hcoeff := h i hi
    simp [Polynomial.coeff_sub, hcoeff]
  have hE2 : LowEq next ((p * g - 1) * (p * g - 1)) 0 := by
    exact (LowEq.mul_self_zero hE).of_le hnext
  have hmain : LowEq next (((p * g) * (Polynomial.C (2 : R) - p * g)) - 1) 0 := by
    have hpoly :
        ((p * g) * (Polynomial.C (2 : R) - p * g)) - 1 =
          -((p * g - 1) * (p * g - 1)) := by
      rw [polynomial_C_two (R := R)]
      ring
    rw [hpoly]
    simpa using hE2.neg
  exact hpg.trans (hpgcorrection.trans (LowEq.eq_one_of_sub hmain))

private lemma min_mul_two_pow_le_min_min_mul (k n fuel : Nat) :
    Nat.min k (n * 2 ^ (fuel + 1)) ≤
      Nat.min k (Nat.min k (2 * n) * 2 ^ fuel) := by
  by_cases h : 2 * n < k
  · have hmin : Nat.min k (2 * n) = 2 * n := Nat.min_eq_right (le_of_lt h)
    rw [hmin]
    have harith : n * 2 ^ (fuel + 1) = (2 * n) * 2 ^ fuel := by
      rw [_root_.pow_succ]
      ring
    rw [← harith]
  · have hmin : Nat.min k (2 * n) = k := Nat.min_eq_left (by omega)
    rw [hmin]
    have hp : 0 < 2 ^ fuel := Nat.pow_pos (a := 2) (by omega)
    have hle : k ≤ k * 2 ^ fuel := Nat.le_mul_of_pos_right (n := k) hp
    simp [Nat.min_eq_left hle]

omit [BEq R] [LawfulBEq R] in
private lemma inverseModX_base_lowEq (p : Raw R)
    (h0 : p.toPoly.coeff 0 ≠ 0) :
    LowEq 1 (p.toPoly * (Raw.C (p.coeff 0)⁻¹).toPoly) 1 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  rw [Raw.toPoly_C]
  rw [Polynomial.coeff_mul]
  simp [Raw.coeff_toPoly] at h0 ⊢
  exact mul_inv_cancel₀ h0

private lemma inverseModX_go_lowEq (M : MulLowContext R) (k : Nat) (p : Raw R) :
    ∀ fuel n g,
      LowEq n (p.toPoly * g.toPoly) 1 →
      LowEq (Nat.min k (n * 2 ^ fuel))
        (p.toPoly * (Raw.inverseModX.go M k p fuel n g).toPoly) 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro n g h
      unfold Raw.inverseModX.go
      have hg :
          LowEq (Nat.min k n) (truncate k g).toPoly g.toPoly :=
        (toPoly_truncate_lowEq k g).of_le (Nat.min_le_left k n)
      simpa using
        (LowEq.mul_left p.toPoly hg).trans (h.of_le (Nat.min_le_right k n))
  | succ fuel ih =>
      intro n g h
      unfold Raw.inverseModX.go
      by_cases hkn : k ≤ n
      · simp [hkn]
        have hg :
            LowEq k (truncate k g).toPoly g.toPoly :=
          toPoly_truncate_lowEq k g
        have hkg : LowEq k (p.toPoly * (truncate k g).toPoly) 1 :=
          (LowEq.mul_left p.toPoly hg).trans (h.of_le hkn)
        exact hkg.of_le (Nat.min_le_left k (n * 2 ^ (fuel + 1)))
      · simp [hkn]
        let next := Nat.min k (2 * n)
        let fg := M.mulLow next p g
        let correction := Raw.C (2 : R) - fg
        let g' := M.mulLow next g correction
        have hnext : next ≤ 2 * n := Nat.min_le_right k (2 * n)
        have hfg : LowEq next fg.toPoly (p.toPoly * g.toPoly) :=
          toPoly_mulLow_lowEq M next p g
        have hcorrection :
            LowEq next correction.toPoly (Polynomial.C (2 : R) - fg.toPoly) := by
          have hpoly : correction.toPoly = Polynomial.C (2 : R) - fg.toPoly := by
            change (Raw.C (2 : R) - fg).toPoly = Polynomial.C (2 : R) - fg.toPoly
            rw [Raw.toPoly_sub, Raw.toPoly_C]
          intro i hi
          rw [hpoly]
        have hg' :
            LowEq next g'.toPoly (g.toPoly * correction.toPoly) :=
          toPoly_mulLow_lowEq M next g correction
        have hstep : LowEq next (p.toPoly * g'.toPoly) 1 :=
          LowEq.newton_step hnext hfg hcorrection hg' h
        exact (ih next g' hstep).of_le
          (min_mul_two_pow_le_min_min_mul k n fuel)

private lemma inverseModX_lowEq (M : MulLowContext R) (k : Nat)
    (p : Raw R) (h0 : p.toPoly.coeff 0 ≠ 0) :
    LowEq k (p.toPoly * (inverseModX M k p).toPoly) 1 := by
  unfold inverseModX
  by_cases hk : k = 0
  · subst k
    intro i hi
    omega
  · simp [hk]
    have hbase := inverseModX_base_lowEq (R := R) p h0
    have hgo := inverseModX_go_lowEq M k p (k + 1) 1 (Raw.C (p.coeff 0)⁻¹) hbase
    have hkpow : k ≤ 2 ^ (k + 1) :=
      le_trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := k)))
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ k))
    have hmin : Nat.min k (2 ^ (k + 1)) = k := Nat.min_eq_left hkpow
    simpa [hmin] using hgo

omit [BEq R] [LawfulBEq R] in
private lemma toPoly_reverse_eq_reflect (n : Nat) (p : Raw R)
    (hdeg : p.toPoly.natDegree < n) :
    (reverse n p).toPoly = Polynomial.reflect (n - 1) p.toPoly := by
  ext i
  rw [toPoly_reverse_coeff, Polynomial.coeff_reflect]
  by_cases hi : i < n
  · have hle : i ≤ n - 1 := by omega
    simp [hi, Polynomial.revAt, hle]
  · have hle : ¬i ≤ n - 1 := by omega
    simp [hi, Polynomial.revAt, hle]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hdeg (Nat.le_of_not_lt hi))).symm

omit [BEq R] [LawfulBEq R] in
private lemma toPoly_reverse_natDegree_le (k : Nat) (p : Raw R) :
    (reverse k p).toPoly.natDegree ≤ k - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [toPoly_reverse_coeff]
  have hnot : ¬N < k := by omega
  simp [hnot]

private lemma toPoly_mulLow_natDegree_le (M : MulLowContext R) (k : Nat)
    (p q : Raw R) :
    (M.mulLow k p q).toPoly.natDegree ≤ k - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [toPoly_mulLow_coeff]
  have hnot : ¬N < k := by omega
  simp [hnot]

private lemma raw_toPoly_natDegree_lt_size_of_trim_eq (p : Raw R)
    (htrim : p.trim = p) (hpos : 0 < p.size) :
    p.toPoly.natDegree < p.size := by
  simpa [htrim] using Raw.toPoly_natDegree_lt_trim_size_of_pos (R := R) p (by
    simpa [htrim] using hpos)

omit [BEq R] [LawfulBEq R] in
private lemma toImpl_size_le_of_degree_lt (f : R[X]) (n : Nat)
    (hdeg : f.degree < (n : WithBot Nat)) : f.toImpl.size ≤ n := by
  rcases Raw.toImpl_elim f with ⟨_hzero, himpl⟩ | ⟨hnz, himpl⟩
  · simp [himpl]
  · have hdegree : f.degree = f.natDegree := Polynomial.degree_eq_natDegree hnz
    have hnat : f.natDegree < n := by
      rw [hdegree] at hdeg
      exact_mod_cast hdeg
    simp [himpl]
    omega

omit [LawfulBEq R] in
private lemma raw_coeff_last_eq_leadingCoeff_of_trim_eq (q : Raw R)
    (htrim : q.trim = q) (hpos : 0 < q.size) :
    q.coeff (q.size - 1) = q.leadingCoeff := by
  rw [Raw.leadingCoeff, htrim]
  simp [Raw.coeff, Array.getLastD, hpos]

private lemma div_step_degree_lt (p q : Raw R)
    (hptrim : p.trim = p) (hqtrim : q.trim = q)
    (hqmonic : q.leadingCoeff = 1) (hsize : ¬p.size < q.size) (hqpos : 0 < q.size) :
    ((p - Raw.C p.leadingCoeff * (q * Raw.X ^ (p.size - q.size))).trim).toPoly.degree <
      ((p.size - 1 : Nat) : WithBot Nat) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [Raw.toPoly_trim, Raw.coeff_toPoly, Raw.sub_coeff, Raw.coeff_C_mul_X_pow]
  have hppos : 0 < p.size := by omega
  have hplast : p.coeff (p.size - 1) = p.leadingCoeff :=
    raw_coeff_last_eq_leadingCoeff_of_trim_eq p hptrim hppos
  have hqlast : q.coeff (q.size - 1) = 1 := by
    rw [raw_coeff_last_eq_leadingCoeff_of_trim_eq q hqtrim hqpos, hqmonic]
  by_cases hm_top : m = p.size - 1
  · subst m
    have hcond :
        p.size - q.size ≤ p.size - 1 ∧
          p.size - 1 - (p.size - q.size) < q.size := by
      omega
    rw [if_pos hcond]
    have hidx : p.size - 1 - (p.size - q.size) = q.size - 1 := by omega
    rw [hplast, hidx, hqlast]
    simp
  · have hmp : p.size ≤ m := by omega
    have hpcoeff : p.coeff m = 0 := by simp [Raw.coeff, hmp]
    have hcond :
        ¬(p.size - q.size ≤ m ∧ m - (p.size - q.size) < q.size) := by
      omega
    rw [if_neg hcond, hpcoeff]
    simp

private lemma div_step_size_lt (p q : Raw R)
    (hptrim : p.trim = p) (hqtrim : q.trim = q)
    (hqmonic : q.leadingCoeff = 1) (hsize : ¬p.size < q.size) (hqpos : 0 < q.size) :
    ((p - Raw.C p.leadingCoeff * (q * Raw.X ^ (p.size - q.size))).trim).size < p.size := by
  let p' := (p - Raw.C p.leadingCoeff * (q * Raw.X ^ (p.size - q.size))).trim
  have hdeg : p'.toPoly.degree < ((p.size - 1 : Nat) : WithBot Nat) :=
    div_step_degree_lt p q hptrim hqtrim hqmonic hsize hqpos
  have hle : p'.toPoly.toImpl.size ≤ p.size - 1 :=
    toImpl_size_le_of_degree_lt p'.toPoly (p.size - 1) hdeg
  have hround := Raw.toImpl_toPoly (R := R) p'
  have htrim' : p'.trim = p' := by
    exact Trim.trim_twice _
  have hsize' : p'.size = p'.toPoly.toImpl.size := by
    rw [hround, htrim']
  have hppos : 0 < p.size := by omega
  change p'.size < p.size
  omega

omit [BEq R] [LawfulBEq R] in
private lemma raw_toPoly_degree_lt_of_size_lt (p q : Raw R)
    (hsize : p.size < q.size)
    (hqdegree : q.toPoly.degree = ((q.size - 1 : Nat) : WithBot Nat)) :
    p.toPoly.degree < q.toPoly.degree := by
  rw [hqdegree, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [Raw.coeff_toPoly]
  have hp : p.size ≤ m := by omega
  simp [Raw.coeff, hp]

private theorem raw_divModByMonicAux_go_spec (q : Raw R)
    (hqtrim : q.trim = q) (hqmonic : q.leadingCoeff = 1) (hqpos : 0 < q.size)
    (hqdegree : q.toPoly.degree = ((q.size - 1 : Nat) : WithBot Nat)) :
    ∀ fuel p,
      p.trim = p →
      p.size ≤ fuel →
      let qr := Raw.divModByMonicAux.go fuel p q
      qr.2.toPoly + q.toPoly * qr.1.toPoly = p.toPoly ∧
        qr.2.toPoly.degree < q.toPoly.degree := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hptrim hfuel
      have hpzero : p.size = 0 := by omega
      unfold Raw.divModByMonicAux.go
      constructor
      · rw [Raw.toPoly_zero]
        ring
      · exact raw_toPoly_degree_lt_of_size_lt p q (by omega) hqdegree
  | succ fuel ih =>
      intro p hptrim hfuel
      unfold Raw.divModByMonicAux.go
      by_cases hsize : p.size < q.size
      · simp only [hsize, ↓reduceIte]
        constructor
        · rw [Raw.toPoly_zero]
          ring
        · exact raw_toPoly_degree_lt_of_size_lt p q hsize hqdegree
      · simp [hsize]
        let step := (p - Raw.C p.leadingCoeff * (q * Raw.X ^ (p.size - q.size))).trim
        have hstep_size : step.size < p.size := by
          exact div_step_size_lt p q hptrim hqtrim hqmonic hsize hqpos
        have hstep_trim : step.trim = step := by
          exact Trim.trim_twice _
        have hstep_fuel : step.size ≤ fuel := by omega
        have ihstep := ih step hstep_trim hstep_fuel
        rcases ihstep with ⟨hrel, hdeg⟩
        constructor
        · change
            (Raw.divModByMonicAux.go fuel step q).2.toPoly +
                q.toPoly *
                  ((Raw.divModByMonicAux.go fuel step q).1 +
                    Raw.C p.leadingCoeff * Raw.X ^ (p.size - q.size)).toPoly =
              p.toPoly
          rw [Raw.toPoly_add, _root_.mul_add, ← _root_.add_assoc, hrel]
          dsimp only [step]
          rw [Raw.toPoly_trim, Raw.toPoly_sub, Raw.toPoly_mul, Raw.toPoly_C,
            Raw.toPoly_mul, Raw.toPoly_pow, Raw.toPoly_X]
          rw [Raw.toPoly_mul, Raw.toPoly_C, Raw.toPoly_pow, Raw.toPoly_X]
          ring
        · exact hdeg

private theorem raw_modByMonic_toPoly_eq_modByMonic (p q : CPolynomial R)
    (hmonic : (q.leadingCoeff == 1) = true) :
    ((p.val : Raw R).modByMonic q.val).toPoly = p.toPoly %ₘ q.toPoly := by
  have hqtrim : (q.val : Raw R).trim = q.val := Trim.trim_eq_of_isCanonical q.property
  have hqLC : q.leadingCoeff = 1 := by
    simpa using (LawfulBEq.eq_of_beq hmonic)
  have hqrawMonic : (q.val : Raw R).leadingCoeff = 1 := by
    simpa [Raw.leadingCoeff, CPolynomial.leadingCoeff, hqtrim] using hqLC
  have hqpos : 0 < (q.val : Raw R).size := by
    by_contra hpos
    have hsize : (q.val : Raw R).size = 0 := Nat.eq_zero_of_not_pos hpos
    have hzero : q.leadingCoeff = 0 := by
      simp [CPolynomial.leadingCoeff, Array.getLastD, hsize]
    have : (1 : R) = 0 := by simpa [hqLC] using hzero.symm
    exact one_ne_zero this
  have hqdegree : q.toPoly.degree = (((q.val : Raw R).size - 1 : Nat) : WithBot Nat) := by
    have hdeg := degree_toPoly q
    cases hs : (q.val : Raw R).size with
    | zero =>
        omega
    | succ n =>
        simp [CPolynomial.degree, hs] at hdeg ⊢
        exact hdeg.symm
  have hspec := raw_divModByMonicAux_go_spec (R := R) q.val hqtrim hqrawMonic hqpos
    hqdegree p.val.size p.val (Trim.trim_eq_of_isCanonical p.property) (Nat.le_refl p.val.size)
  rcases hspec with ⟨hrel, hdeg⟩
  have hqMonicPoly : q.toPoly.Monic := by
    rw [Polynomial.Monic.def, ← leadingCoeff_toPoly]
    exact hqLC
  have hunique :=
    Polynomial.div_modByMonic_unique
      ((Raw.divModByMonicAux p.val q.val).1.toPoly)
      ((Raw.divModByMonicAux p.val q.val).2.toPoly)
      hqMonicPoly ⟨hrel, hdeg⟩
  exact hunique.2.symm

private theorem reversal_remainder_toPoly_eq_modByMonic
    (M : Raw.MulLowContext R) (p q : CPolynomial R)
    (hmonic : (q.leadingCoeff == 1) = true)
    (hsize : ¬p.val.size < q.val.size) :
    (let k := p.val.size - q.val.size + 1
     let remainderLen := q.val.size - 1
     let revP := reverse p.val.size p.val
     let revQ := reverse q.val.size q.val
     let invRevQ := inverseModX M k revQ
     let quotientRev := M.mulLow k revP invRevQ
     let quotient := reverse k quotientRev
     let productLow := M.mulLow remainderLen q.val quotient
     truncate remainderLen p.val - productLow).toPoly = p.toPoly %ₘ q.toPoly := by
  let k := p.val.size - q.val.size + 1
  let n := q.val.size - 1
  let m := p.val.size - 1
  let revP := reverse p.val.size p.val
  let revQ := reverse q.val.size q.val
  let invRevQ := inverseModX M k revQ
  let quotientRev := M.mulLow k revP invRevQ
  let quotient := reverse k quotientRev
  let productLow := M.mulLow n q.val quotient
  let rem := truncate n p.val - productLow
  have hptrim : (p.val : Raw R).trim = p.val := Trim.trim_eq_of_isCanonical p.property
  have hqtrim : (q.val : Raw R).trim = q.val := Trim.trim_eq_of_isCanonical q.property
  have hqLC : q.leadingCoeff = 1 := by
    simpa using (LawfulBEq.eq_of_beq hmonic)
  have hqrawMonic : (q.val : Raw R).leadingCoeff = 1 := by
    simpa [Raw.leadingCoeff, CPolynomial.leadingCoeff, hqtrim] using hqLC
  have hqpos : 0 < (q.val : Raw R).size := by
    by_contra hpos
    have hsizeq : (q.val : Raw R).size = 0 := Nat.eq_zero_of_not_pos hpos
    have hzero : q.leadingCoeff = 0 := by
      simp [CPolynomial.leadingCoeff, Array.getLastD, hsizeq]
    have : (1 : R) = 0 := by simpa [hqLC] using hzero.symm
    exact one_ne_zero this
  have hppos : 0 < (p.val : Raw R).size := by omega
  have hkpos : 0 < k := by omega
  have hqMonicPoly : q.toPoly.Monic := by
    rw [Polynomial.Monic.def, ← leadingCoeff_toPoly]
    exact hqLC
  have hqdegree : q.toPoly.degree = ((n : Nat) : WithBot Nat) := by
    have hdeg := degree_toPoly q
    cases hs : (q.val : Raw R).size with
    | zero =>
        omega
    | succ d =>
        simp [CPolynomial.degree, n, hs] at hdeg ⊢
        exact hdeg.symm
  have hqnat : q.toPoly.natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_degree_le, hqdegree]
  have hpdeg_lt : (p.val : Raw R).toPoly.natDegree < p.val.size :=
    raw_toPoly_natDegree_lt_size_of_trim_eq p.val hptrim hppos
  have hqdeg_lt : (q.val : Raw R).toPoly.natDegree < q.val.size :=
    raw_toPoly_natDegree_lt_size_of_trim_eq q.val hqtrim hqpos
  have hrevP : revP.toPoly = Polynomial.reflect m p.toPoly := by
    simpa [revP, m, CPolynomial.toPoly] using
      toPoly_reverse_eq_reflect (R := R) p.val.size p.val hpdeg_lt
  have hrevQ : revQ.toPoly = Polynomial.reflect n q.toPoly := by
    simpa [revQ, n, CPolynomial.toPoly] using
      toPoly_reverse_eq_reflect (R := R) q.val.size q.val hqdeg_lt
  have hrevQ0 : revQ.toPoly.coeff 0 = 1 := by
    rw [hrevQ, Polynomial.coeff_reflect]
    have hle : 0 ≤ n := Nat.zero_le n
    simp [Polynomial.revAt, hle, n, raw_coeff_last_eq_leadingCoeff_of_trim_eq q.val hqtrim hqpos,
      hqrawMonic, CPolynomial.toPoly, Raw.coeff_toPoly]
  have hinv : LowEq k (revQ.toPoly * invRevQ.toPoly) 1 :=
    inverseModX_lowEq M k revQ (by simp [hrevQ0])
  have hquotRevLow :
      LowEq k quotientRev.toPoly (revP.toPoly * invRevQ.toPoly) := by
    simpa [quotientRev] using toPoly_mulLow_lowEq M k revP invRevQ
  have hrevProd : LowEq k (revQ.toPoly * quotientRev.toPoly) revP.toPoly := by
    have h₁ : LowEq k (revQ.toPoly * quotientRev.toPoly)
        (revQ.toPoly * (revP.toPoly * invRevQ.toPoly)) :=
      LowEq.mul_left revQ.toPoly hquotRevLow
    have h₂ : revQ.toPoly * (revP.toPoly * invRevQ.toPoly) =
        revP.toPoly * (revQ.toPoly * invRevQ.toPoly) := by ring
    have h₃ : LowEq k (revP.toPoly * (revQ.toPoly * invRevQ.toPoly)) revP.toPoly := by
      simpa using LowEq.mul_left revP.toPoly hinv
    exact h₁.trans ((by simpa [h₂] using h₃) : LowEq k
      (revQ.toPoly * (revP.toPoly * invRevQ.toPoly)) revP.toPoly)
  have hquotRevNat : quotientRev.toPoly.natDegree ≤ k - 1 := by
    simpa [quotientRev] using toPoly_mulLow_natDegree_le M k revP invRevQ
  have hquotRevDegLt : quotientRev.toPoly.natDegree < k := by omega
  have hquotReflect : quotient.toPoly = Polynomial.reflect (k - 1) quotientRev.toPoly := by
    simpa [quotient] using toPoly_reverse_eq_reflect (R := R) k quotientRev hquotRevDegLt
  have hquotRevReflect : quotientRev.toPoly = Polynomial.reflect (k - 1) quotient.toPoly := by
    rw [hquotReflect, Polynomial.reflect_reflect]
  have hquotNat : quotient.toPoly.natDegree ≤ k - 1 := by
    simpa [quotient] using toPoly_reverse_natDegree_le (R := R) k quotientRev
  have hm : m = n + (k - 1) := by omega
  have hreflectMul :
      Polynomial.reflect m (q.toPoly * quotient.toPoly) =
        revQ.toPoly * quotientRev.toPoly := by
    calc
      Polynomial.reflect m (q.toPoly * quotient.toPoly)
          = Polynomial.reflect (n + (k - 1)) (q.toPoly * quotient.toPoly) := by rw [hm]
      _ = Polynomial.reflect n q.toPoly * Polynomial.reflect (k - 1) quotient.toPoly := by
          rw [Polynomial.reflect_mul q.toPoly quotient.toPoly hqnat hquotNat]
      _ = revQ.toPoly * quotientRev.toPoly := by rw [← hrevQ, ← hquotRevReflect]
  have hreflectHigh : LowEq k
      (Polynomial.reflect m (q.toPoly * quotient.toPoly))
      (Polynomial.reflect m p.toPoly) := by
    rw [hreflectMul, ← hrevP]
    exact hrevProd
  have hprodNat : (q.toPoly * quotient.toPoly).natDegree ≤ m := by
    have hmul : (q.toPoly * quotient.toPoly).natDegree ≤
        q.toPoly.natDegree + quotient.toPoly.natDegree :=
      Polynomial.natDegree_mul_le
    have hsum : q.toPoly.natDegree + quotient.toPoly.natDegree ≤ n + (k - 1) :=
      Nat.add_le_add hqnat hquotNat
    omega
  have hpNat : p.toPoly.natDegree < p.val.size := hpdeg_lt
  have hremDegree : rem.toPoly.degree < q.toPoly.degree := by
    rw [hqdegree, Polynomial.degree_lt_iff_coeff_zero]
    intro i hi
    dsimp only [rem, productLow]
    rw [Raw.toPoly_sub, Polynomial.coeff_sub, toPoly_truncate_coeff, toPoly_mulLow_coeff]
    have hnotn : ¬i < n := by exact not_lt_of_ge hi
    simp [hnotn]
  have hrel : rem.toPoly + q.toPoly * quotient.toPoly = p.toPoly := by
    ext i
    by_cases hin : i < n
    · rw [Polynomial.coeff_add, Raw.toPoly_sub, Polynomial.coeff_sub,
        toPoly_truncate_coeff]
      dsimp only [productLow]
      rw [toPoly_mulLow_coeff]
      simp [hin, sub_eq_add_neg]
      rw [show (p.val : Raw R).toPoly = p.toPoly by rfl,
        show (q.val : Raw R).toPoly = q.toPoly by rfl]
      ring
    · have hni : n ≤ i := Nat.le_of_not_lt hin
      by_cases him : i ≤ m
      · let j := m - i
        have hjk : j < k := by omega
        have hjm : j ≤ m := by omega
        have hij : Polynomial.revAt m j = i := by
          simp [Polynomial.revAt, hjm, j]
          omega
        have hcoeff := hreflectHigh j hjk
        rw [Polynomial.coeff_reflect, Polynomial.coeff_reflect, hij] at hcoeff
        rw [Polynomial.coeff_add, Raw.toPoly_sub, Polynomial.coeff_sub,
          toPoly_truncate_coeff]
        dsimp only [productLow]
        rw [toPoly_mulLow_coeff]
        have hnotn : ¬i < n := not_lt_of_ge hni
        simp [hnotn, hcoeff]
      · have hmi : m < i := lt_of_not_ge him
        have hpzero : p.toPoly.coeff i = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hpNat (by omega))
        have hprodzero : (q.toPoly * quotient.toPoly).coeff i = 0 := by
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hprodNat hmi)
        rw [Polynomial.coeff_add, Raw.toPoly_sub, Polynomial.coeff_sub,
          toPoly_truncate_coeff]
        dsimp only [productLow]
        rw [toPoly_mulLow_coeff]
        have hnotn : ¬i < n := not_lt_of_ge hni
        simp [hnotn, hpzero, hprodzero]
  have hunique :=
    Polynomial.div_modByMonic_unique quotient.toPoly rem.toPoly hqMonicPoly ⟨hrel, hremDegree⟩
  dsimp only [rem, productLow, quotient, quotientRev, invRevQ, revQ, revP, n, k]
  exact hunique.2.symm

/-- The reversal monic remainder agrees with the canonical monic remainder. -/
theorem modByMonicByReversal_eq_modByMonic
    (M : Raw.MulLowContext R) (p q : CPolynomial R) :
    modByMonicByReversal M p q = modByMonic p q := by
  by_cases hmonic : q.leadingCoeff == 1
  · by_cases hsize : p.val.size < q.val.size
    · apply CPolynomial.ext
      have hptrim : (p.val : Raw R).trim = p.val := Trim.trim_eq_of_isCanonical p.property
      have hqtrim : (q.val : Raw R).trim = q.val := Trim.trim_eq_of_isCanonical q.property
      have hrawMonic : ((q.val : Raw R).leadingCoeff == 1) = true := by
        simpa [Raw.leadingCoeff, CPolynomial.leadingCoeff, hqtrim] using hmonic
      have hguard :
          ((p.val : Raw R).trim == p.val && (q.val : Raw R).trim == q.val &&
              (q.val : Raw R).leadingCoeff == 1) = true := by
        simp [hptrim, hqtrim, hrawMonic]
      unfold modByMonicByReversal CPolynomial.modByMonic
      change (Raw.modByMonicByReversal M (p.val : Raw R) q.val).trim =
        ((p.val : Raw R).modByMonic q.val).trim
      unfold Raw.modByMonicByReversal
      rw [if_pos hguard, if_pos hsize]
      cases hp : (p.val : Raw R).size with
      | zero =>
          unfold Raw.modByMonic Raw.divModByMonicAux
          rw [hp]
          simp [Raw.divModByMonicAux.go]
      | succ n =>
          unfold Raw.modByMonic Raw.divModByMonicAux
          rw [hp]
          simp [Raw.divModByMonicAux.go, hsize, hptrim]
    · apply CPolynomial.ext
      have hptrim : (p.val : Raw R).trim = p.val := Trim.trim_eq_of_isCanonical p.property
      have hqtrim : (q.val : Raw R).trim = q.val := Trim.trim_eq_of_isCanonical q.property
      have hrawMonic : ((q.val : Raw R).leadingCoeff == 1) = true := by
        simpa [Raw.leadingCoeff, CPolynomial.leadingCoeff, hqtrim] using hmonic
      have hguard :
          ((p.val : Raw R).trim == p.val && (q.val : Raw R).trim == q.val &&
              (q.val : Raw R).leadingCoeff == 1) = true := by
        simp [hptrim, hqtrim, hrawMonic]
      unfold modByMonicByReversal CPolynomial.modByMonic
      change (Raw.modByMonicByReversal M (p.val : Raw R) q.val).trim =
        ((p.val : Raw R).modByMonic q.val).trim
      unfold Raw.modByMonicByReversal
      rw [if_pos hguard, if_neg hsize]
      let rem : Raw R :=
        let k := p.val.size - q.val.size + 1
        let remainderLen := q.val.size - 1
        let revP := reverse p.val.size p.val
        let revQ := reverse q.val.size q.val
        let invRevQ := inverseModX M k revQ
        let quotientRev := M.mulLow k revP invRevQ
        let quotient := reverse k quotientRev
        let productLow := M.mulLow remainderLen q.val quotient
        truncate remainderLen p.val - productLow
      change rem.trim = ((p.val : Raw R).modByMonic q.val).trim
      rw [← Raw.toImpl_toPoly rem,
        ← Raw.toImpl_toPoly ((p.val : Raw R).modByMonic q.val)]
      congr 1
      have hremMath : rem.toPoly = p.toPoly %ₘ q.toPoly := by
        simpa [rem] using reversal_remainder_toPoly_eq_modByMonic M p q hmonic hsize
      have hrawMath :
          ((p.val : Raw R).modByMonic q.val).toPoly = p.toPoly %ₘ q.toPoly :=
        raw_modByMonic_toPoly_eq_modByMonic p q hmonic
      exact hremMath.trans hrawMath.symm
  · apply CPolynomial.ext
    have hptrim : (p.val : Raw R).trim = p.val := Trim.trim_eq_of_isCanonical p.property
    have hqtrim : (q.val : Raw R).trim = q.val := Trim.trim_eq_of_isCanonical q.property
    have hrawNotMonic : ¬(((q.val : Raw R).leadingCoeff == 1) = true) := by
      intro hraw
      apply hmonic
      simpa [Raw.leadingCoeff, CPolynomial.leadingCoeff, hqtrim] using hraw
    have hguard :
        ¬(((p.val : Raw R).trim == p.val && (q.val : Raw R).trim == q.val &&
            (q.val : Raw R).leadingCoeff == 1) = true) := by
      intro hguard
      have hraw : (((q.val : Raw R).leadingCoeff == 1) = true) := by
        simpa [hptrim, hqtrim] using hguard
      exact hrawNotMonic hraw
    unfold modByMonicByReversal
    change (Raw.modByMonicByReversal M (p.val : Raw R) q.val).trim =
      (CPolynomial.modByMonic p q).val
    unfold Raw.modByMonicByReversal
    rw [if_neg hguard]
    exact congrArg Subtype.val (modByMonicRemainderOnly_eq_modByMonic p q)

end Division

end CPolynomial
end CompPoly
