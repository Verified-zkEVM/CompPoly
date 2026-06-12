/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.OddBucket
import CompPoly.Univariate.Roots.LasVegas.Probability.Uniform
import Mathlib.FieldTheory.Finite.Basic

/-!
# Euler Bucket Counting for Odd Cantor-Zassenhaus Splitting

Finite-field counting facts about the deterministic Euler bucket classifier
`oddCZBucket`: the Euler criterion bridge, the bucket cardinalities
`1`, `(q - 1) / 2`, and `(q - 1) / 2`, and the resulting probability that two
independent uniform field values land in different buckets.

These theorems are field-theoretic, not algorithmic: they do not mention
`CPolynomial`, gcds, or the Las Vegas loop.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

private theorem two_le_q_of_card_eq {F : Type*} [Field F] [Fintype F]
    {q : Nat} (hcard : Fintype.card F = q) :
    2 ≤ q := by
  have hlt := Fintype.one_lt_card (α := F)
  omega

private theorem ringChar_ne_two_of_odd_card {F : Type*} [Field F] [Fintype F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    ringChar F ≠ 2 := by
  intro hchar
  have heven := FiniteField.even_card_iff_char_two.mp hchar
  rw [hcard] at heven
  omega

private theorem pow_half_eq_one_or_neg_one {F : Type*} [Field F] [Fintype F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q)
    {x : F} (hx : x ≠ 0) :
    x ^ ((q - 1) / 2) = 1 ∨ x ^ ((q - 1) / 2) = -1 := by
  have hq2 : 2 ≤ q := two_le_q_of_card_eq hcard
  have hferm : x ^ (q - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hcard] at h
  have hsq : x ^ ((q - 1) / 2) * x ^ ((q - 1) / 2) = 1 := by
    rw [← pow_add, show (q - 1) / 2 + (q - 1) / 2 = q - 1 by omega]
    exact hferm
  exact mul_self_eq_one_iff.mp hsq

/-- Euler criterion bridge: the square bucket consists of the nonzero squares. -/
theorem oddCZBucket_eq_square_iff_isSquare {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) (x : F) :
    oddCZBucket q x = OddCZBucket.square ↔ x ≠ 0 ∧ IsSquare x := by
  have hchar := ringChar_ne_two_of_odd_card hodd hcard
  have hexp : Fintype.card F / 2 = (q - 1) / 2 := by
    rw [hcard]
    omega
  rw [oddCZBucket_eq_square_iff]
  constructor
  · rintro ⟨hx0, hxm⟩
    refine ⟨hx0, (FiniteField.isSquare_iff hchar hx0).mpr ?_⟩
    rw [hexp]
    exact hxm
  · rintro ⟨hx0, hsq⟩
    refine ⟨hx0, ?_⟩
    have h := (FiniteField.isSquare_iff hchar hx0).mp hsq
    rwa [hexp] at h

/--
Euler criterion bridge: over an odd field of cardinality `q`, the residual
nonsquare bucket is exactly the locus `x ^ ((q - 1) / 2) = -1`.
-/
theorem oddCZBucket_eq_nonsquare_iff_pow_eq_neg_one {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) (x : F) :
    oddCZBucket q x = OddCZBucket.nonsquare ↔ x ^ ((q - 1) / 2) = -1 := by
  have hq2 : 2 ≤ q := two_le_q_of_card_eq hcard
  have hneg : (-1 : F) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (ringChar_ne_two_of_odd_card hodd hcard)
  rw [oddCZBucket_eq_nonsquare_iff]
  constructor
  · rintro ⟨hx0, hxm⟩
    rcases pow_half_eq_one_or_neg_one hodd hcard hx0 with hone | hnegone
    · exact absurd hone hxm
    · exact hnegone
  · intro hxm
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (by omega : (q - 1) / 2 ≠ 0)] at hxm
      exact neg_ne_zero.mpr one_ne_zero hxm.symm
    refine ⟨hx0, ?_⟩
    rw [hxm]
    exact hneg

/-- The zero Euler bucket has exactly one element. -/
theorem card_oddCZBucket_zero {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F] (q : Nat) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.zero).card = 1 := by
  have hfe : (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.zero) = {0} := by
    ext x
    simp [oddCZBucket_eq_zero_iff]
  rw [hfe, Finset.card_singleton]

private theorem card_oddCZBucket_square_add_nonsquare {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hcard : Fintype.card F = q) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.square).card +
      (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.nonsquare).card =
        q - 1 := by
  have hzero := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
    (fun x : F ↦ oddCZBucket q x = OddCZBucket.zero)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun x : F ↦ ¬ oddCZBucket q x = OddCZBucket.zero)
    (fun x : F ↦ oddCZBucket q x = OddCZBucket.square)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hsq : (Finset.univ.filter fun x : F ↦
      ¬ oddCZBucket q x = OddCZBucket.zero ∧ oddCZBucket q x = OddCZBucket.square) =
        Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.square := by
    apply Finset.filter_congr
    intro x _
    cases hbx : oddCZBucket q x <;> simp
  have hns : (Finset.univ.filter fun x : F ↦
      ¬ oddCZBucket q x = OddCZBucket.zero ∧ ¬ oddCZBucket q x = OddCZBucket.square) =
        Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.nonsquare := by
    apply Finset.filter_congr
    intro x _
    cases hbx : oddCZBucket q x <;> simp
  rw [hsq, hns] at hsplit
  have hcardz := card_oddCZBucket_zero (F := F) q
  have hcardu : (Finset.univ : Finset F).card = q := by
    rw [Finset.card_univ, hcard]
  omega

private theorem card_oddCZBucket_square_eq_nonsquare {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.square).card =
      (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.nonsquare).card := by
  have hchar := ringChar_ne_two_of_odd_card hodd hcard
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hchar
  obtain ⟨c, hcns⟩ := FiniteField.exists_nonsquare (F := F) hchar
  have hc0 : c ≠ 0 := by
    intro hzero
    exact hcns (by rw [hzero]; exact ⟨0, by simp⟩)
  have hcm : c ^ ((q - 1) / 2) = -1 := by
    rw [← oddCZBucket_eq_nonsquare_iff_pow_eq_neg_one hodd hcard]
    cases hbc : oddCZBucket q c with
    | zero => exact absurd ((oddCZBucket_eq_zero_iff q c).1 hbc) hc0
    | square =>
        exact absurd ((oddCZBucket_eq_square_iff_isSquare hodd hcard c).1 hbc).2 hcns
    | nonsquare => rfl
  refine Finset.card_bij' (fun x _ ↦ c * x) (fun y _ ↦ c⁻¹ * y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hx0, hxm⟩ := (oddCZBucket_eq_square_iff q x).1 hx.2
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [oddCZBucket_eq_nonsquare_iff]
    refine ⟨mul_ne_zero hc0 hx0, ?_⟩
    rw [mul_pow, hcm, hxm]
    simpa using hneg
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    obtain ⟨hy0, _⟩ := (oddCZBucket_eq_nonsquare_iff q y).1 hy.2
    have hym : y ^ ((q - 1) / 2) = -1 :=
      (oddCZBucket_eq_nonsquare_iff_pow_eq_neg_one hodd hcard y).1 hy.2
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [oddCZBucket_eq_square_iff]
    refine ⟨mul_ne_zero (inv_ne_zero hc0) hy0, ?_⟩
    rw [mul_pow, inv_pow, hcm, hym]
    exact inv_mul_cancel₀ (neg_ne_zero.mpr one_ne_zero)
  · intro x _
    show c⁻¹ * (c * x) = x
    rw [← _root_.mul_assoc, inv_mul_cancel₀ hc0, _root_.one_mul]
  · intro y _
    show c * (c⁻¹ * y) = y
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hc0, _root_.one_mul]

/-- The square Euler bucket of an odd field of cardinality `q` has `(q - 1) / 2` elements. -/
theorem card_oddCZBucket_square {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.square).card =
      (q - 1) / 2 := by
  have hadd := card_oddCZBucket_square_add_nonsquare (F := F) hcard
  have heq := card_oddCZBucket_square_eq_nonsquare hodd hcard
  have hq2 := two_le_q_of_card_eq hcard
  omega

/-- The nonsquare Euler bucket of an odd field of cardinality `q` has `(q - 1) / 2` elements. -/
theorem card_oddCZBucket_nonsquare {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.nonsquare).card =
      (q - 1) / 2 := by
  have hadd := card_oddCZBucket_square_add_nonsquare (F := F) hcard
  have heq := card_oddCZBucket_square_eq_nonsquare hodd hcard
  have hq2 := two_le_q_of_card_eq hcard
  omega

/--
Two independent uniform field values land in different Euler buckets with
probability at least `1 / 2`.

Every Euler bucket has at most `(q - 1) / 2` elements, so for each first value
at least `q - (q - 1) / 2 = (q + 1) / 2` choices of the second value land in a
different bucket, giving separation probability at least `(q + 1) / (2 * q)`.
-/
theorem oddCZBucket_pair_separated_probability_ge_half {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (2 : ℝ≥0∞)⁻¹ ≤
      eventProbability
        ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind
          fun x ↦ (uniformFieldElementPMF enumeration.toFieldEnumeration).map
            fun y ↦ (x, y))
        {xy | oddCZBucket q xy.1 ≠ oddCZBucket q xy.2} := by
  have hq2 : 2 ≤ q := two_le_q_of_card_eq hcard
  apply uniformPair_separated_probability_ge_half_of_fiber_card_le enumeration
    (fun x ↦ oddCZBucket q x) hcard (m := (q - 1) / 2)
  · intro x
    refine ⟨Finset.univ.filter fun y : F ↦ oddCZBucket q y = oddCZBucket q x,
      fun y hy ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩, ?_⟩
    cases hbx : oddCZBucket q x with
    | zero =>
        have hfe := card_oddCZBucket_zero (F := F) q
        omega
    | square =>
        rw [card_oddCZBucket_square hodd hcard]
    | nonsquare =>
        rw [card_oddCZBucket_nonsquare hodd hcard]
  · omega

end FiniteField

end Roots

end CPolynomial

end CompPoly
