/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.Coset
public import CompPoly.Fields.Binary.AdditiveNTT.Correctness

/-!
# The coset transform agrees with the existing additive NTT

The coset file indexes the basis by natural numbers and evaluates at points.

The existing development works with polynomials over a finite field, and a basis indexed by `Fin r`.

This file shows the two presentations compute the same thing.

A natural-number basis `b` stands for `β` when it agrees with it below `r`.

## Main results

- `vanishing_eq_eval_W`: the point-indexed W_i is the evaluation of the polynomial W_i.
- `normalized_eq_eval_normalizedW`: the same for the normalised W^_i.
- `novel_eq_eval_Xⱼ`: the same for the novel basis polynomial X_j.
- `novelEval_eq_eval_polynomialFromNovelCoeffs`: the same for a polynomial in the novel basis.
- `independent_of_linearIndependent`: a linearly independent basis is independent.
- `additiveNTT_eq_ntt`: the existing transform is the coset transform with zero shift.
- `inetwork_additiveNTT`: the inverse network undoes the existing transform.
-/

@[expose] public section

open Polynomial Finset

namespace AdditiveNTT.Coset

variable {r : ℕ} [NeZero r] {L : Type} [Field L] [Fintype L] [DecidableEq L]
  {𝔽q : Type} [Field 𝔽q] [Fintype 𝔽q] [Fact (Fintype.card 𝔽q = 2)] [Algebra 𝔽q L]
  {β : Fin r → L} {b : ℕ → L}

/-! ## The polynomials -/

omit [NeZero r] [Fintype L] [DecidableEq L] in
/-- Point k below 2^i is the sum the existing code forms from the bits of k. -/
theorem point_eq_sum_getBit (hb : ∀ i : Fin r, b i = β i) (i : Fin r) (k : Fin (2 ^ i.val)) :
    point b k = ∑ j : Fin i, if Nat.getBit j k == 1 then β ⟨j, by omega⟩ else 0 := by
  rw [point_eq_sum b k.isLt, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  have h : b j = β ⟨j, by omega⟩ := hb ⟨j, by omega⟩
  rw [Nat.getBit_eq_testBit, h]
  cases (k : ℕ).testBit j <;> rfl

/-- The point-indexed W_i is the evaluation of the polynomial W_i. -/
theorem vanishing_eq_eval_W [Fact (LinearIndependent 𝔽q β)] (hb : ∀ i : Fin r, b i = β i)
    (i : Fin r) (x : L) : vanishing b i x = (W 𝔽q β i).eval x := by
  rw [← evalWAt_eq_W (ℓ := 0) (R_rate := 0) β i x, evalWAt, getUElements, List.map_map,
    List.prod_finRange_eq_finset_prod, vanishing, ← Fin.prod_univ_eq_prod_range]
  exact prod_congr rfl fun k _ => by rw [point_eq_sum_getBit hb]; rfl

/-- The point-indexed W^_i is the evaluation of the polynomial W^_i. -/
theorem normalized_eq_eval_normalizedW [Fact (LinearIndependent 𝔽q β)]
    (hb : ∀ i : Fin r, b i = β i) (i : Fin r) (x : L) :
    normalized b i x = (normalizedW 𝔽q β i).eval x := by
  rw [normalized, vanishing_eq_eval_W (𝔽q := 𝔽q) hb, hb, vanishing_eq_eval_W (𝔽q := 𝔽q) hb,
    normalizedW, eval_mul, eval_C, div_eq_mul_inv, one_div, mul_comm]

/-- The point-indexed X_j is the evaluation of the novel basis polynomial X_j. -/
theorem novel_eq_eval_Xⱼ [Fact (LinearIndependent 𝔽q β)] [Fact (Nat.Prime (ringChar 𝔽q))]
    (hb : ∀ i : Fin r, b i = β i) {ℓ : ℕ} (h_ℓ : ℓ ≤ r) (j : Fin (2 ^ ℓ)) (x : L) :
    novel b ℓ j x = (Xⱼ 𝔽q β ℓ h_ℓ j).eval x := by
  rw [novel, Xⱼ, eval_prod, ← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun i _ => ?_
  have h := normalized_eq_eval_normalizedW (𝔽q := 𝔽q) hb (Fin.castLE h_ℓ i) x
  rw [Fin.val_castLE] at h
  rw [eval_pow, ← h, Nat.getBit_eq_testBit]
  split_ifs <;> simp only [pow_one, pow_zero]

/-- A polynomial in the novel basis has the same value in both presentations. -/
theorem novelEval_eq_eval_polynomialFromNovelCoeffs [Fact (LinearIndependent 𝔽q β)]
    [Fact (Nat.Prime (ringChar 𝔽q))] (hb : ∀ i : Fin r, b i = β i) {ℓ : ℕ} (h_ℓ : ℓ ≤ r)
    (a : Fin (2 ^ ℓ) → L) (d : ℕ → L) (hd : ∀ k : Fin (2 ^ ℓ), d k = a k) (x : L) :
    novelEval b ℓ d x = (polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ a).eval x := by
  rw [novelEval, polynomialFromNovelCoeffs, eval_finsetSum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, novel_eq_eval_Xⱼ (𝔽q := 𝔽q) hb h_ℓ, hd, smul_eq_mul, mul_comm]

/-- A linearly independent basis is independent in the sense of the coset file. -/
theorem independent_of_linearIndependent [Fact (LinearIndependent 𝔽q β)]
    (hb : ∀ i : Fin r, b i = β i) : Independent b r := by
  intro i hi m hm h
  have h0 := vanishing_point b hm
  rw [h, vanishing_eq_eval_W (𝔽q := 𝔽q) hb ⟨i, hi⟩, show b i = β ⟨i, hi⟩ from hb ⟨i, hi⟩] at h0
  exact Wᵢ_eval_βᵢ_neq_zero 𝔽q β ⟨i, hi⟩ h0

/-! ## The transforms -/

omit [DecidableEq L] [Fintype 𝔽q] [Fact (Fintype.card 𝔽q = 2)] in
/-- With beta_0 = 1, the evaluation points of the existing transform are the points of S. -/
theorem evaluationPointω_eq_point [Fact (β 0 = 1)] {ℓ R_rate : ℕ} (hb : ∀ i : Fin r, b i = β i)
    (h : ℓ + R_rate < r) (j : Fin (2 ^ (ℓ + R_rate))) :
    evaluationPointω 𝔽q β h (i := ⟨0, by omega⟩) (h_i := Nat.zero_le ℓ) j = point b j := by
  have hW : ∀ y, (normalizedW 𝔽q β ⟨0, by omega⟩).eval y = y := fun y => by
    rw [show (⟨0, by omega⟩ : Fin r) = 0 from rfl, normalizedW₀_eq_1_div_β₀, eval_mul, eval_X,
      eval_C, Fact.out (p := β 0 = 1), div_one, mul_one]
  rw [point_eq_sum b j.isLt, ← Fin.sum_univ_eq_sum_range, evaluationPointω]
  refine sum_congr rfl fun ⟨k, hk⟩ _ => ?_
  have e : β ⟨0 + k, by omega⟩ = b k := by
    rw [hb ⟨k, by omega⟩]; exact congrArg β (Fin.ext (zero_add k))
  change (if k.getBit j = 1 then eval (β ⟨0 + k, by omega⟩) (normalizedW 𝔽q β ⟨0, by omega⟩)
    else 0) = _
  rw [hW, e, Nat.getBit_eq_testBit]
  cases (j : ℕ).testBit k <;> rfl

variable [Fact (LinearIndependent 𝔽q β)] [Fact (Nat.Prime (ringChar 𝔽q))]
  [Fact (β 0 = 1)] {ℓ R_rate : ℕ}

/-- The existing transform is the coset transform with zero shift.

The coefficients `d` extend `a` past 2^l in any way. -/
theorem additiveNTT_eq_ntt (hb : ∀ i : Fin r, b i = β i) (h : ℓ + R_rate < r)
    (a : Fin (2 ^ ℓ) → L) (d : ℕ → L) (hd : ∀ k : Fin (2 ^ ℓ), d k = a k)
    (j : Fin (2 ^ (ℓ + R_rate))) :
    additiveNTT 𝔽q β h a j = ntt b ℓ 0 d j := by
  rw [additiveNTT_correctness 𝔽q β h (by omega) a _ rfl j, ntt, zero_add,
    novelEval_eq_eval_polynomialFromNovelCoeffs (𝔽q := 𝔽q) hb (by omega) a d hd,
    evaluationPointω_eq_point hb]

/-- The inverse network undoes the existing transform.

It reads the first 2^l outputs and returns the coefficients. -/
theorem inetwork_additiveNTT (hb : ∀ i : Fin r, b i = β i) (h : ℓ + R_rate < r)
    (a : Fin (2 ^ ℓ) → L) (d : ℕ → L) (hd : ∀ k : Fin (2 ^ ℓ), d k = a k) (y : ℕ → L)
    (hy : ∀ j : Fin (2 ^ (ℓ + R_rate)), y j = additiveNTT 𝔽q β h a j) {i : ℕ}
    (hi : i < 2 ^ ℓ) : inetwork (twiddle b 0) ℓ y i = d i := by
  have : CharP 𝔽q 2 := charP_of_card_eq_prime Fact.out
  have : CharP L 2 := (Algebra.charP_iff 𝔽q L 2).mp inferInstance
  have hle : 2 ^ ℓ ≤ 2 ^ (ℓ + R_rate) := Nat.pow_le_pow_right two_pos (Nat.le_add_right ℓ R_rate)
  refine inetwork_ntt b (independent_of_linearIndependent (𝔽q := 𝔽q) hb) (by omega) 0 d y
    (fun j hj => ?_) hi
  rw [show j = (⟨j, by omega⟩ : Fin (2 ^ (ℓ + R_rate))).val from rfl, hy,
    additiveNTT_eq_ntt hb h a d hd]

end AdditiveNTT.Coset
