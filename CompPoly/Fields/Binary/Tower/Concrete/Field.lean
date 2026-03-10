/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import CompPoly.Fields.Binary.Tower.Concrete.Core

namespace ConcreteBinaryTower

open Polynomial

/-! Lemmas of field properties at level k that depends on field properties at level (k-1) -/
section BTFieldPropsOneLevelLiftingLemmas
variable {k : ℕ} {h_k : k > 0}

theorem concrete_mul_eq
    (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a b : ConcreteBTField k) {a₁ a₀ b₁ b₀ : ConcreteBTField (k - 1)}
  (h_a : (a₁, a₀) = split h_k a) (h_b : (b₁, b₀) = split h_k b) :
  concrete_mul a b =
    《 concrete_mul a₀ b₁ + concrete_mul b₀ a₁ + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1)),
      concrete_mul a₀ b₀ + concrete_mul a₁ b₁ 》 := by
  letI : Field (ConcreteBTField (k - 1)) := mkFieldInstance prevBTFieldProps
  have h_a₁ : (split h_k a).1 = a₁ := by rw [h_a.symm]
  have h_a₀ : (split h_k a).2 = a₀ := by rw [h_a.symm]
  have h_b₁ : (split h_k b).1 = b₁ := by rw [h_b.symm]
  have h_b₀ : (split h_k b).2 = b₀ := by rw [h_b.symm]
  conv =>
    lhs
    unfold concrete_mul
    rw [dif_neg (Nat.ne_of_gt h_k)]
    simp only [h_a₁, h_a₀, h_b₁, h_b₀] -- Do this to resolve the two nested matches (of the splits)
    -- while still allowing substitution of a₀ a₁ b₀ b₁ (components of the splits) into the goal
  rw [join_eq_join_iff]
  split_ands
  · change (a₁ + a₀) * (b₁ + b₀) + (a₀ * b₀ + a₁ * b₁) + a₁ * b₁ * Z (k - 1) =
      a₀ * b₁ + b₀ * a₁ + a₁ * b₁ * Z (k - 1)
    have h_add_left_inj := (add_left_inj (a:=(a₁ * b₁) * (Z (k - 1)))
      (b:=(a₁ + a₀) * (b₁ + b₀) + (a₀ * b₀ + a₁ * b₁) + (a₁ * b₁) * (Z (k - 1)))
      (c:= a₀ * b₁ + b₀ * a₁ + (a₁ * b₁) * (Z (k - 1)))).mp
    rw [h_add_left_inj]
    rw [add_assoc, add_self_cancel, add_zero, add_assoc, add_self_cancel, add_zero]
    -- ⊢ (a₁ + a₀) * (b₁ + b₀) + (a₀ * b₀ + a₁ * b₁) = a₀ * b₁ + b₀ * a₁
    rw [left_distrib, right_distrib, right_distrib]
    rw [mul_comm (a:=a₁) (b:=b₀), mul_comm (a:=a₀) (b:=b₁)]
    conv =>
      lhs
      rw [←add_assoc, ←add_assoc]
      rw [add_assoc (b:=a₀ * b₀) (c:=a₀ * b₀), add_self_cancel, add_zero]
      rw [add_comm (b:=a₁ * b₁), ←add_assoc, ←add_assoc, add_self_cancel, zero_add]
  · rfl

lemma concrete_zero_mul
    (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a : ConcreteBTField k) : concrete_mul (zero (k:=k)) a = zero (k:=k) := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case : k = 0
    simp only [h_k_zero, ↓reduceDIte, zero, ite_true]
  · -- Inductive case : k > 0
    simp only [dif_neg h_k_zero]
    -- Obtain h_k_gt_0 from h_k_zero
    have h_k_gt_0_proof : k > 0 := by omega
    -- Split zero into (zero, zero)
    have h_zero_split : split h_k_gt_0_proof (zero (k:=k)) = (zero, zero) := by rw [split_zero]
    let (a₁, a₀) := (zero (k:=k - 1), zero (k:=k - 1))
    let (b₁, b₀) := split h_k_gt_0_proof a
    rw [h_zero_split]
    simp only
    -- Apply the inductive hypothesis to a₁ * b₁, a₀ * b₀, a₁ * b₀, a₀ * b₁
    simp only [zero_is_0, zero_add, prevBTFieldProps.zero_mul']
    simp only [← zero_is_0, join_zero_zero h_k_gt_0_proof]

lemma concrete_mul_zero
    (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a : ConcreteBTField k) : concrete_mul a (zero (k:=k)) = zero (k:=k) := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case : k = 0
    simp only [h_k_zero, ↓reduceDIte, zero, BitVec.zero_eq, ↓reduceIte, ite_self]
  · -- Inductive case : k > 0
    simp only [dif_neg h_k_zero]
    -- Obtain h_k_gt_0 from h_k_zero
    have h_k_gt_0_proof : k > 0 := by omega
    -- Split zero into (zero, zero)
    have h_zero_split : split h_k_gt_0_proof (zero (k:=k)) = (zero, zero) := by rw [split_zero]
    -- Split a into (a₁, a₀)
    let (a₁, a₀) := split h_k_gt_0_proof a
    let (b₁, b₀) := (zero (k:=k - 1), zero (k:=k - 1))
    -- Rewrite with the zero split
    rw [h_zero_split]
    simp only
    -- Apply the inductive hypothesis
    simp only [zero_is_0, zero_add, prevBTFieldProps.mul_zero']
    -- Use join_zero to complete the proof
    simp only [← zero_is_0, prevBTFieldProps.zero_mul, join_zero_zero h_k_gt_0_proof]

lemma concrete_one_mul
    (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a : ConcreteBTField k) : concrete_mul (one (k:=k)) a = a := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case : k = 0
    simp [h_k_zero, ↓reduceDIte, one_is_1, zero_is_0]; intro h; exact h.symm
  · -- Inductive case : k > 0
    have h_k_gt_0 : k > 0 := by omega
    simp only [dif_neg h_k_zero]
    let p := split h_k_gt_0 a
    let a₁ := p.fst
    let a₀ := p.snd
    have h_split_a : split h_k_gt_0 a = (a₁, a₀) := by rfl
    rw [split_one]
    simp only [zero_is_0, zero_add, prevBTFieldProps.one_mul, prevBTFieldProps.zero_mul', add_zero]
    simp [add_assoc, add_self_cancel]
    have join_result : 《 a₁, a₀ 》 = a := by
      have split_join := join_of_split h_k_gt_0 a a₁ a₀
      exact (split_join h_split_a).symm
    exact join_result

lemma concrete_mul_one
    (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a : ConcreteBTField k) : concrete_mul a (one (k:=k)) = a := by
  unfold concrete_mul
  by_cases h_k_zero : k = 0
  · -- Base case : k = 0
    simp [h_k_zero, ↓reduceDIte, one_is_1, zero_is_0];
    conv =>
      lhs
      simp only [if_self_rfl]
  · -- Inductive case : k > 0
    have h_k_gt_0 : k > 0 := by omega
    simp only [dif_neg h_k_zero]
    let p := split h_k_gt_0 a
    let a₁ := p.fst
    let a₀ := p.snd
    have h_split_a : split h_k_gt_0 a = (a₁, a₀) := by rfl
    rw [split_one]
    simp only [zero_is_0, zero_add, prevBTFieldProps.mul_one, prevBTFieldProps.mul_zero',
      prevBTFieldProps.zero_mul', add_zero]
    simp [add_assoc, add_self_cancel]
    have join_result : 《 a₁, a₀ 》 = a := by
      have split_join := join_of_split h_k_gt_0 a a₁ a₀
      exact (split_join h_split_a).symm
    exact join_result

lemma concrete_pow_base_one
    (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1)) (n : ℕ) :
  concrete_pow_nat (k:=k) (x:=1) n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- ih : ∀ m, m < n → concrete_pow_nat (k:=k) (x:=1) m = 1
    unfold concrete_pow_nat
    by_cases h_n_zero : n = 0
    · -- Base case : n = 0
      rw [if_pos h_n_zero]
      exact one_is_1  -- one = 1
    · -- Inductive step : n ≠ 0
      rw [if_neg h_n_zero]
      by_cases h_mod : n % 2 = 0
      · -- Even case : n % 2 = 0
        rw [if_pos h_mod]
        have h_square : concrete_mul (1 : ConcreteBTField k) 1 = 1 := by
          rw [← one_is_1]
          rw [concrete_one_mul prevBTFieldProps]  -- Assume concrete_mul 1 1 = 1
        rw [h_square]
        have h_div_lt : n / 2 < n := by
          apply Nat.div_lt_self
          simp [Nat.ne_zero_iff_zero_lt.mp h_n_zero]
          exact Nat.le_refl 2
        apply ih (n / 2) h_div_lt  -- Use ih for n / 2 < n
      · -- Odd case : n % 2 ≠ 0
        rw [if_neg h_mod]
        have h_square : concrete_mul (1 : ConcreteBTField k) 1 = 1 := by
          rw [← one_is_1]
          rw [concrete_one_mul prevBTFieldProps]  -- Assume concrete_mul 1 1 = 1
        rw [h_square]
        have h_div_lt : n / 2 < n := by
          apply Nat.div_lt_self
          simp [Nat.ne_zero_iff_zero_lt.mp h_n_zero]
          exact Nat.le_refl 2
        rw [ih (n / 2) h_div_lt]  -- Use ih for n / 2 < n
        rw [← one_is_1]
        rw [concrete_one_mul prevBTFieldProps]  -- Assume concrete_mul 1 1 = 1

lemma concrete_mul_comm
    {h_k : k > 0} (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a b : ConcreteBTField k) :
  concrete_mul a b = concrete_mul b a := by
  letI : Field (ConcreteBTField (k - 1)) := mkFieldInstance prevBTFieldProps
  by_cases h_k_zero : k = 0
  · linarith
  · -- Inductive case : k > 0
    -- Approach : utilize concrete_mul_eq of level (k - 1)
    let p1 := split h_k a
    let p2 := split h_k b
    let a₁ := p1.fst
    let a₀ := p1.snd
    let b₁ := p2.fst
    let b₀ := p2.snd
    have h_split_a : split h_k a = (a₁, a₀) := by rfl
    have h_split_b : split h_k b = (b₁, b₀) := by rfl
    have h_a₁_a₀ : a = 《 a₁, a₀ 》 := by exact (join_of_split h_k a a₁ a₀) h_split_a
    have h_b₁_b₀ : b = 《 b₁, b₀ 》 := by exact (join_of_split h_k b b₁ b₀) h_split_b
    have h_a₁ : (split h_k a).1 = a₁ := by rw [h_split_a]
    have h_a₀ : (split h_k a).2 = a₀ := by rw [h_split_a]
    have h_b₁ : (split h_k b).1 = b₁ := by rw [h_split_b]
    have h_b₀ : (split h_k b).2 = b₀ := by rw [h_split_b]
    have h_lhs := concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=a) (b:=b) (a₁:=a₁)
      (a₀:=a₀) (b₁:=b₁) (b₀:=b₀) (h_a:=h_split_a) (h_b:=h_split_b)
    have h_rhs := concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=b) (b:=a) (a₁:=b₁)
      (a₀:=b₀) (b₁:=a₁) (b₀:=a₀) (h_a:=h_split_b) (h_b:=h_split_a)
    rw [h_lhs, h_rhs]
    change join h_k (a₀ * b₁ + b₀ * a₁ + (a₁ * b₁) * (Z (k - 1)))
        (a₀ * b₀ + a₁ * b₁) =
      join h_k (b₀ * a₁ + a₀ * b₁ + (b₁ * a₁) * (Z (k - 1)))
        (b₀ * a₀ + b₁ * a₁)
    rw [join_eq_join_iff (h_pos := h_k)]
    rw [mul_comm (a:=b₀) (b:=a₀), mul_comm (a:=a₁) (b:=b₁)]
    rw [add_comm (a:= a₀ * b₁) (b:= b₀ * a₁)]
    simp only [and_self]

lemma concrete_mul_assoc
    {h_k : k > 0} (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a b c : ConcreteBTField k) :
  concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c) := by
  letI : Field (ConcreteBTField (k - 1)) := mkFieldInstance prevBTFieldProps
  have hmul : ∀ (a b : ConcreteBTField (k - 1)), concrete_mul a b = a * b := fun a b => rfl
  by_cases h_k_zero : k = 0
  · linarith
  · -- Inductive case : k > 0
    -- Approach : utilize concrete_mul_eq of level (k - 1)
    -- ⊢ concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
    let p1 := split h_k a
    let p2 := split h_k b
    let p3 := split h_k c
    let a₁ := p1.fst
    let a₀ := p1.snd
    let b₁ := p2.fst
    let b₀ := p2.snd
    let c₁ := p3.fst
    let c₀ := p3.snd
    have h_split_a : split h_k a = (a₁, a₀) := by rfl
    have h_split_b : split h_k b = (b₁, b₀) := by rfl
    have h_split_c : split h_k c = (c₁, c₀) := by rfl
    have h_a₁_a₀ : a = 《 a₁, a₀ 》 := by exact (join_of_split h_k a a₁ a₀) h_split_a
    have h_b₁_b₀ : b = 《 b₁, b₀ 》 := by exact (join_of_split h_k b b₁ b₀) h_split_b
    have h_c₁_c₀ : c = 《 c₁, c₀ 》 := by exact (join_of_split h_k c c₁ c₀) h_split_c
    -- ⊢ concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
    have a_mul_b_eq := concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=a) (b:=b) (a₁:=a₁)
      (a₀:=a₀) (b₁:=b₁) (b₀:=b₀) (h_a:=h_split_a) (h_b:=h_split_b)
    have b_mul_c_eq := concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=b) (b:=c) (a₁:=b₁)
      (a₀:=b₀) (b₁:=c₁) (b₀:=c₀) (h_a:=h_split_b) (h_b:=h_split_c)
    set ab₁ := concrete_mul a₀ b₁ + concrete_mul b₀ a₁
 + concrete_mul (concrete_mul a₁ b₁) (Z (k - 1))
    set ab₀ := concrete_mul a₀ b₀ + concrete_mul a₁ b₁
    have h_split_a_mul_b : split h_k (concrete_mul a b) = (ab₁, ab₀) := by
      exact (split_of_join h_k (concrete_mul a b) ab₁ ab₀ a_mul_b_eq).symm
    set bc₁ := concrete_mul b₀ c₁ + concrete_mul c₀ b₁
 + concrete_mul (concrete_mul b₁ c₁) (Z (k - 1))
    set bc₀ := concrete_mul b₀ c₀ + concrete_mul b₁ c₁
    have h_split_b_mul_c : split h_k (concrete_mul b c) = (bc₁, bc₀) := by
      exact (split_of_join h_k (concrete_mul b c) bc₁ bc₀ b_mul_c_eq).symm

    set ab := concrete_mul a b
    set bc := concrete_mul b c
    -- rw [a_mul_b_eq, b_mul_c_eq]
    -- ⊢ concrete_mul ab c = concrete_mul a bc
    have a_mul_bc_eq := concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=a) (b:=bc) (a₁:=a₁)
      (a₀:=a₀) (b₁:=bc₁) (b₀:=bc₀) (h_a:=h_split_a) (h_b:=h_split_b_mul_c.symm)
    have ab_mul_c_eq := concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=ab) (b:=c) (a₁:=ab₁)
      (a₀:=ab₀) (b₁:=c₁) (b₀:=c₀) (h_a:=h_split_a_mul_b.symm) (h_b:=h_split_c)
    set a_bc₁ := concrete_mul a₀ bc₁ + concrete_mul bc₀ a₁
 + concrete_mul (concrete_mul a₁ bc₁) (Z (k - 1))
    set a_bc₀ := concrete_mul a₀ bc₀ + concrete_mul a₁ bc₁
    have h_split_a_bc : split h_k (concrete_mul a bc) = (a_bc₁, a_bc₀) := by
      exact (split_of_join h_k (concrete_mul a bc) a_bc₁ a_bc₀ a_mul_bc_eq).symm
    set ab_c₁ := concrete_mul ab₀ c₁ + concrete_mul c₀ ab₁
 + concrete_mul (concrete_mul ab₁ c₁) (Z (k - 1))
    set ab_c₀ := concrete_mul ab₀ c₀ + concrete_mul ab₁ c₁
    have h_split_ab_c : split h_k (concrete_mul ab c) = (ab_c₁, ab_c₀) := by
      exact (split_of_join h_k (concrete_mul ab c) ab_c₁ ab_c₀ ab_mul_c_eq).symm

    rw [a_mul_bc_eq, ab_mul_c_eq] -- convert concrete mul to join
    rw [join_eq_join_iff]
    -- ⊢ ab_c₁ = a_bc₁ ∧ ab_c₀ = a_bc₀
    unfold a_bc₁ ab_c₁ ab_c₀ a_bc₀ ab₀ ab₁ bc₀ bc₁ -- unfold all
    simp_rw [hmul]
    ring_nf
    simp only [and_self]

lemma concrete_mul_left_distrib
    {h_k : k > 0} (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a b c : ConcreteBTField k) :
    concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c := by
  letI : Field (ConcreteBTField (k - 1)) := mkFieldInstance prevBTFieldProps
  have hmul : ∀ (a b : ConcreteBTField (k - 1)), concrete_mul a b = a * b := fun a b => rfl
  by_cases h_k_zero : k = 0
  · linarith
  · -- Inductive case : k > 0
    -- Approach : utilize concrete_mul_eq of level (k - 1)
    -- ⊢ concrete_mul (concrete_mul a b) c = concrete_mul a (concrete_mul b c)
    let p1 := split h_k a
    let p2 := split h_k b
    let p3 := split h_k c
    let a₁ := p1.fst
    let a₀ := p1.snd
    let b₁ := p2.fst
    let b₀ := p2.snd
    let c₁ := p3.fst
    let c₀ := p3.snd
    have h_split_a : split h_k a = (a₁, a₀) := by rfl
    have h_split_b : split h_k b = (b₁, b₀) := by rfl
    have h_split_c : split h_k c = (c₁, c₀) := by rfl
    have h_a₁_a₀ : a = 《 a₁, a₀ 》 := by exact (join_of_split h_k a a₁ a₀) h_split_a
    have h_b₁_b₀ : b = 《 b₁, b₀ 》 := by exact (join_of_split h_k b b₁ b₀) h_split_b
    have h_c₁_c₀ : c = 《 c₁, c₀ 》 := by exact (join_of_split h_k c c₁ c₀) h_split_c
    have h_split_b_add_c : split h_k (b + c) = (b₁ + c₁, b₀ + c₀) := by
      exact split_sum_eq_sum_split h_k (x₀:=b) (x₁:=c) (hi₀:=b₁) (lo₀:=b₀)
        (hi₁:=c₁) (lo₁:=c₀) (h_split_x₀:=h_split_b) (h_split_x₁:=h_split_c)
    -- ⊢ concrete_mul a (b + c) = concrete_mul a b + concrete_mul a c
    conv =>
      lhs
      -- rewrite a * (b + c)
      rw [concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=a) (b:=b + c) (a₁:=a₁)
        (a₀:=a₀) (b₁:=b₁ + c₁) (b₀:=b₀ + c₀) (h_a:=h_split_a) (h_b:=h_split_b_add_c.symm)]
    conv =>
      rhs
      rw [concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=a) (b:=b) (a₁:=a₁)
        (a₀:=a₀) (b₁:=b₁) (b₀:=b₀) (h_a:=h_split_a) (h_b:=h_split_b)]
      rw [concrete_mul_eq prevBTFieldProps (h_k:=h_k) (a:=a) (b:=c) (a₁:=a₁)
        (a₀:=a₀) (b₁:=c₁) (b₀:=c₀) (h_a:=h_split_a) (h_b:=h_split_c)]
    simp_rw [hmul]
    rw [join_add_join]
    rw [join_eq_join_iff]
    ring_nf
    simp only [and_self]

lemma concrete_mul_right_distrib
    {h_k : k > 0} (prevBTFieldProps : ConcreteBTFieldProps (k := k - 1))
  (a b c : ConcreteBTField k) :
    concrete_mul (a + b) c = concrete_mul a c + concrete_mul b c := by
  rw [concrete_mul_comm prevBTFieldProps (h_k:=h_k) (a:=(a + b)) (b:=c)]
  rw [concrete_mul_comm prevBTFieldProps (h_k:=h_k) (a:=a) (b:=c)]
  rw [concrete_mul_comm prevBTFieldProps (h_k:=h_k) (a:=b) (b:=c)]
  exact concrete_mul_left_distrib prevBTFieldProps (h_k:=h_k) (a:=c) (b:=a) (c:=b)

lemma norm_of_ne_zero_is_ne_zero {k : ℕ}
    {h_k_gt_0 : k > 0} (prevBTFieldResult : ConcreteBTFStepResult (k := k - 1))
  (a : ConcreteBTField k) (h_a_ne_zero : a ≠ 0) :
  let a₁ := (split h_k_gt_0 a).1
  let a₀ := (split h_k_gt_0 a).2
  concrete_mul a₀ (a₀ + concrete_mul a₁ (Z (k - 1))) + concrete_mul a₁ a₁ ≠ 0 := by
  letI : Field (ConcreteBTField (k - 1)) := mkFieldInstance prevBTFieldResult.toConcreteBTFieldProps
  have hmul : ∀ (a b : ConcreteBTField (k - 1)), concrete_mul a b = a * b := fun a b => rfl
  -- Set up local variables for convenience
  set a₁ := (split h_k_gt_0 a).1
  set a₀ := (split h_k_gt_0 a).2
  simp_rw [hmul]
  rw [left_distrib]
  have ha : a = 《a₁, a₀》 := by
    apply (join_of_split h_k_gt_0 a a₁ a₀) rfl
  set Na := a₀*a₀ + a₀*(a₁*Z (k - 1)) + a₁*a₁ -- ⊢ Na ≠ 0
  -- Main proof by contradiction
  by_contra h_Na_is_zero
  by_cases h_a₁_zero : a₁ = 0
  · -- Case 1 : a₁ = 0
    have h_a₀_ne_zero : a₀ ≠ 0 := by
      intro h_a₀_zero
      have h_a_is_zero : a = 0 := by
        rw [ha, h_a₁_zero, h_a₀_zero]
        rw! [←zero_is_0, ←zero_is_0, join_zero_zero]
        rfl
      exact h_a_ne_zero h_a_is_zero
    have h_Na_eq_a₀_sq : Na = a₀ * a₀ := by
      simp only [Na, Z, h_a₁_zero, mul_zero, add_zero, zero_mul]
    rw [h_Na_eq_a₀_sq] at h_Na_is_zero -- h_Na_is_zero : a₀ * a₀ = 0
    -- In a field, a₀ * a₀ = 0 implies a₀ = 0.
    have h_a₀_is_zero_from_mul := (mul_self_eq_zero).mp h_Na_is_zero
    -- This contradicts our proof that a₀ is non-zero.
    exact h_a₀_ne_zero h_a₀_is_zero_from_mul
  · -- Case 2 : a₁ ≠ 0
    -- Since a₁ is a non-zero element of a field, its inverse exists.
    set a₁_inv := a₁⁻¹
    set r := a₀ * a₁_inv
    -- We have Na = 0. The goal is to manipulate this equation to show
    -- that it implies the defining polynomial has a root in the base field.
    have h_root : r*r + r*Z (k - 1) + 1 = 0 := by
      have h_manip : (a₁_inv * a₁_inv) * Na = 0 := by rw [h_Na_is_zero, mul_zero]
      rw [show Na = a₀*a₀ + (a₀*a₁)*Z (k - 1) + a₁*a₁ by { simp [Na]; ring }] at h_manip
      rw [left_distrib, left_distrib] at h_manip
      rw [h_manip.symm]
      have h1 : r * r = a₁_inv * a₁_inv * (a₀ * a₀) := by ring
      have h2 : r * Z (k - 1) = a₁_inv * a₁_inv * (a₀ * a₁ * Z (k - 1)) := by
        apply Eq.symm
        -- ⊢ a₁_inv * a₁_inv * (a₀ * a₁ * Z (k - 1)) = r * Z (k - 1)
        calc _ = (a₁ * a₁_inv) * (a₀ * a₁_inv) * Z (k - 1) := by ring
          _ = (a₀ * a₁_inv) * Z (k - 1) := by
            rw [mul_inv_cancel₀ (a:=a₁) (by omega)]; norm_num
          _ = _ := by rfl
      have h3 : a₁_inv * a₁_inv * (a₁ * a₁) = 1 := by
        calc _ = a₁_inv * (a₁_inv * a₁) * a₁ := by ring
          _ = a₁_inv * a₁ * (a₁_inv * a₁) := by ring
          _ = (a₁ * a₁_inv) * (a₁ * a₁_inv) := by ring
          _ = 1 := by rw [mul_inv_cancel₀ (a:=a₁) (by omega)]; norm_num
      rw [h1, h2, h3]
    have h_is_root : (X^2 + C (Z (k - 1)) * X + 1).eval (r) = 0 := by
      simp only [pow_two, eval_add, eval_mul, eval_X, eval_C, eval_one, ←h_root]
      ring
    -- A polynomial that has a root in its base field cannot be irreducible.
    have h_not_irreducible : ¬ Irreducible (X^2 + C (Z (k - 1)) * X + 1) := by
      apply not_irreducible_of_isRoot_of_degree_gt_one (X^2 + C (Z (k - 1)) * X + 1)
      · use r
        simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
        rw [mul_comm, pow_two]
        exact h_root
      · letI := prevBTFieldResult.instFintype
        have h_deg := degree_definingPoly (s:=Z (k - 1))
        unfold definingPoly at h_deg
        rw [h_deg]; norm_num

    -- This gives our final contradiction, because our field extension requires
    -- the defining polynomial to be irreducible.
    have h:= prevBTFieldResult.instIrreduciblePoly
    unfold definingPoly at h
    exact h_not_irreducible h

lemma concrete_mul_inv_cancel
    (prevBTFieldResult : ConcreteBTFStepResult (k := k - 1))
  (a : ConcreteBTField k) (h : a ≠ 0) :
  concrete_mul a (concrete_inv a) = one := by
  letI : Field (ConcreteBTField (k - 1)) := mkFieldInstance prevBTFieldResult.toConcreteBTFieldProps
  have hmul : ∀ (a b : ConcreteBTField (k - 1)), concrete_mul a b = a * b := fun a b => rfl
  unfold concrete_inv
  by_cases h_k_zero : k = 0
  · rw [dif_pos h_k_zero]
    have h_2_pow_k_eq_1 : 2 ^ k = 1 := by rw [h_k_zero]; norm_num
    let a0 : ConcreteBTField 0 := Eq.mp (congrArg ConcreteBTField h_k_zero) a
    have a0_is_eq_mp_a : a0 = Eq.mp (congrArg ConcreteBTField h_k_zero) a := by rfl
    rcases concrete_eq_zero_or_eq_one (a := a) (h_k_zero:=h_k_zero) with (ha0 | ha1)
    · -- ha0 : a = zero (k:=k)
      have a_is_zero : a = zero (k:=k) := ha0
      have a_is_0 : a = 0 := by rw [←zero_is_0, a_is_zero]
      contradiction
    · -- ha1 : a = 1
      have a_is_1 : a = 1 := ha1
      have a_ne_0 : a ≠ 0 := by rw [a_is_1]; exact one_ne_zero
      rw [if_neg a_ne_0]
      rw [←one_is_1]
      rw [concrete_mul_one prevBTFieldResult.toConcreteBTFieldProps (a:=a)]
      rw [ha1]
  · by_cases h_a_zero : a = 0
    · contradiction
    · rw [dif_neg h_k_zero]
      rw [dif_neg h_a_zero]
      by_cases h_a_one : a = 1
      · rw [dif_pos h_a_one]
        rw [←one_is_1]
        rw [concrete_mul_one prevBTFieldResult.toConcreteBTFieldProps (a:=a)]
        rw [h_a_one, one_is_1]
      · rw [dif_neg h_a_one]
        have h_k_gt_0 : k > 0 := Nat.zero_lt_of_ne_zero h_k_zero
        let split_a := split h_k_gt_0 a
        let a₁ := split_a.fst
        let a₀ := split_a.snd
        have h_a_split : split h_k_gt_0 a = (a₁, a₀) := by rfl
        have h_a₁ : (split h_k_gt_0 a).1 = a₁ := by rfl
        have h_a₀ : (split h_k_gt_0 a).2 = a₀ := by rfl
        have h_a₁_a₀ : a = 《 a₁, a₀ 》 := by exact (join_of_split h_k_gt_0 a a₁ a₀) h_a_split
        simp_rw [h_a₁, h_a₀] -- resolve the match of split a
        -- ⊢ a * b = 1
        -- Let `b = (b_hi, b_lo) = (a_hi * N(a)⁻¹, (a_lo + a_hi*X_{k-1}) * N(a)⁻¹)`
        -- be inverse of `a = (a_hi, a_lo)`. We need to prove that `a * b = 1`.
        set Na := a₀ * (a₀ + a₁ * (Z (k - 1))) + a₁ * a₁
        have h_Na_ne_0 : Na ≠ 0 := norm_of_ne_zero_is_ne_zero
          prevBTFieldResult a h_a_zero
        change a * (《 Na⁻¹ * a₁, Na⁻¹ * (a₀ + a₁ * (Z (k - 1))) 》) = one
        set b := 《 Na⁻¹ * a₁, Na⁻¹ * (a₀ + a₁ * (Z (k - 1))) 》 with hb
        have h_b_split := split_of_join h_k_gt_0 b (h_join:=hb)
        have h_mul_eq := concrete_mul_eq prevBTFieldResult.toConcreteBTFieldProps
          (h_k:=h_k_gt_0) (a:=a) (b:=b) (a₁:=a₁) (a₀:=a₀)
          (b₁:=Na⁻¹ * a₁) (b₀:=Na⁻¹ * (a₀ + a₁ * (Z (k - 1)))) (h_a:=h_a_split) (h_b:=h_b_split)
        conv_lhs at h_mul_eq => change a * b
        rw [h_mul_eq]
        have h_one_eq_join_0_1 : one (k:=k) = 《 0, 1 》 := join_zero_one (k:=k) (h_k:=h_k_gt_0).symm
        conv_rhs => rw [h_one_eq_join_0_1]
        rw [join_eq_join_iff] -- split into equalities in each part in level (k-1)
        simp_rw [hmul]
        constructor
        · rw [left_distrib (a:=Na⁻¹) (b:=a₀) (c:=a₁ * (Z (k - 1)))]
          rw [right_distrib (c:=a₁)]
          simp_rw [add_assoc (c:=(a₁ * ((Na⁻¹) * a₁)) * (Z (k - 1)))] -- this rw is done TWICE
          rw [←mul_assoc (a:=a₀) (b:=Na⁻¹) (c:=a₁)]
          rw [mul_comm (a:=a₀) (b:=Na⁻¹)] -- swap a₀ and Na⁻¹
          rw [mul_assoc (a:=Na⁻¹) (b:=a₀) (c:=a₁)]
          rw [mul_assoc (a:=Na⁻¹) (b:=a₁ * (Z (k - 1))) (c:=a₁)]
          rw [mul_assoc (a:=a₁) (b:=(Na⁻¹) * a₁) (c:=Z (k - 1))]
          rw [← add_assoc (a:=(Na⁻¹) * (a₀ * a₁)) (b:=(Na⁻¹) * (a₀ * a₁))]
          rw [add_self_cancel (a:=(Na⁻¹) * (a₀ * a₁)), zero_add]
          conv_lhs =>
            enter [1]
            rw [mul_comm (a := Na⁻¹)]
            rw [mul_assoc]
            rw [mul_comm (a := a₁) (b := Na⁻¹)]
            rw [mul_assoc]
            rw [mul_comm (a := Z (k - 1))]
          rw [add_self_cancel]
        · rw [←mul_assoc (a:=a₀), ←mul_assoc (a:=a₁)]
          rw [mul_comm (a:=a₀) (b:=Na⁻¹), mul_comm (a:=a₁) (b:=Na⁻¹)]
          simp_rw [mul_assoc (a:=Na⁻¹)]
          rw [←left_distrib (a:=Na⁻¹)]
          rw [mul_comm (a:=Na⁻¹)];
          change Na * Na⁻¹ = 1
          exact CommGroupWithZero.mul_inv_cancel Na h_Na_ne_0

lemma concrete_inv_one :
    concrete_inv (k:=k) 1 = 1 := by
  unfold concrete_inv
  by_cases h_k_zero : k = 0
  · simp only [h_k_zero]; norm_num
  · simp only [h_k_zero]; norm_num

end BTFieldPropsOneLevelLiftingLemmas

/-! Inductive tower construction, using lemmas from `BTFieldPropsOneLevelLiftingLemmas` -/
section TowerFieldsConstruction

lemma Z_square_eq (k : ℕ) (prevBTFieldProps : ConcreteBTFieldProps (k := k))
    (curBTFieldProps : ConcreteBTFieldProps (k := (k + 1))) :
  letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance curBTFieldProps
  (Z (k + 1)) ^ 2 = 《 Z (k), 1 》 := by
  letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance curBTFieldProps
  have hmul : ∀ (a b : ConcreteBTField (k - 1)), concrete_mul a b = a * b := fun a b => rfl
  rw [pow_two]
  change concrete_mul (Z (k + 1)) (Z (k + 1)) = 《 Z (k), 1 》
  have h_split_Z_k_add_1 : split (k:=k+1) (h:=by omega) (Z (k + 1)) = (1, 0) := by
    exact Eq.symm
      (split_of_join (by omega) (Z (k + 1)) 1 0 rfl)
  have h_mul_eq := curBTFieldProps.mul_eq (a:=Z (k+1)) (b:=Z (k+1))
    (a₁:=1) (a₀:=0) (b₁:=1) (b₀:=0) (h_k:=by omega)
    (by exact id (Eq.symm h_split_Z_k_add_1)) (by exact id (Eq.symm h_split_Z_k_add_1))
  rw [h_mul_eq]
  simp_rw [←zero_is_0, ←one_is_1]
  simp only [Nat.add_one_sub_one]
  simp_rw [prevBTFieldProps.mul_zero, prevBTFieldProps.mul_one,
    prevBTFieldProps.add_zero, prevBTFieldProps.one_mul]
  simp_rw [prevBTFieldProps.zero_add]

def liftBTFieldProps (k : ℕ) (prevBTFResult : ConcreteBTFStepResult (k := k)) :
  ConcreteBTFieldProps (k + 1) := {
    zero_mul := concrete_zero_mul (prevBTFResult.toConcreteBTFieldProps),
    zero_mul' := fun a => by
      rw [←zero_is_0]; exact concrete_zero_mul (k := k + 1)
        (prevBTFResult.toConcreteBTFieldProps) a
    mul_zero := concrete_mul_zero (k := k + 1) (prevBTFResult.toConcreteBTFieldProps),
    mul_zero' := fun a => by
      rw [←zero_is_0]; exact concrete_mul_zero (k := k + 1)
        (prevBTFResult.toConcreteBTFieldProps) a
    one_mul := concrete_one_mul (k := k + 1) (prevBTFResult.toConcreteBTFieldProps),
    mul_one := concrete_mul_one (k := k + 1) (prevBTFResult.toConcreteBTFieldProps),
    mul_assoc := concrete_mul_assoc (k := k + 1)
      (prevBTFResult.toConcreteBTFieldProps) (h_k := Nat.succ_pos k),
    mul_comm := concrete_mul_comm (k := k + 1)
      (prevBTFResult.toConcreteBTFieldProps) (h_k := Nat.succ_pos k),
    mul_left_distrib := concrete_mul_left_distrib (k := k + 1)
      (prevBTFResult.toConcreteBTFieldProps) (h_k := Nat.succ_pos k),
    mul_right_distrib := concrete_mul_right_distrib (k := k + 1)
      (prevBTFResult.toConcreteBTFieldProps) (h_k := Nat.succ_pos k),
    add_assoc := add_assoc,
    add_comm := add_comm,
    add_zero := add_zero,
    zero_add := zero_add,
    add_neg := neg_add_cancel,
    mul_inv_cancel := concrete_mul_inv_cancel (k:=k + 1)
      (prevBTFResult),
    mul_eq :=
      fun a b h_k =>
        concrete_mul_eq (k:=k + 1)
          (prevBTFResult.toConcreteBTFieldProps) (a) (b)
          (h_k:=h_k)
  }

def liftConcreteBTField (k : ℕ) (prevBTFResult : ConcreteBTFStepResult (k := k)) :
  Field (ConcreteBTField (k + 1)) := by
  exact mkFieldInstance (k:=k + 1) (props:=liftBTFieldProps (k:=k) (prevBTFResult:=prevBTFResult))

/--
The canonical ring homomorphism embedding `ConcreteBTField k` into
`ConcreteBTField (k + 1)`.
This is the `AdjoinRoot.of` map.
-/
def concreteCanonicalEmbedding (k : ℕ)
    (prevBTFieldProps : ConcreteBTFieldProps (k := (k)))
    (curBTFieldProps : ConcreteBTFieldProps (k := (k + 1))) :
  letI := mkFieldInstance prevBTFieldProps
  letI := mkFieldInstance curBTFieldProps
  ConcreteBTField k →+* ConcreteBTField (k + 1) := by
  letI := mkFieldInstance prevBTFieldProps
  letI := mkFieldInstance curBTFieldProps
  exact {
    toFun := fun x => 《 zero (k:=k), x 》
    map_one' := join_zero_one (k:=k + 1) (h_k:=by omega)
    map_mul' := fun x y => by
      -- ⊢ join ⋯ zero (x * y) = join ⋯ zero x * join ⋯ zero y
      set hx := join (k:=k+1) (h_pos:=by omega) (hi:=zero (k:=k)) (lo:=x)
      set hy := join (k:=k+1) (h_pos:=by omega) (hi:=zero (k:=k)) (lo:=y)
      have h_mul_eq := curBTFieldProps.mul_eq

      have h_x_split := split_of_join (k:=k + 1) (h_pos:=by omega)
        (x:=hx) (zero (k:=k)) (x) (h_join:=rfl)
      have h_y_split := split_of_join (k:=k + 1) (h_pos:=by omega)
        (x:=hy) (zero (k:=k)) (y) (h_join:=rfl)
      -- rhs
      change join (by omega) zero (concrete_mul x y) = concrete_mul hx hy
      have h_mul_eq_join_split := h_mul_eq hx hy (by omega) h_x_split h_y_split
      rw [h_mul_eq_join_split]
      simp only [Nat.add_one_sub_one]

      have h_left : zero (k:=k) = concrete_mul x zero + concrete_mul y zero +
        concrete_mul (concrete_mul zero zero) (Z k) := by
        simp only [prevBTFieldProps.mul_zero, prevBTFieldProps.zero_mul]
        rw! [zero_is_0]
        norm_num

      have h_right : concrete_mul x y = concrete_mul x y + concrete_mul zero zero:= by
        rw [prevBTFieldProps.mul_zero, zero_is_0]
        norm_num

      rw [←h_left, ←h_right]
    map_add' := fun x y => by
      -- ⊢ join ⋯ zero (x + y) = join ⋯ zero x + join ⋯ zero y
      simp only [join_add_join, Nat.add_one_sub_one]
      rw [zero_is_0, zero_add]
    map_zero' := by
      rw! [←zero_is_0, join_zero_zero, zero_is_0]
      rfl
  }

instance instAlgebraLiftConcreteBTField (k : ℕ)
  (prevBTFResult : ConcreteBTFStepResult (k := k)) :
  letI := mkFieldInstance (prevBTFResult.toConcreteBTFieldProps)
  letI := liftConcreteBTField (k:=k) prevBTFResult
  Algebra (ConcreteBTField k) (ConcreteBTField (k + 1)) :=
  letI := mkFieldInstance (prevBTFResult.toConcreteBTFieldProps)
  letI := liftConcreteBTField (k:=k) prevBTFResult
  RingHom.toAlgebra (R:=ConcreteBTField k) (S:=ConcreteBTField (k + 1))
    (i:=(concreteCanonicalEmbedding (k:=k)
      (prevBTFieldProps:=prevBTFResult.toConcreteBTFieldProps)
      (curBTFieldProps:=liftBTFieldProps (k:=k) (prevBTFResult:=prevBTFResult))))

lemma Z_square_mul_form
    (k : ℕ)
  (prev : ConcreteBTFStepResult (k := k)) :
  letI : Field (ConcreteBTField k) := mkFieldInstance (prev.toConcreteBTFieldProps)
  letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance (k:=k+1)
    (props:=liftBTFieldProps (k:=k) (prevBTFResult:=prev))
  letI : Algebra (ConcreteBTField k) (ConcreteBTField (k + 1)) :=
    instAlgebraLiftConcreteBTField k prev
  Z (k + 1) ^ 2
    = Z (k + 1)
      * (algebraMap (ConcreteBTField k) (ConcreteBTField (k + 1))) (Z k)
      + 1 := by
  let curProps := liftBTFieldProps (k:=k) (prevBTFResult:=prev)
  letI : Field (ConcreteBTField k) := mkFieldInstance (prev.toConcreteBTFieldProps)
  letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance (k:=k+1) (props:=curProps)
  letI : Algebra (ConcreteBTField k) (ConcreteBTField (k + 1)) :=
    instAlgebraLiftConcreteBTField k prev
  -- use the join-form version and rewrite
  have h := Z_square_eq (k:=k) (prevBTFieldProps:=prev.toConcreteBTFieldProps)
    (curBTFieldProps:=curProps)
  rw [h]
  have h_Z_next: Z (k + 1) = 《 one (k:=k), zero (k:=k) 》 := rfl
  change _ =  concrete_mul (a := Z (k + 1)) (b:=《 zero (k:=k), Z k 》) + 1
  rw [h_Z_next]
  rw [curProps.mul_eq (h_k:=by omega) (a:= 《 one (k:=k), zero (k:=k) 》)
    (b:=《 zero (k:=k), Z k 》) (a₁:=1) (a₀:=0) (b₁:=0) (b₀:=Z k)
    (_h_a:=by rw [split_of_join]; rfl) (_h_b:=by rw [split_of_join]; rfl)]
  conv_rhs =>
    enter [2]; change one; rw [←join_zero_one (k:=k + 1) (h_k:=by omega)];
    simp only [Nat.add_one_sub_one]
  rw [join_add_join]
  simp only [Nat.add_one_sub_one]
  have hmul : ∀ (a b : ConcreteBTField k), concrete_mul a b = a * b := fun a b => rfl
  rw! [hmul, hmul, hmul, hmul, hmul]
  simp only [mul_zero, mul_one, _root_.zero_add, zero_mul, _root_.add_zero, zero_is_0, one_is_1]

lemma sum_inv_Z_next_eq
    (k : ℕ)
  (prev : ConcreteBTFStepResult (k := k)) :
  letI : Field (ConcreteBTField k) := mkFieldInstance (prev.toConcreteBTFieldProps)
  letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance (k:=k+1)
    (props:=liftBTFieldProps (k:=k) (prevBTFResult:=prev))
  letI : Algebra (ConcreteBTField k) (ConcreteBTField (k + 1)) :=
    instAlgebraLiftConcreteBTField k prev
  Z (k + 1) + (Z (k + 1))⁻¹ = (algebraMap (ConcreteBTField k) (ConcreteBTField (k + 1))) (Z k) := by
  let curProps := liftBTFieldProps (k:=k) (prevBTFResult:=prev)
  letI : Field (ConcreteBTField k) := mkFieldInstance (prev.toConcreteBTFieldProps)
  letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance (k:=k+1) (props:=curProps)
  letI : Algebra (ConcreteBTField k) (ConcreteBTField (k + 1)) :=
    instAlgebraLiftConcreteBTField k prev
  apply mul_left_cancel₀ (a := Z (k + 1)) (ha:=Z_ne_zero)
  rw [mul_add, ←pow_two]
  have h_mul_inv: Z (k + 1) * (Z (k + 1))⁻¹ = 1 := by
    change concrete_mul (Z (k + 1)) (concrete_inv (Z (k + 1))) = one
    exact curProps.mul_inv_cancel (a:= Z (k + 1)) (Z_ne_zero)
  rw [h_mul_inv, Z_square_mul_form (k:=k) (prev:=prev), add_assoc]
  rw [add_self_cancel, add_zero]
-------------------------------------------------------------------------------------------
def getBTFResult (k : ℕ) : ConcreteBTFStepResult k :=
  match k with
  | 0 =>
    let base : ConcreteBTFieldProps 0 := {
      mul_eq := fun a b h_k _ _ _ _ _ _ => by
        have h_l_ne_lt_0 := Nat.not_lt_zero 0
        exact absurd h_k h_l_ne_lt_0,
      zero_mul := concrete_zero_mul0,
      zero_mul' := concrete_zero_mul0,
      mul_zero := concrete_mul_zero0,
      mul_zero' := concrete_mul_zero0,
      one_mul := concrete_one_mul0,
      mul_one := concrete_mul_one0,
      mul_assoc := concrete_mul_assoc0,
      mul_comm := concrete_mul_comm0,
      mul_left_distrib := concrete_mul_left_distrib0,
      mul_right_distrib := concrete_mul_right_distrib0,
      add_assoc := add_assoc,
      add_comm := add_comm,
      add_zero := add_zero,
      zero_add := zero_add,
      add_neg := neg_add_cancel,
      mul_inv_cancel := fun a ha => by
        rcases concrete_eq_zero_or_eq_one (a := a) (h_k_zero:=by omega) with (ha0 | ha1)
        · subst ha0
          simp only [concrete_zero_mul0]; exact False.elim (ha rfl)
        · subst ha1
          simp only [concrete_one_mul0];
          simp only [concrete_inv, ↓reduceDIte]
          exact rfl
    }
    letI : Field (ConcreteBTField 0) := mkFieldInstance (k:=0) (props:=base)
    letI instFintype0: Fintype (ConcreteBTField 0) := {
      elems := {0, 1}
      complete := fun x => by
        rcases concrete_eq_zero_or_eq_one (a := x) (h_k_zero:=by omega) with (ha0 | ha1)
        · rw [zero_is_0] at ha0
          simp only [ha0, Finset.mem_insert, Finset.mem_singleton, zero_ne_one, or_false]
        · rw [one_is_1] at ha1
          simp only [ha1, Finset.mem_insert, one_ne_zero, Finset.mem_singleton, or_true]
    }
    have hZ0_eq_1: Z 0 = 1 := rfl
    let specialElement : ConcreteBTField 0 := 1
    let specialElementNeZero : NeZero specialElement := instNeZeroConcreteBTFieldOfNat
    let newPoly : (ConcreteBTField 0)[X] := definingPoly (F:=ConcreteBTField 0) (s:=specialElement)
    have nat_deg_poly_is_2 : newPoly.natDegree = 2 := natDegree_definingPoly specialElement
    have coeffOfX_0 : newPoly.coeff 0 = 1 := definingPoly_coeffOf0 specialElement
    have coeffOfX_1 : newPoly.coeff 1 = specialElement := definingPoly_coeffOf1 specialElement
    let instIrreduciblePoly : Irreducible newPoly := by
      by_contra h_not_irreducible
      -- ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
      obtain ⟨c₁, c₂, h_mul, h_add⟩ :=
        (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
          (definingPoly_is_monic specialElement) (nat_deg_poly_is_2)).mp h_not_irreducible
      rw [coeffOfX_0] at h_mul -- 1 = c₁ * c₂
      rw [coeffOfX_1] at h_add -- specialElement = c₁ + c₂
      -- since c₁, c₂ ∈ GF(2), c₁ * c₂ = 1 => c₁ = c₂ = 1
      have c1_c2_eq_one : c₁ = 1 ∧ c₂ = 1 := by
        -- In GF(2), elements are only 0 or 1
        have c1_cases : c₁ = 0 ∨ c₁ = 1 := by
          exact concrete_eq_zero_or_eq_one (a:=c₁) (h_k_zero:=by omega)
        have c2_cases : c₂ = 0 ∨ c₂ = 1 := by
          exact concrete_eq_zero_or_eq_one (a:=c₂) (h_k_zero:=by omega)
        -- Case analysis on c₁ and c₂
        rcases c1_cases with c1_zero | c1_one
        · -- If c₁ = 0
          rw [c1_zero] at h_mul
          -- Then 0 * c₂ = 1, contradiction
          simp at h_mul
        · -- If c₁ = 1
          rcases c2_cases with c2_zero | c2_one
          · -- If c₂ = 0
            rw [c2_zero] at h_mul
            -- Then 1 * 0 = 1, contradiction
            simp at h_mul
          · -- If c₂ = 1
            -- Then we have our result
            exact ⟨c1_one, c2_one⟩
      -- Now we can show specialElement = 0
      have specialElement_eq_zero : specialElement = 0 := by
        rw [h_add]  -- Use c₁ + c₂ = specialElement
        rw [c1_c2_eq_one.1, c1_c2_eq_one.2]  -- Replace c₁ and c₂ with 1
        -- In GF(2), 1 + 1 = 0
        exact rfl
      -- But we know specialElement = 1
      have specialElement_eq_one : specialElement = 1 := by rfl
      rw [specialElement_eq_zero] at specialElement_eq_one
      -- (0 : GF(2)) = (1 : GF(2))
      have one_ne_zero_in_gf2 : (1 : ConcreteBTField 0) ≠ (0 : ConcreteBTField 0) := by
        exact NeZero.out
      exact one_ne_zero_in_gf2 specialElement_eq_zero -- contradiction

    let result : ConcreteBTFStepResult 0 := {
      toConcreteBTFieldProps := base,
      instFintype := instFintype0,
      fieldFintypeCard := rfl,
      sumZeroIffEq := fun x y => by
        constructor
        · -- (→) If x + y = 0, then x = y
          intro h_sum_zero
          -- Case analysis on x
          rcases concrete_eq_zero_or_eq_one (a := x) (h_k_zero:=by omega) with x_zero | x_one
          · -- Case x = 0
            rcases concrete_eq_zero_or_eq_one (a := y) (h_k_zero:=by omega) with y_zero | y_one
            · -- Case y = 0
              rw [x_zero, y_zero]
            · -- Case y = 1
              simp only [x_zero, y_one] at h_sum_zero
              contradiction
          · -- Case x = 1
            rcases concrete_eq_zero_or_eq_one (a := y) (h_k_zero:=by omega) with y_zero | y_one
            · -- Case y = 0
              simp only [x_one, y_zero] at h_sum_zero
              contradiction
            · -- Case y = 1
              rw [x_one, y_one]
        · -- (←) If x = y, then x + y = 0
          intro h_eq
          rw [h_eq]
          -- In GF(2), x + x = 0 for any x
          rcases concrete_eq_zero_or_eq_one (a := y) (h_k_zero:=by omega) with y_zero | y_one
          · rw [y_zero]; rfl
          · rw [y_one]; rfl
      traceMapEvalAtRootsIs1 := by
        exact {
          element_trace := by
            rw [Nat.pow_zero] -- 2^0 = 1
            rw [Finset.range_one] -- range 1 = {0}
            norm_num
            exact hZ0_eq_1
          inverse_trace := by
            rw [Nat.pow_zero] -- 2^0 = 1
            simp [Finset.range_one] -- range 1 = {0}
            exact hZ0_eq_1
        },
      instIrreduciblePoly := instIrreduciblePoly
    }
    result
  | k + 1 => by
    let prevBTFResult := getBTFResult k
    let baseProps := liftBTFieldProps (k:=k) (prevBTFResult:=prevBTFResult)

    letI inst_Field_ConcreteBTField_k: Field (ConcreteBTField k) :=
      mkFieldInstance (k:=k) (props:=prevBTFResult.toConcreteBTFieldProps)

    letI instFintype_ConcreteBTField_k: Fintype (ConcreteBTField k) := prevBTFResult.instFintype
    letI : Finite (ConcreteBTField k) := by exact Fintype.finite instFintype_ConcreteBTField_k
    have equivRelation: ConcreteBTField (k + 1) ≃ ConcreteBTField (k) × ConcreteBTField (k) :=
      equivProd (k:=k + 1) (by omega)
    letI: Fintype (ConcreteBTField k × ConcreteBTField k) :=
      instFintypeProd (α:=ConcreteBTField k) (β:=ConcreteBTField k)

    let instFintype : Fintype (ConcreteBTField (k + 1)) := by
      exact Fintype.ofEquiv (ConcreteBTField (k) × ConcreteBTField (k)) equivRelation.symm

    let fieldFintypeCard : Fintype.card (ConcreteBTField (k + 1)) = 2^(2^(k + 1)) := by
      let e := equivRelation.symm
      have equivCard := Fintype.ofEquiv_card equivRelation.symm
      let res := Fintype.card_prod (α:=ConcreteBTField k) (β:=ConcreteBTField k)
      rw [Fintype.card_prod (α:=ConcreteBTField k) (β:=ConcreteBTField k)] at equivCard
      rw [prevBTFResult.fieldFintypeCard] at equivCard
      have card_simp : 2 ^ 2 ^ k * 2 ^ 2 ^ k = 2 ^ (2 ^ k + 2 ^ k) := by rw [Nat.pow_add]
      have exp_simp : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
        rw [←Nat.mul_two, Nat.pow_succ]
      rw [card_simp, exp_simp] at equivCard
      exact equivCard

    letI inst_Fintype_ConcreteBTField_k: Fintype (ConcreteBTField (k)) := prevBTFResult.instFintype
    letI : Field (ConcreteBTField (k + 1)) := mkFieldInstance (k:=k + 1) (props:=baseProps)
    let sumZeroIffEq := fun x y => -- due to our definition of addition = BitVec.xor
        add_eq_zero_iff_eq (k:=(k + 1)) (a:=x) (b:=y)
    letI instAlgebra: Algebra (ConcreteBTField k) (ConcreteBTField (k + 1)):=
      instAlgebraLiftConcreteBTField k prevBTFResult
    let traceMapEvalAtRootsIs1 := traceMapProperty_of_quadratic_extension
      (F_prev:=ConcreteBTField k) (t1:=Z k) (k:=k)
      (fintypeCardPrev:=prevBTFResult.fieldFintypeCard)
      (F_cur:=ConcreteBTField (k + 1)) (u:=Z (k + 1)) (h_rel:= {
        sum_inv_eq := sum_inv_Z_next_eq (k:=k) (prev:=prevBTFResult)
        h_u_square := Z_square_mul_form (k:=k) (prev:=prevBTFResult)
      }) (prev_trace_map := prevBTFResult.traceMapEvalAtRootsIs1
      ) (sumZeroIffEq := sumZeroIffEq)

    letI : CharP (ConcreteBTField (k + 1)) 2 :=
      charP_eq_2_of_add_self_eq_zero (F:=(ConcreteBTField (k + 1)))
      (sumZeroIffEq:=sumZeroIffEq)

    let instIrreduciblePoly :=
      irreducible_quadratic_defining_poly_of_traceMap_eq_1
        (F:=(ConcreteBTField (k + 1))) (s:=Z (k + 1)) (k:=k+1)
        (trace_map_prop := traceMapEvalAtRootsIs1) (fintypeCard := fieldFintypeCard)

    let result : ConcreteBTFStepResult (k + 1) := {
      toConcreteBTFieldProps := baseProps,
      instFintype := instFintype,
      fieldFintypeCard := fieldFintypeCard,
      sumZeroIffEq := sumZeroIffEq,
      traceMapEvalAtRootsIs1 := traceMapEvalAtRootsIs1,
      instIrreduciblePoly := instIrreduciblePoly
    }

    exact result

instance instFieldConcrete {k : ℕ} : Field (ConcreteBTField k) :=
  mkFieldInstance (getBTFResult k).toConcreteBTFieldProps

instance instCharP2 {k : ℕ} : CharP (ConcreteBTField k) 2 :=
  charP_eq_2_of_add_self_eq_zero (F:=(ConcreteBTField k)) (sumZeroIffEq:=add_eq_zero_iff_eq)

instance (k : ℕ) : Fintype (ConcreteBTField k) := (getBTFResult k).instFintype

instance instFintype {k : ℕ} : Fintype (ConcreteBTField k) := (getBTFResult k).instFintype

/-- adjoined root of poly k, generator of successor field BTField (k + 1) -/
@[simp]
def 𝕏 (k : ℕ) : ConcreteBTField (k + 1) := Z (k + 1)

end TowerFieldsConstruction

end ConcreteBinaryTower
