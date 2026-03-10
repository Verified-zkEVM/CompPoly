/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import CompPoly.Fields.Binary.Tower.Support.Preliminaries

/-!
# Binary Tower Fin Helpers

Finite-index helper lemmas for bit manipulations used in binary tower proofs.
-/

open Polynomial
open AdjoinRoot
open Module

section FinHelpers

@[simp]
theorem bit_finProdFinEquiv_symm_2_pow_succ {n : ℕ} (j : Fin (2 ^ (n + 1))) (i : Fin (n + 1)) :
    let e:=finProdFinEquiv (m:=2^(n)) (n:=2).symm
    Nat.getBit (i) j = if i.val > 0 then Nat.getBit (i.val-1) (e j).1 else (e j).2 := by
  simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat]
  if h_i_gt_0 : i.val > 0 then
    simp_rw [h_i_gt_0]
    simp only [↓reduceIte]
    rw [Nat.getBit_eq_pred_getBit_of_div_two (by omega)]
  else
    simp_rw [h_i_gt_0]
    simp only [↓reduceIte]
    simp only [gt_iff_lt, Fin.val_pos_iff, not_lt, Fin.le_zero_iff] at h_i_gt_0
    rw [h_i_gt_0]
    rw [Nat.getBit, Fin.val_zero, Nat.shiftRight_zero]
    simp only [Nat.and_one_is_mod]

/-- Equivalence between `Fin m × Fin n` and `Fin (m * n)`
which splits quotient part into Fin (n) and the remainder into Fin (m).
If m and n are powers of 2, the Fin (n) holds MSBs and Fin (m) holds LSBs.
This is a reversed version of `finProdFinEquiv`.
We put `m` before `n` for integration with `Basis.smulTower` in `multilinearBasis`
though it's a bit counter-intuitive.
-/
def leftDivNat {m n : ℕ} (i : Fin (m * n)) : Fin n := ⟨i / m, by
  apply Nat.div_lt_of_lt_mul
  exact i.2
⟩

def leftModNat {m n : ℕ} (h_m : m > 0) (i : Fin (m * n)) : Fin m := ⟨i % m, by
  apply Nat.mod_lt
  exact h_m
⟩

@[simps]
def revFinProdFinEquiv {m n : ℕ} (h_m : m > 0) : Fin m × Fin n ≃ Fin (m * n) where
  toFun x :=
      ⟨x.1.val + m * x.2.val,
      calc
        x.1.val + m * x.2.val < m + m * x.2.val := Nat.add_lt_add_right x.1.is_lt _
        _ = m * (1 + x.2.val) := by rw [Nat.left_distrib, mul_one]
        _ = m * Nat.succ x.2.val := by rw [Nat.add_comm]
        _ ≤ m * n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt x.2.is_lt)
        ⟩
  invFun := fun x => -- ⊢ Fin (m * n) → Fin m × Fin n
    (leftModNat (m:=m) (n:=n) h_m (i:=x), leftDivNat (m:=m) (n:=n) (i:=x))
  left_inv := fun ⟨x, y⟩ =>
    -- We need a proof that m > 0 for the division properties.
    -- This is provable because if m = 0, then Fin m is empty, so no `x` exists.
    Prod.ext
      (Fin.eq_of_val_eq <|
        calc
          (x.val + m * y.val) % m = x.val % m := by exact Nat.add_mul_mod_self_left (↑x) m ↑y
          _ = x.val := Nat.mod_eq_of_lt x.is_lt
          )
      (Fin.eq_of_val_eq <|
        calc
          (x.val + m * y.val) / m = x.val / m + y.val := by exact Nat.add_mul_div_left (↑x) (↑y) h_m
          _ = 0 + y.val := by rw [Nat.div_eq_of_lt x.is_lt]
          _ = y.val := Nat.zero_add y.val
          )
  right_inv x := by exact Fin.eq_of_val_eq <| Nat.mod_add_div x.val m

@[simp]
theorem bit_revFinProdFinEquiv_symm_2_pow_succ {n : ℕ} (j : Fin (2 ^ (n + 1))) (i : Fin (n + 1)) :
    let e : Fin (2 ^ n * 2) ≃ Fin (2 ^ n) × Fin 2 :=
      revFinProdFinEquiv (m:=2^(n)) (n:=2) (h_m:=by exact Nat.two_pow_pos n).symm
    let msb : Fin 2 := (e j).2
    let lsbs : Fin (2 ^ n) := (e j).1
    Nat.getBit (i) j = if i.val < n then Nat.getBit (i.val) lsbs else msb := by
  simp only [revFinProdFinEquiv_symm_apply]
  if h_i_lt_n : i < n then
    simp_rw [h_i_lt_n]
    simp only [↓reduceIte]
    rw [leftModNat]
    simp only;
    rw [← Nat.getLowBits_eq_mod_two_pow]
    rw [Nat.getBit_of_lowBits]
    simp only [h_i_lt_n, ↓reduceIte]
  else
    simp_rw [h_i_lt_n]
    simp only [↓reduceIte]
    rw [leftDivNat]
    simp only;
    simp at h_i_lt_n
    have hi_eq_n : i = n := by
      have h_i_lt : i < n + 1 := i.2
      have h_i_le_n : i ≤ n := by omega
      exact Eq.symm (Nat.le_antisymm h_i_lt_n h_i_le_n)
    set i' := i - n with h_i'
    have hi : i = i' + n := by omega
    rw [hi]
    have h_i' : i' = 0 := by omega
    rw [← Nat.getBit_of_highBits_no_shl]
    rw [Nat.getHighBits_no_shl, Nat.shiftRight_eq_div_pow]
    rw [h_i']
    simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mod_succ_eq_iff_lt,
      Nat.succ_eq_add_one, Nat.reduceAdd, gt_iff_lt]
    have hj_lt : j.val < (2^n * 2) := by
      calc j.val < 2 ^ (n + 1) := j.2
      _ = 2 ^ n * 2 := by rw [Nat.pow_succ]
    exact Nat.div_lt_of_lt_mul hj_lt

end FinHelpers
