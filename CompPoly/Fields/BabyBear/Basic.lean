/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.PrattCertificate
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
/-!
  # BabyBear Field `2^{31} - 2^{27} + 1`

  This is the field used by Risc Zero.
-/

namespace BabyBear

/-- The BabyBear field modulus, `2^31 - 2^27 + 1`. -/
@[reducible]
def fieldSize : Nat := 2 ^ 31 - 2 ^ 27 + 1

/-- The BabyBear prime field as a `ZMod`. -/
abbrev Field := ZMod fieldSize

/-- The BabyBear modulus is prime. -/
theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

/-!
  ## Constants

  These are convenience constants for the BabyBear field:
  - `pBits = 31`
  - `twoAdicity = 27` with `fieldSize - 1 = 2^27 * 15`
-/

/-- Bit width of the BabyBear modulus. -/
@[reducible]
def pBits : Nat := 31

/-- The largest supported power-of-two root-of-unity exponent for BabyBear. -/
@[reducible]
def twoAdicity : Nat := 27

instance : Fact (Nat.Prime fieldSize) := ⟨is_prime⟩

instance : _root_.Field Field := ZMod.instField fieldSize

instance : NonBinaryField Field where
  char_neq_2 := by
    simpa [Field, fieldSize] using
      (by decide : (2 : ZMod (2 ^ 31 - 2 ^ 27 + 1)) ≠ 0)

/-- Fermat-style inversion in `ZMod fieldSize`. -/
lemma inv_eq_pow (a : Field) (ha : a ≠ 0) : a⁻¹ = a ^ (fieldSize - 2) := by
  have hcard : Fintype.card Field = fieldSize := ZMod.card fieldSize
  have h1 : a ^ (fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (fieldSize - 2) = 1 := by
    rw [← pow_succ']; show a ^ (fieldSize - 2 + 1) = 1
    have : fieldSize - 2 + 1 = fieldSize - 1 := by unfold fieldSize; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-!
  ## Two-adicity and roots of unity table

  We record the factorization of `fieldSize - 1` and provide a precomputed table
  of `2^n`-th roots of unity for `0 ≤ n ≤ twoAdicity`.
-/

/-- The factorization `fieldSize - 1 = 2^twoAdicity * 15`. -/
lemma fieldSize_sub_one_factorization : fieldSize - 1 = 2 ^ twoAdicity * 15 := by
  unfold fieldSize twoAdicity
  decide

/-!
  A table of `2^n`-th roots of unity. The element at index `n` generates the
  multiplicative subgroup of order `2^n`.

  The first entry n = 0 is 1.
-/
/-- Precomputed generators for the BabyBear two-adic subgroups. -/
def twoAdicGenerators : List Field :=
  [
    (0x1 : Field),
    (0x78000000 : Field),
    (0x67055C21 : Field),
    (0x5EE99486 : Field),
    (0xBB4C4E4 : Field),
    (0x2D4CC4DA : Field),
    (0x669D6090 : Field),
    (0x17B56C64 : Field),
    (0x67456167 : Field),
    (0x688442F9 : Field),
    (0x145E952D : Field),
    (0x4FE61226 : Field),
    (0x4C734715 : Field),
    (0x11C33E2A : Field),
    (0x62C3D2B1 : Field),
    (0x77CAD399 : Field),
    (0x54C131F4 : Field),
    (0x4CABD6A6 : Field),
    (0x5CF5713F : Field),
    (0x3E9430E8 : Field),
    (0xBA067A3 : Field),
    (0x18ADC27D : Field),
    (0x21FD55BC : Field),
    (0x4B859B3D : Field),
    (0x3BD57996 : Field),
    (0x4483D85A : Field),
    (0x3A26EEF8 : Field),
    (0x1A427A41 : Field)
  ]

/-- The BabyBear two-adic generator table has one entry for each supported exponent. -/
@[simp] lemma twoAdicGenerators_length : twoAdicGenerators.length = twoAdicity + 1 := by
  decide

/-- Consecutive BabyBear two-adic generators square to the previous generator. -/
@[simp] lemma twoAdicGenerators_succ_square_eq' (idx : Fin twoAdicity) :
    twoAdicGenerators[idx.val + 1] ^ 2 = twoAdicGenerators[idx] := by
  fin_cases idx
  <;> simp [twoAdicGenerators] <;> decide

/-- Consecutive BabyBear two-adic generators square to the previous generator. -/
@[simp] lemma twoAdicGenerators_succ_square_eq (idx : Nat) (h : idx < twoAdicity) :
    haveI : idx + 1 < twoAdicGenerators.length := by simp [twoAdicGenerators_length, h]
    twoAdicGenerators[idx + 1] ^ 2 = twoAdicGenerators[idx] :=
  twoAdicGenerators_succ_square_eq' ⟨idx, h⟩

/-- `twoAdicity` is maximal: `2^(twoAdicity+1)` does not divide `fieldSize - 1`. -/
lemma twoAdicity_maximal : ¬ (2 ^ (twoAdicity + 1)) ∣ (fieldSize - 1) := by
  decide

/-- Repeated squaring: `sqChain g n = g ^ (2^n)`.
    Does `n` multiplications instead of `2^n`, making it kernel-friendly. -/
private def sqChain (g : Field) : Nat → Field
  | 0 => g
  | n + 1 => let h := sqChain g n; h * h

/-- Repeated squaring agrees with exponentiation by a power of two. -/
private theorem sqChain_eq_pow_two_pow (g : Field) (n : Nat) :
    sqChain g n = g ^ (2 ^ n) := by
  induction n with
  | zero => simp [sqChain]
  | succ n ih => simp [sqChain, ih, pow_succ, pow_mul]

/-- Repeated squaring walks backward through the precomputed two-adic generator table. -/
private theorem sqChain_twoAdicGenerators_shift (k n : Nat) (hkn : k + n ≤ twoAdicity) :
    sqChain twoAdicGenerators[(⟨k + n, by omega⟩ : Fin (twoAdicity + 1))] n =
      twoAdicGenerators[(⟨k, by omega⟩ : Fin (twoAdicity + 1))] := by
  induction n generalizing k with
  | zero =>
      simp [sqChain]
  | succ n ih =>
      calc
        sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ : Fin (twoAdicity + 1))]
            (n + 1)
          = sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ :
                Fin (twoAdicity + 1))] n *
              sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ :
                Fin (twoAdicity + 1))] n := by
              simp [sqChain]
        _ = twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] *
              twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] := by
              have hshift :
                  sqChain twoAdicGenerators[(⟨k + (n + 1), by omega⟩ :
                      Fin (twoAdicity + 1))] n =
                    twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  (ih (k := k + 1) (by omega))
              exact congrArg (fun x ↦ x * x) hshift
        _ = twoAdicGenerators[(⟨k + 1, by omega⟩ : Fin (twoAdicity + 1))] ^ 2 := by
              simp [pow_two]
        _ = twoAdicGenerators[(⟨k, by omega⟩ : Fin (twoAdicity + 1))] := by
              simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using (twoAdicGenerators_succ_square_eq k (by omega))

/-- Every nonzero index in the precomputed table is genuinely nontrivial. -/
private lemma twoAdicGenerators_ne_one_of_pos (n : Fin (twoAdicity + 1)) (hn : 0 < n) :
    twoAdicGenerators[n] ≠ (1 : Field) := by
  fin_cases n <;> simp_all [twoAdicGenerators] <;> decide

/-- The power `(twoAdicGenerators[bits])^(2^bits) = 1`. -/
lemma twoAdicGenerators_pow_twoPow_eq_one (bits : Fin (twoAdicity + 1)) :
    twoAdicGenerators[bits] ^ (2 ^ (bits : Nat)) = 1 := by
  rw [← sqChain_eq_pow_two_pow]
  rcases bits with ⟨n, hn⟩
  have hshift :
      sqChain twoAdicGenerators[(⟨n, hn⟩ : Fin (twoAdicity + 1))] n =
        twoAdicGenerators[(⟨0, by omega⟩ : Fin (twoAdicity + 1))] := by
    simpa using sqChain_twoAdicGenerators_shift 0 n (by omega)
  simpa [twoAdicGenerators] using hshift

/-- Helper: Fin-indexed version for computational verification of non-triviality. -/
private lemma twoAdicGenerators_pow_ne_one_aux (n : Fin 28) (m : Fin 28)
    (hm : m.val < n.val) :
    twoAdicGenerators[n] ^ (2 ^ m.val) ≠ (1 : Field) := by
  rw [← sqChain_eq_pow_two_pow]
  let nMinus : Fin (twoAdicity + 1) :=
    ⟨n.val - m.val, lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩
  have hshift :
      sqChain twoAdicGenerators[n] m.val = twoAdicGenerators[nMinus] := by
    have hn_le : n.val ≤ twoAdicity := by
      simpa [twoAdicity] using Nat.le_of_lt_succ n.isLt
    have hbound : (n.val - m.val) + m.val ≤ twoAdicity := by
      simpa [Nat.sub_add_cancel (Nat.le_of_lt hm)] using hn_le
    simpa [Nat.sub_add_cancel (Nat.le_of_lt hm)] using
      (sqChain_twoAdicGenerators_shift (n.val - m.val) m.val hbound)
  rw [hshift]
  exact twoAdicGenerators_ne_one_of_pos nMinus (by
    change 0 < n.val - m.val
    exact Nat.sub_pos_of_lt hm)

/-- If `m < bits`, then `(twoAdicGenerators[bits])^(2^m) ≠ 1`. -/
lemma twoAdicGenerators_pow_twoPow_ne_one_of_lt
    {bits : Fin (twoAdicity + 1)} {m : Nat} (hm : m < bits) :
    (twoAdicGenerators[bits]) ^ (2 ^ m) ≠ (1 : Field) := by
  have hm_lt : m < 28 := Nat.lt_trans hm bits.isLt
  exact twoAdicGenerators_pow_ne_one_aux bits ⟨m, hm_lt⟩ hm

/-- The precomputed element at index `bits` is a primitive `2^bits`-th root of unity. -/
lemma isPrimitiveRoot_twoAdicGenerator (n : Fin (twoAdicity + 1)) :
    IsPrimitiveRoot (twoAdicGenerators[n]) (2 ^ (n : Nat)) := by
  rw [IsPrimitiveRoot.iff_def]
  rcases n with ⟨_ | k, hb⟩
  · simp [twoAdicGenerators]
  · constructor
    · exact twoAdicGenerators_pow_twoPow_eq_one ⟨k + 1, hb⟩
    · intro m hm
      by_contra h
      have hord := orderOf_eq_prime_pow
        (twoAdicGenerators_pow_twoPow_ne_one_of_lt (bits := ⟨k + 1, hb⟩) (m := k)
          (by simp))
        (twoAdicGenerators_pow_twoPow_eq_one ⟨k + 1, hb⟩)
      have hdvd := orderOf_dvd_of_pow_eq_one hm
      rw [hord] at hdvd
      exact h hdvd

/-- As a unit, the precomputed element is a member of `rootsOfUnity (2^bits)`. -/
lemma twoAdicGenerator_unit_mem_rootsOfUnity
    (bits : Fin (twoAdicity + 1)) (h : twoAdicGenerators[bits] ≠ 0) :
    Units.mk0 (twoAdicGenerators[bits]) h ∈ rootsOfUnity (2 ^ (bits : Nat)) Field := by
  rw [mem_rootsOfUnity]
  rw [Units.ext_iff]
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
  exact twoAdicGenerators_pow_twoPow_eq_one bits

/-- The order of `twoAdicGenerators[bits]` equals `2^bits`. -/
lemma twoAdicGenerators_order (bits : Fin (twoAdicity + 1)) :
    orderOf (twoAdicGenerators[bits]) = 2 ^ (bits : Nat) := by
  rcases bits with ⟨_ | n, hb⟩
  · simp [twoAdicGenerators, orderOf_one]
  · exact orderOf_eq_prime_pow
      (twoAdicGenerators_pow_twoPow_ne_one_of_lt (bits := ⟨n + 1, hb⟩) (m := n)
        (by simp))
      (twoAdicGenerators_pow_twoPow_eq_one ⟨n + 1, hb⟩)

end BabyBear
