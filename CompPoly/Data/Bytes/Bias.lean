/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Bytes.CanonicalNat
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Count
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bias of the reduce-modulo-order decoder

A challenge squeezed from a byte sponge is `CanonicalNat.ofBytesModOrder`: `n` bytes read as a
little-endian integer and reduced modulo `bound`. Reducing the `256 ^ n` strings modulo `bound`
hits every residue `256 ^ n / bound` or `256 ^ n / bound + 1` times, so the induced distribution
on `F` is within `bound / 256 ^ n` of uniform in total variation. Sixteen bytes beyond the
field's width make that below `2 ^ -128`, which is the margin spongefish uses.

* `Bytes.equivFin`: `n`-byte strings are the naturals below `256 ^ n`.
* `CanonicalNat.card_fiber_ofBytesModOrder`: the exact fiber count, from Mathlib's
  `Nat.count_modEq_card`.
* `CanonicalNat.tv_ofBytesModOrder_le`: the total-variation bound, over `ℚ`.

Everything here is counting; no probability theory is imported. ArkLib's
`Deserialize.CloseToUniform` instance for `ZMod p` is derived from the last theorem by casting
into its `PMF` distance.
-/

@[expose] public section

namespace CompPoly

namespace Bytes

/-- Little-endian byte strings of length `n` are the naturals below `256 ^ n`. -/
def equivFin (n : ℕ) : Vector UInt8 n ≃ Fin (256 ^ n) where
  toFun v := ⟨ofVecLE v, ofVecLE_lt v⟩
  invFun m := toVecLE n m.1
  left_inv v := toVecLE_ofVecLE v
  right_inv m := Fin.ext (ofVecLE_toVecLE_of_lt m.2)

/-- `n`-byte strings are finite, through `equivFin`. -/
instance instFintypeVectorUInt8 (n : ℕ) : Fintype (Vector UInt8 n) :=
  Fintype.ofEquiv _ (equivFin n).symm

theorem card_vector_uint8 (n : ℕ) : Fintype.card (Vector UInt8 n) = 256 ^ n := by
  rw [Fintype.card_congr (equivFin n), Fintype.card_fin]

end Bytes

namespace CanonicalNat

open Bytes

variable {F : Type*} [CanonicalNat F]

theorem ofNat_eq_iff {m : ℕ} {x : F} : ofNat m = x ↔ m % bound F = toNat x := by
  constructor
  · intro h
    rw [← h, toNat_ofNat]
  · intro h
    rw [← ofNat_mod, h, ofNat_toNat]

/-- The `n`-byte strings decoding to `x` modulo the order, as the naturals below `256 ^ n`
congruent to `toNat x`. -/
def fiberEquiv (n : ℕ) (x : F) :
    {v : Vector UInt8 n // ofBytesModOrder v = x}
      ≃ {k : ℕ // k < 256 ^ n ∧ k ≡ toNat x [MOD bound F]} where
  toFun v := ⟨ofVecLE v.1, ofVecLE_lt v.1, by
    have h := ofNat_eq_iff.mp v.2
    unfold Nat.ModEq
    rw [h, Nat.mod_eq_of_lt (toNat_lt x)]⟩
  invFun k := ⟨toVecLE n k.1, by
    obtain ⟨k, hk, hmod⟩ := k
    have h : k % bound F = toNat x := by
      have := hmod
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (toNat_lt x)] at this
    show ofNat (ofVecLE (toVecLE n k)) = x
    rw [ofVecLE_toVecLE_of_lt hk]
    exact ofNat_eq_iff.mpr h⟩
  left_inv v := Subtype.ext (toVecLE_ofVecLE v.1)
  right_inv k := Subtype.ext (ofVecLE_toVecLE_of_lt k.2.1)

instance instFintypeFiber [DecidableEq F] (n : ℕ) (x : F) :
    Fintype {v : Vector UInt8 n // ofBytesModOrder v = x} :=
  Subtype.fintype _

variable [DecidableEq F]

/-- Exactly how many `n`-byte strings decode to `x` modulo the order: the quotient
`256 ^ n / bound`, plus one for the residues below the remainder. -/
theorem card_fiber_ofBytesModOrder (n : ℕ) (x : F) :
    Fintype.card {v : Vector UInt8 n // ofBytesModOrder v = x}
      = 256 ^ n / bound F + if toNat x < 256 ^ n % bound F then 1 else 0 := by
  open scoped Count in
  rw [Fintype.card_congr (fiberEquiv n x), ← Nat.count_eq_card_fintype,
    Nat.count_modEq_card _ bound_pos, Nat.mod_eq_of_lt (toNat_lt x)]

/-- Every fiber is within one of the ideal `256 ^ n / bound`, so each residue's probability is
within `1 / 256 ^ n` of uniform. -/
theorem abs_card_fiber_div_sub_le (n : ℕ) (x : F) :
    |((Fintype.card {v : Vector UInt8 n // ofBytesModOrder v = x} : ℚ) / 256 ^ n)
      - 1 / bound F| ≤ 1 / 256 ^ n := by
  rw [card_fiber_ofBytesModOrder]
  have hN : (0 : ℚ) < 256 ^ n := by positivity
  have hp : (0 : ℚ) < bound F := by exact_mod_cast bound_pos (F := F)
  have hdiv : (256 ^ n : ℕ) = bound F * (256 ^ n / bound F) + 256 ^ n % bound F :=
    (Nat.div_add_mod _ _).symm
  have hrem : 256 ^ n % bound F < bound F := Nat.mod_lt _ bound_pos
  -- The fiber count `c` satisfies `|c * bound - 256 ^ n| ≤ bound`.
  have habs : |((256 ^ n / bound F + if toNat x < 256 ^ n % bound F then 1 else 0 : ℕ) : ℚ)
      * bound F - 256 ^ n| ≤ bound F := by
    have hdiv' : ((256 ^ n : ℕ) : ℚ)
        = bound F * (256 ^ n / bound F : ℕ) + (256 ^ n % bound F : ℕ) := by
      exact_mod_cast hdiv
    have hrem' : ((256 ^ n % bound F : ℕ) : ℚ) < bound F := by exact_mod_cast hrem
    have hnn : (0 : ℚ) ≤ (256 ^ n % bound F : ℕ) := by positivity
    rw [abs_le]
    split_ifs with hlt
    · push_cast at hdiv' ⊢
      constructor <;> nlinarith
    · push_cast at hdiv' ⊢
      constructor <;> nlinarith
  rw [div_sub_div _ _ hN.ne' hp.ne', mul_one, abs_div, abs_of_pos (mul_pos hN hp)]
  calc |((256 ^ n / bound F + if toNat x < 256 ^ n % bound F then 1 else 0 : ℕ) : ℚ)
        * bound F - 256 ^ n| / (256 ^ n * bound F)
      ≤ bound F / (256 ^ n * bound F) :=
        div_le_div_of_nonneg_right habs (le_of_lt (mul_pos hN hp))
    _ = 1 / 256 ^ n := by
        field_simp

/-- The total-variation distance of `ofBytesModOrder` on `n` bytes from the uniform
distribution on `F` is at most `bound / 256 ^ n`: sixteen bytes beyond the width give
`2 ^ -128`. Stated over `ℚ`; ArkLib derives its `PMF` form from it. -/
theorem tv_ofBytesModOrder_le [Fintype F] (n : ℕ) :
    ∑ x : F, |((Fintype.card {v : Vector UInt8 n // ofBytesModOrder v = x} : ℚ) / 256 ^ n)
      - 1 / bound F| ≤ bound F / 256 ^ n := by
  calc ∑ x : F, |((Fintype.card {v : Vector UInt8 n // ofBytesModOrder v = x} : ℚ) / 256 ^ n)
        - 1 / bound F|
      ≤ ∑ _x : F, (1 / 256 ^ n : ℚ) := Finset.sum_le_sum fun x _ => abs_card_fiber_div_sub_le n x
    _ = Fintype.card F * (1 / 256 ^ n) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = bound F / 256 ^ n := by rw [card_eq, mul_one_div]

end CanonicalNat

end CompPoly
