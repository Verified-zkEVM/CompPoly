/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Derek Sorensen, Dimitris Mitsios
-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Fold
import Mathlib.Tactic.NormNum

/-!
# Binary polynomial word arithmetic

A word's bit `i` represents the coefficient of `X^i`. Changing word width
zero-extends or truncates the coefficient vector. Carry-less multiplication
accumulates shifted words using XOR and truncates at the chosen result width.
A width at least twice the operand width preserves the full polynomial product.
The 128-bit specialization returns a 256-bit product.

Polynomial interpretation and its correspondence proofs are available through
`CompPoly.Fields.Binary.Common`.
-/

@[expose] public section

namespace BinaryField

section BitVecOperations

-- We use BitVec 256 to ensure no overflows during squaring
abbrev B128 := BitVec 128
abbrev B256 := BitVec 256

-- Extend 128 to 256
def to256 (v : B128) : B256 := BitVec.zeroExtend 256 v

lemma to256_toNat (v : B128) : (to256 v).toNat = v.toNat := by
  simp only [to256, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.reducePow,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  change BitVec.toNat v < 2^256
  have h_toNat_lt := BitVec.toNat_lt_twoPow_of_le (n := 256) (x := v) (h := by omega)
  omega

-- Std.Commutative and Std.Associative instances for Nat.xor required by Finset.fold
instance : Std.Commutative Nat.xor where
  comm := Nat.xor_comm

instance : Std.Associative Nat.xor where
  assoc := Nat.xor_assoc

-- Std.Commutative and Std.Associative instances for BitVec.xor required by Finset.fold
instance {w : Nat} : Std.Commutative (α := BitVec w) BitVec.xor where
  comm := fun a b => by
    ext i
    simp only [BitVec.xor_eq, BitVec.getElem_xor]
    rw [Bool.xor_comm]

instance {w : Nat} : Std.Associative (α := BitVec w) BitVec.xor where
  assoc := fun a b c => by
    ext i
    simp only [BitVec.xor_eq, BitVec.getElem_xor, Bool.bne_assoc]

/-- Resize a bit vector by zero extension or truncation to the target width. -/
def zeroExtendTo {v w : ℕ} (a : BitVec v) : BitVec w := BitVec.zeroExtend w a

theorem toNat_zeroExtendTo {v w : ℕ} (a : BitVec v) (h : v ≤ w) :
    (zeroExtendTo (w := w) a).toNat = a.toNat := by
  unfold zeroExtendTo
  simp [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by norm_num) h))

/-- `to256` is the 128-to-256 instance of `zeroExtendTo`. -/
theorem to256_eq_zeroExtendTo (v : B128) : to256 v = zeroExtendTo v := rfl

/-- Multiply binary polynomial coefficients using XOR and shifts, retaining the lowest `w`
bits. If `v + v ≤ w`, every coefficient of the full product is retained. -/
def carryLessMul {v w : ℕ} (a b : BitVec v) : BitVec w :=
  Fin.foldl v (fun acc i =>
    if a.getLsbD i then acc ^^^ (zeroExtendTo b <<< (i : Nat))
    else acc) (0 : BitVec w)

/-- The full carry-less product of two 128-bit polynomial coefficient vectors. -/
def clMul (a b : B128) : B256 := carryLessMul a b

theorem clMul_eq_carryLessMul (a b : B128) : clMul a b = carryLessMul (w := 256) a b := rfl

/-- Carry-less squaring of a 128-bit vector. -/
def clSq (a : B128) : B256 :=
  clMul a a

lemma fold_range_xor_eq_foldl {w : Nat} (n : Nat) (f : Nat → BitVec w) :
    (Finset.range n).fold BitVec.xor 0 f =
    Fin.foldl n (fun acc i => acc ^^^ (f i)) 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.foldl_succ_last, Finset.range_add_one, Finset.fold_insert Finset.notMem_range_self]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [←ih, BitVec.xor_comm]
    rfl

end BitVecOperations

end BinaryField
