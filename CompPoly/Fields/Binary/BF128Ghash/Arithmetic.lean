/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Dimitris Mitsios
-/
module

public import CompPoly.Fields.Binary.Common.Arithmetic
public import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.NormNum

/-!
# GHASH polynomial-basis arithmetic

The nominal carrier stores 128 polynomial coefficients, with bit `i` representing `X^i`.
Multiplication folds the full carry-less product modulo `X^128 + X^7 + X^2 + X + 1`.
Inversion uses repeated squaring and a fixed addition chain, sending zero to zero.
These operations and the explicit word maps require no irreducibility certificate.

`CompPoly.Fields.Binary.BF128Ghash.Impl` proves correspondence with the polynomial quotient
and supplies the canonical ring and field instances. The coordinates here describe
polynomial coefficients; byte and wire formats require an explicit conversion.

## References

* Dworkin, M., *Recommendation for Block Cipher Modes of Operation: Galois/Counter Mode
  (GCM) and GMAC*, NIST SP 800-38D.
  https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf
-/

@[expose] public section

namespace BF128Ghash

open BitVec BinaryField

/-- An element of `GF(2)[X] / (X^128 + X^7 + X^2 + X + 1)` in a polynomial basis. -/
structure ConcreteBF128Ghash where
  /-- Bit `i` is the coefficient of `X^i`. -/
  toBitVec : BitVec 128
  deriving DecidableEq, BEq

/-- Construct a field element from its polynomial-basis coordinates. -/
@[inline] def ofBitVec (a : BitVec 128) : ConcreteBF128Ghash := ⟨a⟩

/-- Reading the coordinates of a constructed element recovers the input word. -/
@[simp] theorem toBitVec_ofBitVec (a : BitVec 128) : (ofBitVec a).toBitVec = a := rfl

/-- Reconstructing an element from its coordinates recovers that element. -/
@[simp] theorem ofBitVec_toBitVec (a : ConcreteBF128Ghash) : ofBitVec a.toBitVec = a := rfl

/-- Polynomial-basis coordinates uniquely determine a field element. -/
theorem toBitVec_injective : Function.Injective ConcreteBF128Ghash.toBitVec := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- Elements with equal polynomial-basis coordinates are equal. -/
@[ext] theorem ConcreteBF128Ghash.ext {a b : ConcreteBF128Ghash}
    (h : a.toBitVec = b.toBitVec) : a = b := toBitVec_injective h

/-- The equivalence between field elements and their polynomial-basis coordinates. -/
def equivBitVec : ConcreteBF128Ghash ≃ BitVec 128 where
  toFun := ConcreteBF128Ghash.toBitVec
  invFun := ofBitVec
  left_inv := ofBitVec_toBitVec
  right_inv := toBitVec_ofBitVec

instance : LawfulBEq ConcreteBF128Ghash where
  eq_of_beq {a b} h := toBitVec_injective (eq_of_beq h)
  rfl {a} := by
    change (a.toBitVec == a.toBitVec) = true
    exact BEq.rfl

instance : Repr ConcreteBF128Ghash := ⟨fun a prec => reprPrec a.toBitVec prec⟩

/-- Folding Constant R = X^7 + X^2 + X + 1.
  Since P = X^128 + R, we have X^128 ≡ R (mod P). -/
def R_val : B128 := 135#128

/-- Replace the high half of a 256-bit polynomial word by its product with
`X^7 + X^2 + X + 1`, then XOR the low half into the result. -/
def fold_step (prod : B256) : B256 :=
  let h := prod.extractLsb 255 128
  let l := prod.extractLsb 127 0
  clMul h R_val ^^^ (to256 l)

/-- Reduce a 256-bit polynomial word modulo `X^128 + X^7 + X^2 + X + 1` using two
folds, then retain its low 128 bits. -/
def reduce_clMul (prod : B256) : B128 :=
  let acc := fold_step prod
  let res := fold_step acc
  res.extractLsb 127 0

section AddCommGroupInstance

instance : Zero ConcreteBF128Ghash where zero := ofBitVec 0
instance : One ConcreteBF128Ghash where one := ofBitVec 1
instance : Inhabited ConcreteBF128Ghash := ⟨0⟩
instance : Add ConcreteBF128Ghash where add a b := ofBitVec (a.toBitVec ^^^ b.toBitVec)
instance : Neg ConcreteBF128Ghash where neg a := a
instance : Sub ConcreteBF128Ghash where sub a b := ofBitVec (a.toBitVec ^^^ b.toBitVec)

/-- Zero has every polynomial-basis coefficient equal to zero. -/
@[simp] theorem toBitVec_zero : (0 : ConcreteBF128Ghash).toBitVec = 0#128 := rfl

/-- One has only its constant coefficient equal to one. -/
@[simp] theorem toBitVec_one : (1 : ConcreteBF128Ghash).toBitVec = 1#128 := rfl

/-- Addition is coefficientwise exclusive-or in the polynomial basis. -/
@[simp] theorem toBitVec_add (a b : ConcreteBF128Ghash) :
    (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- Multiply by reducing the carry-less product of the polynomial-basis words. -/
def mul (a b : ConcreteBF128Ghash) : ConcreteBF128Ghash :=
  ofBitVec (reduce_clMul (clMul a.toBitVec b.toBitVec))

instance : Mul ConcreteBF128Ghash where mul := mul

/-- The product coordinates are the reduced carry-less product of the input coordinates. -/
@[simp] theorem toBitVec_mul (a b : ConcreteBF128Ghash) :
    (a * b).toBitVec = reduce_clMul (clMul a.toBitVec b.toBitVec) := rfl

-- -----------------------------------------------------------------------------
-- 4. AddCommGroup Instance
-- -----------------------------------------------------------------------------

lemma add_assoc (a b c : ConcreteBF128Ghash) : a + b + c = a + (b + c) := by
  apply ConcreteBF128Ghash.ext
  exact BitVec.xor_assoc a.toBitVec b.toBitVec c.toBitVec

lemma add_comm (a b : ConcreteBF128Ghash) : a + b = b + a := by
  apply ConcreteBF128Ghash.ext
  exact BitVec.xor_comm a.toBitVec b.toBitVec

lemma add_zero (a : ConcreteBF128Ghash) : a + 0 = a := by
  apply ConcreteBF128Ghash.ext
  exact BitVec.xor_zero

lemma zero_add (a : ConcreteBF128Ghash) : 0 + a = a := by
  rw [add_comm]
  apply ConcreteBF128Ghash.ext
  exact BitVec.xor_zero

lemma neg_add_cancel (a : ConcreteBF128Ghash) : -a + a = 0 := by
  apply ConcreteBF128Ghash.ext
  exact BitVec.xor_self

lemma add_self_cancel (a : ConcreteBF128Ghash) : a + a = 0 := by
  apply ConcreteBF128Ghash.ext
  exact BitVec.xor_self

lemma nsmul_succ (n : ℕ) (x : ConcreteBF128Ghash) :
    (if (n + 1) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = (if n % 2 = 0 then (0 : ConcreteBF128Ghash) else x) + x := by
  have h_mod : (n + 1) % 2 = (n % 2 + 1) % 2 := Nat.add_mod n 1 2
  by_cases h : n % 2 = 0
  · rw [h, Nat.zero_add] at h_mod
    rw [h]; simp only [↓reduceIte]
    have h_mod: (n + 1) % 2 = 1 := by omega
    rw [h_mod]; simp only [one_ne_zero, ↓reduceIte]
    exact (zero_add x).symm
  · have h1 : n % 2 = 1 := by
      have := Nat.mod_two_eq_zero_or_one n
      exact Nat.mod_two_ne_zero.mp h
    rw [h1] at h_mod ⊢
    have h_mod: (n + 1) % 2 = 0 := by omega
    rw [h_mod]; simp only [↓reduceIte, one_ne_zero]
    exact (add_self_cancel x).symm

lemma zsmul_succ (n : ℕ) (x : ConcreteBF128Ghash) :
    (if (n + 1 : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = (if (n : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x) + x := by
  norm_cast
  exact nsmul_succ n x

lemma int_neg_mod_two (n : ℤ) : (-n) % 2 = n % 2 := by
  simp only [Int.neg_emod_two]

lemma zsmul_neg (n : ℕ) (x : ConcreteBF128Ghash) :
    (if (Int.negSucc n) % 2 = 0 then (0 : ConcreteBF128Ghash) else x)
    = -(if (n + 1 : ℤ) % 2 = 0 then (0 : ConcreteBF128Ghash) else x) := by
  have h_neg : Int.negSucc n = - (n + 1 : ℤ) := rfl
  rw [h_neg]
  rw [int_neg_mod_two (n + 1)]
  rfl

/-- In characteristic 2, `n • x = x` if `n` is odd, and `n • x = 0` if `n` is even.
This is because `2 • x = x + x = 0` in any ring of characteristic 2. -/
instance : AddCommGroup ConcreteBF128Ghash where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  zero_add := zero_add
  neg_add_cancel := neg_add_cancel
  nsmul := fun n x => if n % 2 = 0 then 0 else x
  zsmul := fun n x => if n % 2 = 0 then 0 else x
  nsmul_zero := fun x => by
    rfl
  nsmul_succ := nsmul_succ
  zsmul_zero' := fun x => by
    rfl
  zsmul_succ' := zsmul_succ
  zsmul_neg' := zsmul_neg

end AddCommGroupInstance

-- Natural number casting: even numbers → 0, odd numbers → 1
def natCast (n : ℕ) : ConcreteBF128Ghash := if n % 2 = 0 then 0 else 1

instance : NatCast ConcreteBF128Ghash where
  natCast := natCast

@[simp] lemma natCast_eq (n : ℕ) : (↑n : ConcreteBF128Ghash) = natCast n := rfl

lemma natCast_zero : natCast 0 = 0 := by simp [natCast]

lemma natCast_succ (n : ℕ) : natCast (n + 1) = natCast n + 1 := by
  simp [natCast]
  by_cases h : n % 2 = 0
  · -- If n is even, then n+1 is odd
    have h_succ : (n + 1) % 2 = 1 := by omega
    simp [h, h_succ]
  · -- If n is odd, then n+1 is even
    have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [h, h_succ]; norm_num;
    rw [add_self_cancel]

-- Integer casting: same as natural casting (mod 2)
def intCast (n : ℤ) : ConcreteBF128Ghash := if n % 2 = 0 then 0 else 1

instance : IntCast ConcreteBF128Ghash where
  intCast := intCast

lemma intCast_ofNat (n : ℕ) : intCast (n : ℤ) = natCast n := by
  have h : ((n : ℤ) % 2 = 0) ↔ n % 2 = 0 := by omega
  simp only [intCast, natCast, h]

lemma intCast_negSucc (n : ℕ) : intCast (Int.negSucc n) = -(↑(n + 1) : ConcreteBF128Ghash) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · have h_neg : ( - (n + 1 : ℤ)) % 2 = 0 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ, h_neg]
    have h_nat : (↑(n + 1) : ConcreteBF128Ghash) = (0 : ConcreteBF128Ghash) := by
      simp only [natCast_eq, natCast, h_mod]; rfl
    rw [h_nat]; rfl
  · have h_neg : ( - (n + 1 : ℤ)) % 2 = 1 := by omega
    unfold intCast
    have int_neg_succ : Int.negSucc n = - (n + 1 : ℤ) := by rfl
    rw [int_neg_succ, h_neg, if_neg (by simp)]
    have h_nat : (↑(n + 1) : ConcreteBF128Ghash) = (1 : ConcreteBF128Ghash) := by
      simp only [natCast_eq, natCast, h_mod]; rfl
    rw [h_nat]; rfl

/-- Squaring in GF(2^128). -/
def square (a : ConcreteBF128Ghash) : ConcreteBF128Ghash := a * a

/-- Computes a^(2^k) by repeated squaring. -/
def powTwoPow (a : ConcreteBF128Ghash) (k : Nat) : ConcreteBF128Ghash :=
  match k with
  | 0 => a
  | n + 1 => powTwoPow (square a) n

/-- Invert using repeated squaring and a fixed addition chain for 127.
Zero maps to zero; a nonzero element `a` maps to `a^(2^128 - 2)`. -/
def invItohTsujii (a : ConcreteBF128Ghash) : ConcreteBF128Ghash :=
  if a.toBitVec.toNat = 0 then 0 else
    -- Addition chain for 127:
    -- 1 -> 2 -> 3 -> 6 -> 7 -> 14 -> 15 -> 30 -> 31 -> 62 -> 63 -> 126 -> 127
    let u1 := a                         -- 2^1 - 1
    let u2 := (powTwoPow u1 1) * u1        -- 2^2 - 1
    let u3 := (powTwoPow u2 1) * u1        -- 2^3 - 1
    let u6 := (powTwoPow u3 3) * u3        -- 2^6 - 1
    let u7 := (powTwoPow u6 1) * u1        -- 2^7 - 1
    let u14 := (powTwoPow u7 7) * u7       -- 2^14 - 1
    let u15 := (powTwoPow u14 1) * u1      -- 2^15 - 1
    let u30 := (powTwoPow u15 15) * u15    -- 2^30 - 1
    let u31 := (powTwoPow u30 1) * u1      -- 2^31 - 1
    let u62 := (powTwoPow u31 31) * u31    -- 2^62 - 1
    let u63 := (powTwoPow u62 1) * u1      -- 2^63 - 1
    let u126 := (powTwoPow u63 63) * u63   -- 2^126 - 1
    let u127 := (powTwoPow u126 1) * u1    -- 2^127 - 1
    square u127                         -- 2^128 - 2

instance : Inv ConcreteBF128Ghash where
  inv a := invItohTsujii a

lemma inv_zero : (0 : ConcreteBF128Ghash)⁻¹ = 0 := by
  simp [Inv.inv]
  unfold invItohTsujii
  simp

instance instDivConcreteBF128Ghash : Div (ConcreteBF128Ghash) where
  div a b := a * (Inv.inv b)

/-- Compatibility name for division inherited from the homogeneous division instance. -/
@[deprecated "Use the inferred homogeneous division instance." (since := "2026-09-16")]
abbrev instHDivConcreteBF128Ghash :
    HDiv ConcreteBF128Ghash ConcreteBF128Ghash ConcreteBF128Ghash := inferInstance

lemma div_eq_mul_inv (a b : ConcreteBF128Ghash) : a / b = a * b⁻¹ := by rfl

end BF128Ghash
