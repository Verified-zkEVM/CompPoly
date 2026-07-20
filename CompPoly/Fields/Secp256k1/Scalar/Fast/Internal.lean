/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Secp256k1.Scalar.Basic

/-!
  # Internal definitions for fast secp256k1 scalar arithmetic

  Low-level constants, the 4-limb representation, and raw limb helpers.
-/

namespace Secp256k1.Scalar.Fast

/-- secp256k1 scalar order, limb 0. -/
@[inline] def N_0 : UInt64 := 0xBFD25E8CD0364141

/-- secp256k1 scalar order, limb 1. -/
@[inline] def N_1 : UInt64 := 0xBAAEDCE6AF48A03B

/-- secp256k1 scalar order, limb 2. -/
@[inline] def N_2 : UInt64 := 0xFFFFFFFFFFFFFFFE

/-- secp256k1 scalar order, limb 3. -/
@[inline] def N_3 : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Limb 0 of `2^256 - n`. -/
@[inline] def N_C_0 : UInt64 := 0x402DA1732FC9BEBF

/-- Limb 1 of `2^256 - n`. -/
@[inline] def N_C_1 : UInt64 := 0x4551231950B75FC4

/-- Limb 2 of `2^256 - n`. -/
@[inline] def N_C_2 : UInt64 := 0x0000000000000001

/-- Radix weight of the second 64-bit limb. -/
@[inline] def TWO64 : Nat := 0x10000000000000000

/-- Radix weight of the third 64-bit limb. -/
@[inline] def TWO128 : Nat := 0x100000000000000000000000000000000

/-- Radix weight of the fourth 64-bit limb. -/
@[inline] def TWO192 : Nat := 0x1000000000000000000000000000000000000000000000000

/-- Raw 4×64-bit secp256k1 scalar representation, little-endian. -/
structure Repr where
  d0 : UInt64
  d1 : UInt64
  d2 : UInt64
  d3 : UInt64
deriving BEq, Inhabited, DecidableEq

/-- Four little-endian 64-bit limbs. Used as the raw 256-bit kernel interface. -/
abbrev Limbs4 := UInt64 × UInt64 × UInt64 × UInt64

/-- Four little-endian limbs and a carry or borrow word. -/
abbrev Limbs4Carry := UInt64 × UInt64 × UInt64 × UInt64 × UInt64

/-- Eight little-endian 64-bit limbs. Used for raw 512-bit products. -/
abbrev Limbs8 := UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64

/-- Three accumulator words used by libsecp256k1's scalar multiplication macros. -/
abbrev AccLimbs := UInt64 × UInt64 × UInt64

namespace Repr

/-- Zero as raw limbs. -/
@[inline] def zero : Repr := ⟨0, 0, 0, 0⟩

/-- One as raw limbs. -/
@[inline] def one : Repr := ⟨1, 0, 0, 0⟩

/-- The scalar modulus as raw limbs. This is not canonical as a field element. -/
@[inline] def modulus : Repr := ⟨N_0, N_1, N_2, N_3⟩

/-- Construct raw limbs. -/
@[inline] def ofLimbs (d0 d1 d2 d3 : UInt64) : Repr := ⟨d0, d1, d2, d3⟩

/-- Convert raw little-endian limbs to a natural number. -/
@[inline] def toNat (x : Repr) : Nat :=
  x.d0.toNat + x.d1.toNat * TWO64 + x.d2.toNat * TWO128 + x.d3.toNat * TWO192

/-- The four-limb natural interpretation uniquely determines a representation. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  have ha0 := a.d0.toNat_lt_size
  have ha1 := a.d1.toNat_lt_size
  have ha2 := a.d2.toNat_lt_size
  have ha3 := a.d3.toNat_lt_size
  have hb0 := b.d0.toNat_lt_size
  have hb1 := b.d1.toNat_lt_size
  have hb2 := b.d2.toNat_lt_size
  have hb3 := b.d3.toNat_lt_size
  norm_num [UInt64.size] at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  unfold toNat TWO64 TWO128 TWO192 at h
  have h0 : a.d0.toNat = b.d0.toNat := by omega
  have h1 : a.d1.toNat = b.d1.toNat := by omega
  have h2 : a.d2.toNat = b.d2.toNat := by omega
  have h3 : a.d3.toNat = b.d3.toNat := by omega
  cases a
  cases b
  simp only [mk.injEq]
  exact ⟨UInt64.toNat.inj h0, UInt64.toNat.inj h1,
    UInt64.toNat.inj h2, UInt64.toNat.inj h3⟩

/-- Reference raw constructor: reduce a natural number modulo the scalar order. -/
def ofNat (n : Nat) : Repr :=
  let r := n % Secp256k1.Scalar.Basic.CARD
  let d0 := (r % TWO64).toUInt64
  let r := r / TWO64
  let d1 := (r % TWO64).toUInt64
  let r := r / TWO64
  let d2 := (r % TWO64).toUInt64
  let r := r / TWO64
  let d3 := (r % TWO64).toUInt64
  ⟨d0, d1, d2, d3⟩

/-- Reconstructing `ofNat`'s four limbs yields the input reduced modulo the scalar order. -/
@[simp] theorem toNat_ofNat (n : Nat) :
    (ofNat n).toNat = n % Secp256k1.Scalar.Basic.CARD := by
  unfold ofNat toNat TWO64 TWO128 TWO192
  simp
  have hCard : 0 < Secp256k1.Scalar.Basic.CARD := by
    norm_num [Secp256k1.Scalar.Basic.CARD]
  have hr : n % Secp256k1.Scalar.Basic.CARD < 2 ^ 256 := by
    apply Nat.lt_trans (Nat.mod_lt n hCard)
    norm_num [Secp256k1.Scalar.Basic.CARD]
  have hq : n % Secp256k1.Scalar.Basic.CARD / 18446744073709551616 /
      18446744073709551616 / 18446744073709551616 / 18446744073709551616 = 0 := by
    omega
  have h0 := Nat.mod_add_div (n % Secp256k1.Scalar.Basic.CARD) 18446744073709551616
  have h1 := Nat.mod_add_div (n % Secp256k1.Scalar.Basic.CARD / 18446744073709551616)
    18446744073709551616
  have h2 := Nat.mod_add_div
    (n % Secp256k1.Scalar.Basic.CARD / 18446744073709551616 / 18446744073709551616)
    18446744073709551616
  have h3 := Nat.mod_add_div
    (n % Secp256k1.Scalar.Basic.CARD / 18446744073709551616 / 18446744073709551616 /
      18446744073709551616)
    18446744073709551616
  omega

/-- `ofNat` always produces a canonical scalar representative. -/
theorem ofNat_lt (n : Nat) :
    (ofNat n).toNat < Secp256k1.Scalar.Basic.CARD := by
  rw [toNat_ofNat]
  exact Nat.mod_lt _ (by norm_num [Secp256k1.Scalar.Basic.CARD])

/-- `ofNat` represents the input natural number in the canonical scalar field. -/
theorem ofNat_cast (n : Nat) :
    ((ofNat n).toNat : Secp256k1.Scalar.Basic.Field) =
      (n : Secp256k1.Scalar.Basic.Field) := by
  rw [toNat_ofNat]
  simp

/-- Reducing the natural interpretation of a canonical representation is identity. -/
theorem ofNat_toNat (x : Repr) (hx : x.toNat < Secp256k1.Scalar.Basic.CARD) :
    ofNat x.toNat = x := by
  apply toNat_injective
  rw [toNat_ofNat, Nat.mod_eq_of_lt hx]

/-- The raw zero representation is canonical. -/
theorem zero_lt : zero.toNat < Secp256k1.Scalar.Basic.CARD := by
  change 0 < Secp256k1.Scalar.Basic.CARD
  norm_num [Secp256k1.Scalar.Basic.CARD]

/-- The raw one representation is canonical. -/
theorem one_lt : one.toNat < Secp256k1.Scalar.Basic.CARD := by
  change 1 < Secp256k1.Scalar.Basic.CARD
  norm_num [Secp256k1.Scalar.Basic.CARD]

/-- Every four-limb representation denotes a number below `2^256`. -/
theorem toNat_lt_two256 (x : Repr) : x.toNat < 2 ^ 256 := by
  have h0 := x.d0.toNat_lt_size
  have h1 := x.d1.toNat_lt_size
  have h2 := x.d2.toNat_lt_size
  have h3 := x.d3.toNat_lt_size
  norm_num [UInt64.size] at h0 h1 h2 h3
  unfold toNat TWO64 TWO128 TWO192
  norm_num
  omega

/-- The raw modulus limbs reconstruct the secp256k1 scalar order. -/
@[simp] theorem modulus_toNat : modulus.toNat = Secp256k1.Scalar.Basic.CARD := by
  norm_num [modulus, toNat, N_0, N_1, N_2, N_3, TWO64, TWO128, TWO192,
    UInt64.toNat_ofNat,
    Secp256k1.Scalar.Basic.CARD]

/-- The complement limbs reconstruct `2^256` minus the scalar order. -/
theorem complement_toNat :
    (ofLimbs N_C_0 N_C_1 N_C_2 0).toNat =
      2 ^ 256 - Secp256k1.Scalar.Basic.CARD := by
  norm_num [ofLimbs, toNat, N_C_0, N_C_1, N_C_2, TWO64, TWO128, TWO192,
    UInt64.toNat_ofNat,
    Secp256k1.Scalar.Basic.CARD]

/-- True iff all limbs are zero. -/
@[inline] def isZero (x : Repr) : Bool :=
  (x.d0 ||| x.d1 ||| x.d2 ||| x.d3) == 0

/-- True iff this scalar is one. -/
@[inline] def isOne (x : Repr) : Bool :=
  ((x.d0 ^^^ 1) ||| x.d1 ||| x.d2 ||| x.d3) == 0

/-- True iff this scalar is even. -/
@[inline] def isEven (x : Repr) : Bool :=
  x.d0 &&& 1 == 0

/-- `x >= n`, matching libsecp256k1's scalar overflow check. -/
@[inline] def checkOverflow (x : Repr) : Bool :=
  if x.d3 < N_3 then false
  else if x.d2 < N_2 then false
  else if x.d2 > N_2 then true
  else if x.d1 < N_1 then false
  else if x.d1 > N_1 then true
  else x.d0 >= N_0

end Repr

/-- `d0..d3 >= n`, matching libsecp256k1's scalar overflow check. -/
@[inline] def checkOverflowRaw (d0 d1 d2 d3 : UInt64) : Bool :=
  if d3 < N_3 then false
  else if d2 < N_2 then false
  else if d2 > N_2 then true
  else if d1 < N_1 then false
  else if d1 > N_1 then true
  else d0 >= N_0

/-- The limbwise overflow check is equivalent to comparison with the scalar order. -/
theorem checkOverflowRaw_eq_decide (d0 d1 d2 d3 : UInt64) :
    checkOverflowRaw d0 d1 d2 d3 =
      decide ((Repr.ofLimbs d0 d1 d2 d3).toNat >= Secp256k1.Scalar.Basic.CARD) := by
  unfold checkOverflowRaw Repr.toNat Repr.ofLimbs N_0 N_1 N_2 N_3 TWO64 TWO128 TWO192
  have h0 := d0.toNat_lt_size
  have h1 := d1.toNat_lt_size
  have h2 := d2.toNat_lt_size
  have h3 := d3.toNat_lt_size
  norm_num [UInt64.size] at h0 h1 h2 h3
  simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le]
  simp only [UInt64.toNat_ofNat]
  split <;> rename_i h3cmp
  · norm_num [Secp256k1.Scalar.Basic.CARD] at *
    omega
  · split <;> rename_i h2lo
    · norm_num [Secp256k1.Scalar.Basic.CARD] at *
      omega
    · split <;> rename_i h2hi
      · norm_num [Secp256k1.Scalar.Basic.CARD] at *
        omega
      · split <;> rename_i h1lo
        · norm_num [Secp256k1.Scalar.Basic.CARD] at *
          omega
        · split <;> rename_i h1hi
          · norm_num [Secp256k1.Scalar.Basic.CARD] at *
            omega
          · norm_num [Secp256k1.Scalar.Basic.CARD] at *
            omega

/-- True iff all four raw limbs are zero. -/
@[inline] def isZeroRaw (d0 d1 d2 d3 : UInt64) : Bool :=
  (d0 ||| d1 ||| d2 ||| d3) == 0


/-- Add two limbs plus an incoming carry bit. -/
@[inline] def addCarry (x y carry : UInt64) : UInt64 × UInt64 :=
  let y' := y + carry
  let c0 : UInt64 := if y' < y then 1 else 0
  let s := x + y'
  let c1 : UInt64 := if s < x then 1 else 0
  (s, c0 + c1)

/-- Exact value equation for one wrapped 64-bit addition and its overflow flag. -/
private theorem addWord_value (a b : UInt64) :
    (a + b).toNat + 2 ^ 64 * (if a + b < a then 1 else 0) = a.toNat + b.toNat := by
  have ha := a.toNat_lt_size
  have hb := b.toNat_lt_size
  norm_num [UInt64.size] at ha hb
  have hmod := Nat.mod_add_div (a.toNat + b.toNat) (2 ^ 64)
  by_cases h : a + b < a
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h'
    rw [if_pos h, UInt64.toNat_add]
    omega
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h'
    rw [if_neg h, UInt64.toNat_add]
    omega

/-- Addition value equation with overflow compared against the right operand. -/
private theorem addWordRight_value (a b : UInt64) :
    (a + b).toNat + 2 ^ 64 * (if a + b < b then 1 else 0) = a.toNat + b.toNat := by
  have hab : a + b = b + a := by
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_add, Nat.add_comm]
  rw [hab]
  simpa only [Nat.add_comm] using addWord_value b a

/-- Addition value equation with its overflow flag stored as a machine word. -/
private theorem addWordRightCarry_value (a b : UInt64) :
    let carry : UInt64 := if a + b < b then 1 else 0
    (a + b).toNat + 2 ^ 64 * carry.toNat = a.toNat + b.toNat := by
  by_cases h : a + b < b
  · simpa [h] using addWordRight_value a b
  · simpa [h] using addWordRight_value a b

/-- Exact value equation for one wrapped 64-bit subtraction and its borrow flag. -/
private theorem subWord_value (a b : UInt64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (if a < b then 1 else 0) := by
  have ha := a.toNat_lt_size
  have hb := b.toNat_lt_size
  norm_num [UInt64.size] at ha hb
  have hmod := Nat.mod_add_div (2 ^ 64 - b.toNat + a.toNat) (2 ^ 64)
  by_cases h : a < b
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt] at h'
    rw [if_pos h, UInt64.toNat_sub]
    omega
  · have h' := h
    rw [UInt64.lt_iff_toNat_lt] at h'
    rw [if_neg h, UInt64.toNat_sub]
    omega

/-- The value equation for `addCarry`. -/
theorem addCarry_value (x y carry : UInt64) (_hcarry : carry.toNat ≤ 1) :
    let r := addCarry x y carry
    r.1.toNat + TWO64 * r.2.toNat = x.toNat + y.toNat + carry.toNat := by
  let y' := y + carry
  let c0 : UInt64 := if y' < y then 1 else 0
  let s := x + y'
  let c1 : UInt64 := if s < x then 1 else 0
  change s.toNat + TWO64 * (c0 + c1).toNat = x.toNat + y.toNat + carry.toNat
  have hc0val : c0.toNat = if y' < y then 1 else 0 := by
    simp only [c0]
    split <;> rfl
  have hc1val : c1.toNat = if s < x then 1 else 0 := by
    simp only [c1]
    split <;> rfl
  have hy : y'.toNat + TWO64 * c0.toNat = y.toNat + carry.toNat := by
    rw [hc0val]
    simpa [y', TWO64] using addWord_value y carry
  have hs : s.toNat + TWO64 * c1.toNat = x.toNat + y'.toNat := by
    rw [hc1val]
    simpa [s, TWO64] using addWord_value x y'
  have hc0 : c0.toNat ≤ 1 := by
    rw [hc0val]
    split <;> norm_num
  have hc1 : c1.toNat ≤ 1 := by
    rw [hc1val]
    split <;> norm_num
  have hsum : c0.toNat + c1.toNat < TWO64 := by
    unfold TWO64
    omega
  have hcarrySum : (c0 + c1).toNat = c0.toNat + c1.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hsum
  rw [hcarrySum]
  unfold TWO64 at hy hs ⊢
  omega

/-- The outgoing word from `addCarry` is a bit. -/
theorem addCarry_carry_le_one (x y carry : UInt64) (hcarry : carry.toNat ≤ 1) :
    (addCarry x y carry).2.toNat ≤ 1 := by
  have hx := x.toNat_lt_size
  have hy := y.toNat_lt_size
  norm_num [UInt64.size] at hx hy
  have hvalue := addCarry_value x y carry hcarry
  unfold TWO64 at hvalue
  omega

/-- `addCarry` represents exact addition split into a low word and one carry bit. -/
theorem addCarry_spec (x y carry : UInt64) (hcarry : carry.toNat ≤ 1) :
    let r := addCarry x y carry
    r.1.toNat + TWO64 * r.2.toNat = x.toNat + y.toNat + carry.toNat ∧
      r.2.toNat ≤ 1 := by
  exact ⟨addCarry_value x y carry hcarry, addCarry_carry_le_one x y carry hcarry⟩

/-- Subtract two limbs plus an incoming borrow bit. -/
@[inline] def subBorrow (x y borrow : UInt64) : UInt64 × UInt64 :=
  let y' := y + borrow
  let b0 : UInt64 := if y' < y then 1 else 0
  let s := x - y'
  let b1 : UInt64 := if x < y' then 1 else 0
  (s, b0 + b1)

/-- The value equation for `subBorrow`. -/
theorem subBorrow_value (x y borrow : UInt64) (_hborrow : borrow.toNat ≤ 1) :
    let r := subBorrow x y borrow
    r.1.toNat + y.toNat + borrow.toNat = x.toNat + TWO64 * r.2.toNat := by
  let y' := y + borrow
  let b0 : UInt64 := if y' < y then 1 else 0
  let s := x - y'
  let b1 : UInt64 := if x < y' then 1 else 0
  change s.toNat + y.toNat + borrow.toNat = x.toNat + TWO64 * (b0 + b1).toNat
  have hb0val : b0.toNat = if y' < y then 1 else 0 := by
    simp only [b0]
    split <;> rfl
  have hb1val : b1.toNat = if x < y' then 1 else 0 := by
    simp only [b1]
    split <;> rfl
  have hy : y'.toNat + TWO64 * b0.toNat = y.toNat + borrow.toNat := by
    rw [hb0val]
    simpa [y', TWO64] using addWord_value y borrow
  have hs : s.toNat + y'.toNat = x.toNat + TWO64 * b1.toNat := by
    rw [hb1val]
    simpa [s, TWO64] using subWord_value x y'
  have hb0 : b0.toNat ≤ 1 := by
    rw [hb0val]
    split <;> norm_num
  have hb1 : b1.toNat ≤ 1 := by
    rw [hb1val]
    split <;> norm_num
  have hsum : b0.toNat + b1.toNat < TWO64 := by
    unfold TWO64
    omega
  have hborrowSum : (b0 + b1).toNat = b0.toNat + b1.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt hsum
  rw [hborrowSum]
  unfold TWO64 at hy hs ⊢
  omega

/-- The outgoing word from `subBorrow` is a bit. -/
theorem subBorrow_borrow_le_one (x y borrow : UInt64) (hborrow : borrow.toNat ≤ 1) :
    (subBorrow x y borrow).2.toNat ≤ 1 := by
  have hs := (subBorrow x y borrow).1.toNat_lt_size
  have hy := y.toNat_lt_size
  have hx := x.toNat_lt_size
  norm_num [UInt64.size] at hs hy hx
  have hvalue := subBorrow_value x y borrow hborrow
  unfold TWO64 at hvalue
  omega

/-- `subBorrow` represents exact subtraction with one outgoing borrow bit. -/
theorem subBorrow_spec (x y borrow : UInt64) (hborrow : borrow.toNat ≤ 1) :
    let r := subBorrow x y borrow
    r.1.toNat + y.toNat + borrow.toNat = x.toNat + TWO64 * r.2.toNat ∧
      r.2.toNat ≤ 1 := by
  exact ⟨subBorrow_value x y borrow hborrow,
    subBorrow_borrow_le_one x y borrow hborrow⟩

/-- Append one radix-`2^64` limb to an exact addition identity. -/
private theorem appendAddValue
    (p c a lo c' x y w : Nat)
    (hp : p + w * c = a)
    (h : lo + 18446744073709551616 * c' = x + y + c) :
    p + w * lo + (w * 18446744073709551616) * c' = a + w * (x + y) := by
  have hpz : (p : Int) + w * c = a := by exact_mod_cast hp
  have hz : (lo : Int) + 18446744073709551616 * c' = x + y + c := by
    exact_mod_cast h
  apply Nat.cast_injective (R := Int)
  push_cast
  calc
    (p : Int) + w * lo + w * 18446744073709551616 * c' =
        p + w * (lo + 18446744073709551616 * c') := by ring
    _ = p + w * (x + y + c) := by rw [hz]
    _ = (p + w * c) + w * (x + y) := by ring
    _ = a + w * (x + y) := by rw [hpz]

/-- Append one radix-`2^64` limb to an exact subtraction identity. -/
private theorem appendSubValue
    (r b a borrow lo y x nextBorrow w : Nat)
    (hp : r + b = a + w * borrow)
    (h : lo + y + borrow = x + 18446744073709551616 * nextBorrow) :
    r + w * lo + (b + w * y) =
      a + w * x + (w * 18446744073709551616) * nextBorrow := by
  have hpz : (r : Int) + b = a + w * borrow := by exact_mod_cast hp
  have hz : (lo : Int) + y + borrow = x + 18446744073709551616 * nextBorrow := by
    exact_mod_cast h
  apply Nat.cast_injective (R := Int)
  push_cast
  calc
    (r : Int) + w * lo + (b + w * y) =
        (r + b) + w * (lo + y) := by ring
    _ = (a + w * borrow) + w * (lo + y) := by rw [hpz]
    _ = a + w * (lo + y + borrow) := by ring
    _ = a + w * (x + 18446744073709551616 * nextBorrow) := by rw [hz]
    _ = a + w * x + w * 18446744073709551616 * nextBorrow := by ring

/-- Low 64 bits of a 64×64 product. -/
@[inline] def mul64Lo (a b : UInt64) : UInt64 :=
  a * b

/-- High 64 bits of a 64×64 product using four 32×32-bit products.

    Every intermediate operation fits in `UInt64`. Together with `mul64Lo`,
    this is the pure-Lean counterpart of libsecp256k1's 128-bit multiply.
-/
@[inline] def mul64Hi (a b : UInt64) : UInt64 :=
  let mask : UInt64 := 0xffffffff
  let a0 := a &&& mask
  let a1 := a >>> 32
  let b0 := b &&& mask
  let b1 := b >>> 32
  let w0 := a0 * b0
  let t := a1 * b0 + (w0 >>> 32)
  let w1 := t &&& mask
  let w2 := t >>> 32
  let w1 := w1 + a0 * b1
  a1 * b1 + w2 + (w1 >>> 32)

/-- Split a word into its low and high 32-bit halves. -/
private theorem split32 (x : UInt64) :
    x.toNat = (x &&& 0xffffffff).toNat + 2 ^ 32 * (x >>> 32).toNat := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_ofNat]
  norm_num [Nat.shiftRight_eq_div_pow]
  rw [show 4294967295 = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_add_div x.toNat (2 ^ 32)).symm

/-- Natural value of the low 32-bit half of a word. -/
private theorem low32_value (x : UInt64) :
    (x &&& 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and]
  simp only [UInt64.toNat_ofNat]
  norm_num
  rw [show 4294967295 = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

/-- Natural value of the high 32-bit half of a word. -/
private theorem high32_value (x : UInt64) :
    (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_ofNat]
  norm_num [Nat.shiftRight_eq_div_pow]

/-- The low and high words reconstruct the exact 64x64-bit product. -/
theorem mul64_value (a b : UInt64) :
    (mul64Lo a b).toNat + 2 ^ 64 * (mul64Hi a b).toNat = a.toNat * b.toNat := by
  let mask : UInt64 := 0xffffffff
  let a0 := a &&& mask
  let a1 := a >>> 32
  let b0 := b &&& mask
  let b1 := b >>> 32
  let w0 := a0 * b0
  let t := a1 * b0 + (w0 >>> 32)
  let w1 := t &&& mask
  let w2 := t >>> 32
  let w1' := w1 + a0 * b1
  change (a * b).toNat + 2 ^ 64 * (a1 * b1 + w2 + (w1' >>> 32)).toNat = _
  have ha := split32 a
  have hb := split32 b
  change a.toNat = a0.toNat + 2 ^ 32 * a1.toNat at ha
  change b.toNat = b0.toNat + 2 ^ 32 * b1.toNat at hb
  have ha0 : a0.toNat < 2 ^ 32 := by
    change (a &&& 0xffffffff).toNat < _
    rw [low32_value]
    exact Nat.mod_lt _ (by norm_num)
  have hb0 : b0.toNat < 2 ^ 32 := by
    change (b &&& 0xffffffff).toNat < _
    rw [low32_value]
    exact Nat.mod_lt _ (by norm_num)
  have ha1 : a1.toNat < 2 ^ 32 := by
    change (a >>> 32).toNat < _
    rw [high32_value]
    have h := a.toNat_lt_size
    norm_num [UInt64.size] at h ⊢
    omega
  have hb1 : b1.toNat < 2 ^ 32 := by
    change (b >>> 32).toNat < _
    rw [high32_value]
    have h := b.toNat_lt_size
    norm_num [UInt64.size] at h ⊢
    omega
  have hw0lt : a0.toNat * b0.toNat < 2 ^ 64 := by nlinarith
  have hw0 : w0.toNat = a0.toNat * b0.toNat := by
    change (a0 * b0).toNat = _
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hw0lt]
  have hw0hi : (w0 >>> 32).toNat = w0.toNat / 2 ^ 32 := high32_value w0
  have hw0lo : (w0 &&& mask).toNat = w0.toNat % 2 ^ 32 := by
    simpa [mask] using low32_value w0
  have htlt : a1.toNat * b0.toNat + (w0 >>> 32).toNat < 2 ^ 64 := by
    have hw0hibound : (w0 >>> 32).toNat < 2 ^ 32 := by
      rw [hw0hi]
      omega
    nlinarith
  have ht : t.toNat = a1.toNat * b0.toNat + (w0 >>> 32).toNat := by
    change (a1 * b0 + (w0 >>> 32)).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    have hp : a1.toNat * b0.toNat < 2 ^ 64 := by nlinarith
    rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt htlt]
  have hw1 : w1.toNat = t.toNat % 2 ^ 32 := by
    change (t &&& 0xffffffff).toNat = _
    exact low32_value t
  have hw2 : w2.toNat = t.toNat / 2 ^ 32 := by
    change (t >>> 32).toNat = _
    exact high32_value t
  have hw1lt : w1.toNat < 2 ^ 32 := by
    rw [hw1]
    exact Nat.mod_lt _ (by norm_num)
  have hw1'lt : w1.toNat + a0.toNat * b1.toNat < 2 ^ 64 := by nlinarith
  have hw1' : w1'.toNat = w1.toNat + a0.toNat * b1.toNat := by
    change (w1 + a0 * b1).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    have hp : a0.toNat * b1.toNat < 2 ^ 64 := by nlinarith
    rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hw1'lt]
  have hw1'hi : (w1' >>> 32).toNat = w1'.toNat / 2 ^ 32 := high32_value w1'
  have hw1'lo : (w1' &&& mask).toNat = w1'.toNat % 2 ^ 32 := by
    simpa [mask] using low32_value w1'
  have hw2lt : w2.toNat < 2 ^ 32 := by
    rw [hw2]
    omega
  have hw1'hilt : (w1' >>> 32).toNat < 2 ^ 32 := by
    rw [hw1'hi]
    omega
  have hhi1lt : a1.toNat * b1.toNat + w2.toNat < 2 ^ 64 := by nlinarith
  have hhi2lt : a1.toNat * b1.toNat + w2.toNat + (w1' >>> 32).toNat < 2 ^ 64 := by
    nlinarith
  have hhi : (a1 * b1 + w2 + (w1' >>> 32)).toNat =
      a1.toNat * b1.toNat + w2.toNat + (w1' >>> 32).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
    have hp : a1.toNat * b1.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hhi1lt,
      Nat.mod_eq_of_lt hhi2lt]
  have htSplit := Nat.mod_add_div t.toNat (2 ^ 32)
  have hw1Split := Nat.mod_add_div w1'.toNat (2 ^ 32)
  have hw0Split := Nat.mod_add_div w0.toNat (2 ^ 32)
  rw [← hw1, ← hw2] at htSplit
  rw [← hw1'lo, ← hw1'hi] at hw1Split
  rw [← hw0lo, ← hw0hi] at hw0Split
  let rem := (w0 &&& mask).toNat + 2 ^ 32 * (w1' &&& mask).toNat
  have hremLt : rem < 2 ^ 64 := by
    have h0lt : (w0 &&& mask).toNat < 2 ^ 32 := by
      rw [hw0lo]
      exact Nat.mod_lt _ (by norm_num)
    have h1lt : (w1' &&& mask).toNat < 2 ^ 32 := by
      rw [hw1'lo]
      exact Nat.mod_lt _ (by norm_num)
    dsimp [rem]
    omega
  have hproduct : a.toNat * b.toNat = rem + 2 ^ 64 *
      (a1.toNat * b1.toNat + w2.toNat + (w1' >>> 32).toNat) := by
    apply Nat.cast_injective (R := Int)
    push_cast
    have haz : (a.toNat : Int) = a0.toNat + 2 ^ 32 * a1.toNat := by exact_mod_cast ha
    have hbz : (b.toNat : Int) = b0.toNat + 2 ^ 32 * b1.toNat := by exact_mod_cast hb
    have hw0z : (w0.toNat : Int) = a0.toNat * b0.toNat := by exact_mod_cast hw0
    have htz : (t.toNat : Int) = a1.toNat * b0.toNat + (w0 >>> 32).toNat := by
      exact_mod_cast ht
    have hw1'z : (w1'.toNat : Int) = w1.toNat + a0.toNat * b1.toNat := by
      exact_mod_cast hw1'
    have hw0Splitz : ((w0 &&& mask).toNat : Int) + 2 ^ 32 * (w0 >>> 32).toNat =
        w0.toNat := by exact_mod_cast hw0Split
    have htSplitz : (w1.toNat : Int) + 2 ^ 32 * w2.toNat = t.toNat := by
      exact_mod_cast htSplit
    have hw1Splitz : ((w1' &&& mask).toNat : Int) +
        2 ^ 32 * (w1' >>> 32).toNat = w1'.toNat := by exact_mod_cast hw1Split
    have htCombined : ((w0 >>> 32).toNat : Int) + a1.toNat * b0.toNat =
        w1.toNat + 4294967296 * w2.toNat := by omega
    have hw1Combined : (w1.toNat : Int) + a0.toNat * b1.toNat =
        (w1' &&& mask).toNat + 4294967296 * (w1' >>> 32).toNat := by omega
    dsimp [rem]
    calc
      (a.toNat : Int) * b.toNat =
          (a0.toNat + 2 ^ 32 * a1.toNat) * (b0.toNat + 2 ^ 32 * b1.toNat) := by
            rw [haz, hbz]
      _ = a0.toNat * b0.toNat + 2 ^ 32 *
            (a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
            2 ^ 64 * (a1.toNat * b1.toNat) := by ring
      _ = (w0 &&& mask).toNat + 2 ^ 32 * (w0 >>> 32).toNat + 2 ^ 32 *
            (a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
            2 ^ 64 * (a1.toNat * b1.toNat) := by
              rw [← hw0z, ← hw0Splitz]
      _ = (w0 &&& mask).toNat + 2 ^ 32 *
            ((w0 >>> 32).toNat + a1.toNat * b0.toNat + a0.toNat * b1.toNat) +
            2 ^ 64 * (a1.toNat * b1.toNat) := by ring
      _ = (w0 &&& mask).toNat + 2 ^ 32 *
            (w1.toNat + 2 ^ 32 * w2.toNat + a0.toNat * b1.toNat) +
            2 ^ 64 * (a1.toNat * b1.toNat) := by
              rw [htCombined]
              norm_num
      _ = (w0 &&& mask).toNat + 2 ^ 32 *
            (w1.toNat + a0.toNat * b1.toNat + 2 ^ 32 * w2.toNat) +
            2 ^ 64 * (a1.toNat * b1.toNat) := by ring
      _ = (w0 &&& mask).toNat + 2 ^ 32 *
            ((w1' &&& mask).toNat + 2 ^ 32 * (w1' >>> 32).toNat +
              2 ^ 32 * w2.toNat) + 2 ^ 64 * (a1.toNat * b1.toNat) := by
                rw [hw1Combined]
                norm_num
      _ = (w0 &&& mask).toNat + 2 ^ 32 * (w1' &&& mask).toNat +
            2 ^ 64 * (a1.toNat * b1.toNat + w2.toNat + (w1' >>> 32).toNat) := by ring
  have hlo : (a * b).toNat = rem := by
    rw [UInt64.toNat_mul, hproduct]
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp only [Nat.add_zero, Nat.mod_eq_of_lt hremLt]
  rw [hlo, hhi, ← hproduct]


/-- C macro `muladd`: add `a*b` to `(c0,c1,c2)`. -/
@[inline] def mulAdd (c0 c1 c2 a b : UInt64) : AccLimbs :=
  let tl := mul64Lo a b
  let th := mul64Hi a b
  let c0' := c0 + tl
  let th := th + if c0' < tl then 1 else 0
  let c1' := c1 + th
  let c2' := c2 + if c1' < th then 1 else 0
  (c0', c1', c2')

/-- C macro `muladd_fast`: add `a*b` to `(c0,c1)`, preserving `c2 = 0`. -/
@[inline] def mulAddFast (c0 c1 c2 a b : UInt64) : AccLimbs :=
  let tl := mul64Lo a b
  let th := mul64Hi a b
  let c0' := c0 + tl
  let th := th + if c0' < tl then 1 else 0
  let c1' := c1 + th
  (c0', c1', c2)

/-- C macro `sumadd`: add a word to `(c0,c1,c2)`. -/
@[inline] def sumAdd (c0 c1 c2 a : UInt64) : AccLimbs :=
  let c0' := c0 + a
  let over : UInt64 := if c0' < a then 1 else 0
  let c1' := c1 + over
  let c2' := c2 + if c1' < over then 1 else 0
  (c0', c1', c2')

/-- C macro `sumadd_fast`: add a word to `(c0,c1)`, preserving `c2 = 0`. -/
@[inline] def sumAddFast (c0 c1 c2 a : UInt64) : AccLimbs :=
  let c0' := c0 + a
  let c1' := c1 + if c0' < a then 1 else 0
  (c0', c1', c2)

/-- C macro `extract`: output `c0` and shift `(c0,c1,c2)` down one limb. -/
@[inline] def extract (c0 c1 c2 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (c0, c1, c2, 0)

/-- C macro `extract_fast`: output `c0` and shift `(c0,c1)` down one limb. -/
@[inline] def extractFast (c0 c1 _c2 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (c0, c1, 0, 0)

/-- Natural-number value of libsecp256k1's three-word multiplication accumulator. -/
def accToNat (c0 c1 c2 : UInt64) : Nat :=
  c0.toNat + 2 ^ 64 * c1.toNat + 2 ^ 128 * c2.toNat

/-- A two-word accumulator is strictly smaller than `2^128`. -/
theorem accToNat_lt_two128 (c0 c1 : UInt64) : accToNat c0 c1 0 < 2 ^ 128 := by
  have h0 := c0.toNat_lt_size
  have h1 := c1.toNat_lt_size
  norm_num [UInt64.size, accToNat] at h0 h1 ⊢
  omega

/-- A one-word accumulator is strictly smaller than `2^64`. -/
theorem accToNat_lt_two64 (c0 : UInt64) : accToNat c0 0 0 < 2 ^ 64 := by
  have h0 := c0.toNat_lt_size
  norm_num [UInt64.size, accToNat] at h0 ⊢
  exact h0

/-- A product of two machine words is strictly smaller than `2^128`. -/
theorem wordProduct_lt_two128 (a b : UInt64) : a.toNat * b.toNat < 2 ^ 128 := by
  have ha := a.toNat_lt_size
  have hb := b.toNat_lt_size
  norm_num [UInt64.size] at ha hb ⊢
  nlinarith

/-- `extract` emits the low word and shifts the accumulator down by one word. -/
theorem extract_value (c0 c1 c2 : UInt64) :
    let r := extract c0 c1 c2
    r.1.toNat + 2 ^ 64 * accToNat r.2.1 r.2.2.1 r.2.2.2 =
      accToNat c0 c1 c2 := by
  simp [extract, accToNat]
  ring

/-- `extractFast` emits the low word and shifts a two-word accumulator down. -/
theorem extractFast_value (c0 c1 c2 : UInt64) (hc2 : c2 = 0) :
    let r := extractFast c0 c1 c2
    r.1.toNat + 2 ^ 64 * accToNat r.2.1 r.2.2.1 r.2.2.2 =
      accToNat c0 c1 c2 := by
  subst c2
  simp [extractFast, accToNat]

/-- `mulAdd` adds one full 64x64-bit product to the three-word accumulator.
    The bound is the C macro's no-overflow invariant. -/
theorem mulAdd_value (c0 c1 c2 a b : UInt64)
    (hbound : accToNat c0 c1 c2 + a.toNat * b.toNat < 2 ^ 192) :
    let r := mulAdd c0 c1 c2 a b
    accToNat r.1 r.2.1 r.2.2 = accToNat c0 c1 c2 + a.toNat * b.toNat := by
  let tl := mul64Lo a b
  let th0 := mul64Hi a b
  let c0' := c0 + tl
  let carry0 : UInt64 := if c0' < tl then 1 else 0
  let th := th0 + carry0
  let c1' := c1 + th
  let carry1 : UInt64 := if c1' < th then 1 else 0
  let c2' := c2 + carry1
  change accToNat c0' c1' c2' = _
  have hp := mul64_value a b
  change tl.toNat + 2 ^ 64 * th0.toNat = a.toNat * b.toNat at hp
  have h0raw := addWord_value tl c0
  have h0 : c0'.toNat + 2 ^ 64 * carry0.toNat = tl.toNat + c0.toNat := by
    simpa [carry0, c0', add_comm] using addWordRightCarry_value c0 tl
  have hcarry0 : carry0.toNat ≤ 1 := by
    by_cases h : c0' < tl <;> simp [carry0, h]
  have ha := a.toNat_lt_size
  have hb := b.toNat_lt_size
  have htl := tl.toNat_lt_size
  have hth0 := th0.toNat_lt_size
  have hc0 := c0.toNat_lt_size
  have hc1 := c1.toNat_lt_size
  have hc2 := c2.toNat_lt_size
  norm_num [UInt64.size] at ha hb htl hth0 hc0 hc1 hc2
  have hprodMax : a.toNat * b.toNat ≤
      340282366920938463426481119284349108225 := by nlinarith
  have hth : th0.toNat + carry0.toNat < 2 ^ 64 := by
    norm_num at hp hprodMax ⊢
    omega
  have hthNat : th.toNat = th0.toNat + carry0.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hth]
  have h1raw := addWord_value th c1
  have h1 : c1'.toNat + 2 ^ 64 * carry1.toNat = th.toNat + c1.toNat := by
    simpa [carry1, c1', add_comm] using addWordRightCarry_value c1 th
  have hcarry1 : carry1.toNat ≤ 1 := by
    by_cases h : c1' < th <;> simp [carry1, h]
  have hc2sum : c2.toNat + carry1.toNat < 2 ^ 64 := by
    unfold accToNat at hbound
    norm_num at hbound hp h0 h1 hthNat ⊢
    omega
  have hc2Nat : c2'.toNat = c2.toNat + carry1.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hc2sum]
  unfold accToNat
  norm_num at hp h0 h1 hthNat hc2Nat ⊢
  omega

/-- `mulAddFast` adds a product to a two-word accumulator.
    Its preconditions are the `c2 = 0` and no-carry assertions of the C macro. -/
theorem mulAddFast_value (c0 c1 c2 a b : UInt64) (hc2zero : c2 = 0)
    (hbound : accToNat c0 c1 c2 + a.toNat * b.toNat < 2 ^ 128) :
    let r := mulAddFast c0 c1 c2 a b
    accToNat r.1 r.2.1 r.2.2 = accToNat c0 c1 c2 + a.toNat * b.toNat := by
  subst c2
  let tl := mul64Lo a b
  let th0 := mul64Hi a b
  let c0' := c0 + tl
  let carry0 : UInt64 := if c0' < tl then 1 else 0
  let th := th0 + carry0
  let c1' := c1 + th
  change accToNat c0' c1' 0 = _
  have hp := mul64_value a b
  change tl.toNat + 2 ^ 64 * th0.toNat = a.toNat * b.toNat at hp
  have h0raw := addWord_value tl c0
  have h0 : c0'.toNat + 2 ^ 64 * carry0.toNat = tl.toNat + c0.toNat := by
    simpa [carry0, c0', add_comm] using addWordRightCarry_value c0 tl
  have hcarry0 : carry0.toNat ≤ 1 := by
    by_cases h : c0' < tl <;> simp [carry0, h]
  have ha := a.toNat_lt_size
  have hb := b.toNat_lt_size
  have hth0 := th0.toNat_lt_size
  norm_num [UInt64.size] at ha hb hth0
  have hprodMax : a.toNat * b.toNat ≤
      340282366920938463426481119284349108225 := by nlinarith
  have hth : th0.toNat + carry0.toNat < 2 ^ 64 := by
    norm_num at hp hprodMax ⊢
    omega
  have hthNat : th.toNat = th0.toNat + carry0.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hth]
  have hc1sum : c1.toNat + th.toNat < 2 ^ 64 := by
    unfold accToNat at hbound
    norm_num at hbound hp h0 hthNat ⊢
    omega
  have hc1Nat : c1'.toNat = c1.toNat + th.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hc1sum]
  unfold accToNat
  norm_num at hp h0 hthNat hc1Nat ⊢
  omega

/-- `sumAdd` adds one word to the three-word accumulator.
    The bound is the C macro's no-overflow invariant. -/
theorem sumAdd_value (c0 c1 c2 a : UInt64)
    (hbound : accToNat c0 c1 c2 + a.toNat < 2 ^ 192) :
    let r := sumAdd c0 c1 c2 a
    accToNat r.1 r.2.1 r.2.2 = accToNat c0 c1 c2 + a.toNat := by
  let c0' := c0 + a
  let carry0 : UInt64 := if c0' < a then 1 else 0
  let c1' := c1 + carry0
  let carry1 : UInt64 := if c1' < carry0 then 1 else 0
  let c2' := c2 + carry1
  change accToNat c0' c1' c2' = _
  have h0raw := addWord_value a c0
  have h0 : c0'.toNat + 2 ^ 64 * carry0.toNat = a.toNat + c0.toNat := by
    simpa [carry0, c0', add_comm] using addWordRightCarry_value c0 a
  have h1raw := addWord_value carry0 c1
  have h1 : c1'.toNat + 2 ^ 64 * carry1.toNat = carry0.toNat + c1.toNat := by
    simpa [carry1, c1', add_comm] using addWordRightCarry_value c1 carry0
  have hcarry1 : carry1.toNat ≤ 1 := by
    by_cases h : c1' < carry0 <;> simp [carry1, h]
  have hc2sum : c2.toNat + carry1.toNat < 2 ^ 64 := by
    unfold accToNat at hbound
    norm_num at hbound h0 h1 ⊢
    omega
  have hc2Nat : c2'.toNat = c2.toNat + carry1.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hc2sum]
  unfold accToNat
  norm_num at h0 h1 hc2Nat ⊢
  omega

/-- `sumAddFast` adds one word to a two-word accumulator.
    Its preconditions are the `c2 = 0` and no-carry assertions of the C macro. -/
theorem sumAddFast_value (c0 c1 c2 a : UInt64) (hc2zero : c2 = 0)
    (hbound : accToNat c0 c1 c2 + a.toNat < 2 ^ 128) :
    let r := sumAddFast c0 c1 c2 a
    accToNat r.1 r.2.1 r.2.2 = accToNat c0 c1 c2 + a.toNat := by
  subst c2
  let c0' := c0 + a
  let carry0 : UInt64 := if c0' < a then 1 else 0
  let c1' := c1 + carry0
  change accToNat c0' c1' 0 = _
  have h0raw := addWord_value a c0
  have h0 : c0'.toNat + 2 ^ 64 * carry0.toNat = a.toNat + c0.toNat := by
    simpa [carry0, c0', add_comm] using addWordRightCarry_value c0 a
  have hc1sum : c1.toNat + carry0.toNat < 2 ^ 64 := by
    unfold accToNat at hbound
    norm_num at hbound h0 ⊢
    omega
  have hc1Nat : c1'.toNat = c1.toNat + carry0.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt hc1sum]
  unfold accToNat
  norm_num at h0 hc1Nat ⊢
  omega

/-- Raw 256-bit limb addition. Returns four result limbs and a carry. -/
@[inline] def addRaw (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Limbs4Carry :=
  let (d0, c) := addCarry a0 b0 0
  let (d1, c) := addCarry a1 b1 c
  let (d2, c) := addCarry a2 b2 c
  let (d3, c) := addCarry a3 b3 c
  (d0, d1, d2, d3, c)

/-- Raw 256-bit limb subtraction. Returns four result limbs and a borrow. -/
@[inline] def subRaw (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) : Limbs4Carry :=
  let (d0, c) := subBorrow a0 b0 0
  let (d1, c) := subBorrow a1 b1 c
  let (d2, c) := subBorrow a2 b2 c
  let (d3, c) := subBorrow a3 b3 c
  (d0, d1, d2, d3, c)

/-- Exact natural-number value of four-limb addition and its carry word. -/
theorem addRaw_value (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    let r := addRaw a0 a1 a2 a3 b0 b1 b2 b3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat +
        2 ^ 256 * r.2.2.2.2.toNat =
      (Repr.ofLimbs a0 a1 a2 a3).toNat + (Repr.ofLimbs b0 b1 b2 b3).toNat := by
  let r0 := addCarry a0 b0 0
  let r1 := addCarry a1 b1 r0.2
  let r2 := addCarry a2 b2 r1.2
  let r3 := addCarry a3 b3 r2.2
  change (Repr.ofLimbs r0.1 r1.1 r2.1 r3.1).toNat + 2 ^ 256 * r3.2.toNat = _
  have h0 := addCarry_value a0 b0 0 (by norm_num)
  have hc0 := addCarry_carry_le_one a0 b0 0 (by norm_num)
  have h1 := addCarry_value a1 b1 r0.2 hc0
  have hc1 := addCarry_carry_le_one a1 b1 r0.2 hc0
  have h2 := addCarry_value a2 b2 r1.2 hc1
  have hc2 := addCarry_carry_le_one a2 b2 r1.2 hc1
  have h3 := addCarry_value a3 b3 r2.2 hc2
  unfold TWO64 at h0 h1 h2 h3
  have h01 := appendAddValue r0.1.toNat r0.2.toNat
    (a0.toNat + b0.toNat) r1.1.toNat r1.2.toNat a1.toNat b1.toNat
    18446744073709551616 (by simpa using h0) h1
  have h012 := appendAddValue
    (r0.1.toNat + 18446744073709551616 * r1.1.toNat) r1.2.toNat
    (a0.toNat + b0.toNat + 18446744073709551616 * (a1.toNat + b1.toNat))
    r2.1.toNat r2.2.toNat a2.toNat b2.toNat
    340282366920938463463374607431768211456 (by omega) h2
  have h0123 := appendAddValue
    (r0.1.toNat + 18446744073709551616 * r1.1.toNat +
      340282366920938463463374607431768211456 * r2.1.toNat) r2.2.toNat
    (a0.toNat + b0.toNat + 18446744073709551616 * (a1.toNat + b1.toNat) +
      340282366920938463463374607431768211456 * (a2.toNat + b2.toNat))
    r3.1.toNat r3.2.toNat a3.toNat b3.toNat
    6277101735386680763835789423207666416102355444464034512896 (by omega) h3
  unfold Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192 at *
  norm_num at *
  omega

/-- The final carry returned by four-limb addition is a bit. -/
theorem addRaw_carry_le_one (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    (addRaw a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.toNat ≤ 1 := by
  let r0 := addCarry a0 b0 0
  let r1 := addCarry a1 b1 r0.2
  let r2 := addCarry a2 b2 r1.2
  have hc0 := addCarry_carry_le_one a0 b0 0 (by norm_num)
  have hc1 := addCarry_carry_le_one a1 b1 r0.2 hc0
  have hc2 := addCarry_carry_le_one a2 b2 r1.2 hc1
  exact addCarry_carry_le_one a3 b3 r2.2 hc2

/-- Exact natural-number value of four-limb subtraction and its borrow word. -/
theorem subRaw_value (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    let r := subRaw a0 a1 a2 a3 b0 b1 b2 b3
    (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2.1).toNat +
        (Repr.ofLimbs b0 b1 b2 b3).toNat =
      (Repr.ofLimbs a0 a1 a2 a3).toNat + 2 ^ 256 * r.2.2.2.2.toNat := by
  let r0 := subBorrow a0 b0 0
  let r1 := subBorrow a1 b1 r0.2
  let r2 := subBorrow a2 b2 r1.2
  let r3 := subBorrow a3 b3 r2.2
  change (Repr.ofLimbs r0.1 r1.1 r2.1 r3.1).toNat +
      (Repr.ofLimbs b0 b1 b2 b3).toNat =
    (Repr.ofLimbs a0 a1 a2 a3).toNat + 2 ^ 256 * r3.2.toNat
  have h0 := subBorrow_value a0 b0 0 (by norm_num)
  have hc0 := subBorrow_borrow_le_one a0 b0 0 (by norm_num)
  have h1 := subBorrow_value a1 b1 r0.2 hc0
  have hc1 := subBorrow_borrow_le_one a1 b1 r0.2 hc0
  have h2 := subBorrow_value a2 b2 r1.2 hc1
  have hc2 := subBorrow_borrow_le_one a2 b2 r1.2 hc1
  have h3 := subBorrow_value a3 b3 r2.2 hc2
  unfold TWO64 at h0 h1 h2 h3
  have h01 := appendSubValue r0.1.toNat b0.toNat a0.toNat r0.2.toNat
    r1.1.toNat b1.toNat a1.toNat r1.2.toNat 18446744073709551616
    (by simpa using h0) h1
  have h012 := appendSubValue
    (r0.1.toNat + 18446744073709551616 * r1.1.toNat)
    (b0.toNat + 18446744073709551616 * b1.toNat)
    (a0.toNat + 18446744073709551616 * a1.toNat) r1.2.toNat
    r2.1.toNat b2.toNat a2.toNat r2.2.toNat
    340282366920938463463374607431768211456 (by omega) h2
  have h0123 := appendSubValue
    (r0.1.toNat + 18446744073709551616 * r1.1.toNat +
      340282366920938463463374607431768211456 * r2.1.toNat)
    (b0.toNat + 18446744073709551616 * b1.toNat +
      340282366920938463463374607431768211456 * b2.toNat)
    (a0.toNat + 18446744073709551616 * a1.toNat +
      340282366920938463463374607431768211456 * a2.toNat) r2.2.toNat
    r3.1.toNat b3.toNat a3.toNat r3.2.toNat
    6277101735386680763835789423207666416102355444464034512896 (by omega) h3
  unfold Repr.toNat Repr.ofLimbs TWO64 TWO128 TWO192 at *
  norm_num at *
  omega

/-- The final borrow returned by four-limb subtraction is a bit. -/
theorem subRaw_borrow_le_one (a0 a1 a2 a3 b0 b1 b2 b3 : UInt64) :
    (subRaw a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.toNat ≤ 1 := by
  let r0 := subBorrow a0 b0 0
  let r1 := subBorrow a1 b1 r0.2
  let r2 := subBorrow a2 b2 r1.2
  have hc0 := subBorrow_borrow_le_one a0 b0 0 (by norm_num)
  have hc1 := subBorrow_borrow_le_one a1 b1 r0.2 hc0
  have hc2 := subBorrow_borrow_le_one a2 b2 r1.2 hc1
  exact subBorrow_borrow_le_one a3 b3 r2.2 hc2

end Secp256k1.Scalar.Fast
