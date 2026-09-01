/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin, Georgios Raikos
-/
module

public import CompPoly.Fields.Basic
public import CompPoly.Fields.Montgomery.Native32
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.Linarith

/-!
# Fast 32-bit Montgomery Fields

The bounded carrier, conversions, arithmetic, and field instances built on `Native32` reduction.
-/

@[expose] public section

namespace Montgomery
namespace Native32

/-- Per-field data for a fast 32-bit Montgomery field. -/
class Mont32Field (modulus : ℕ) where
  /-- `modulus` is prime. -/
  prime : modulus.Prime
  /-- `modulus` as a 32-bit word. -/
  modulus32 : UInt32
  /-- `modulus` as a 64-bit word. -/
  modulus64 : UInt64
  /-- `2^32 mod modulus`, the Montgomery representation of one. -/
  rModModulus : UInt32
  /-- `(2^32)^2 mod modulus`, used to enter Montgomery form. -/
  r2ModModulus : UInt64
  /-- `-modulus⁻¹ mod 2^32`, used by Montgomery reduction. -/
  montgomeryNegInv : UInt32
  modulus32_toNat : modulus32.toNat = modulus := by decide
  modulus64_toNat : modulus64.toNat = modulus := by decide
  two_lt_modulus : 2 < modulus := by decide
  modulus_lt_two_pow_31 : modulus < 2 ^ 31 := by decide
  rModModulus_toNat : rModModulus.toNat = 2 ^ 32 % modulus := by decide
  r2ModModulus_toNat : r2ModModulus.toNat = (2 ^ 32) ^ 2 % modulus := by decide
  montgomeryNegInv_mul_modulus_mod_two_pow_32 :
    (montgomeryNegInv.toNat * modulus) % 2 ^ 32 = 2 ^ 32 - 1 := by decide

attribute [simp] Mont32Field.modulus32_toNat Mont32Field.modulus64_toNat
  Mont32Field.rModModulus_toNat Mont32Field.r2ModModulus_toNat
  Mont32Field.modulus_lt_two_pow_31

attribute [-simp] Nat.reducePow

/-- The fast carrier for a prime modulus: a native word below `modulus`,
interpreted as a Montgomery residue. At runtime this erases to `UInt32`. -/
@[implicit_reducible]
def FastField (modulus : ℕ) [Mont32Field modulus] : Type :=
  { x : UInt32 // x.toNat < modulus }

section
variable {modulus : ℕ} [P : Mont32Field modulus]

instance : DecidableEq (FastField modulus) :=
  inferInstanceAs (DecidableEq { x : UInt32 // x.toNat < modulus })

namespace Mont32Field

instance : Fact (Nat.Prime modulus) := ⟨P.prime⟩

@[simp]
theorem modulus_pos : 0 < modulus := Nat.zero_lt_of_lt P.two_lt_modulus

@[simp] theorem modulus32_pos : 0 < P.modulus32.toNat := by simp
@[simp] theorem modulus64_pos : 0 < P.modulus64.toNat := by simp
@[simp] theorem modulus32_lt_two_pow_31 : P.modulus32.toNat < 2 ^ 31 := by simp
@[simp] theorem modulus64_lt_two_pow_31 : P.modulus64.toNat < 2 ^ 31 := by simp

@[simp] theorem modulus_lt_two_pow_32 : modulus < 2 ^ 32 := by
  linarith [P.modulus_lt_two_pow_31]

theorem modulus_sq_lt_two_pow_64 : modulus ^ 2 < 2 ^ 64 := by
  nlinarith [P.modulus_lt_two_pow_32]

theorem two_ne_zero : (2 : ZMod modulus) ≠ 0 := by
  intro h
  have hdvd : modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 modulus).mp h
  exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)

theorem two_pow_32_ne_zero : ((2 ^ 32 : ℕ) : ZMod modulus) ≠ 0 := by
  simp [two_ne_zero]

theorem r2ModModulus_lt_modulus : (2 ^ 32) ^ 2 % modulus < modulus := by
  exact Nat.mod_lt _ P.modulus_pos

end Mont32Field

instance : NeZero modulus := ⟨P.modulus_pos.ne'⟩

/-! ## Implementation -/

/-- Montgomery reduction for inputs known to be below `p * 2^32`. -/
@[inline]
def reduce (x : UInt64) (h : x.toNat < modulus * 2 ^ 32) : FastField modulus :=
  .mk (reduceRaw P.modulus32 P.modulus64 P.montgomeryNegInv x) <| by
    nth_rw 4 [← P.modulus32_toNat]
    apply reduceRaw_lt <;> simp_all

namespace FastField

/-! ### Conversions -/

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : ℕ) (h : n < modulus) : FastField modulus :=
  reduce (UInt64.ofNat n * P.r2ModModulus) <| by
    simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', P.r2ModModulus_toNat,
      Nat.mod_mul_mod]
    apply Nat.mod_lt_of_lt
    have hr : (2 ^ 32) ^ 2 % modulus < modulus := Nat.mod_lt _ P.modulus_pos
    have h1 : n * ((2 ^ 32) ^ 2 % modulus) < modulus * modulus :=
      Nat.mul_lt_mul_of_lt_of_lt h hr
    have h2 : modulus * modulus < modulus * 2 ^ 32 :=
      (Nat.mul_lt_mul_left P.modulus_pos).mpr P.modulus_lt_two_pow_32
    exact lt_trans h1 h2

/-- Convert a natural number into fast Montgomery representation. -/
@[inline]
def ofNat (modulus : ℕ) [P : Mont32Field modulus] (n : ℕ) : FastField modulus :=
  ofCanonicalNat (n % modulus) (Nat.mod_lt _ P.modulus_pos)

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (modulus : ℕ) [P : Mont32Field modulus] (x : UInt32) : FastField modulus :=
  reduce (x.toUInt64 * P.r2ModModulus) <| by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64, P.r2ModModulus_toNat]
    apply Nat.mod_lt_of_lt
    have hr : (2 ^ 32) ^ 2 % modulus < modulus := Nat.mod_lt _ P.modulus_pos
    have hx : x.toNat < 2 ^ 32 := UInt32.toNat_lt x
    have h1 : x.toNat * ((2 ^ 32) ^ 2 % modulus) < 2 ^ 32 * modulus :=
      Nat.mul_lt_mul_of_lt_of_lt hx hr
    rwa [mul_comm modulus]

/-- Convert from the canonical `ZMod` field into fast Montgomery form. -/
@[inline]
def ofField (x : ZMod modulus) : FastField modulus :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery representation. -/
@[inline]
def ofInt (modulus : ℕ) [P : Mont32Field modulus] (n : Int) : FastField modulus :=
  ofField (n : ZMod modulus)

/-- Convert a fast element to its canonical native-word representative. -/
@[inline]
def toUInt32 (x : FastField modulus) : UInt32 := Subtype.val <|
  reduce (modulus := modulus) x.val.toUInt64 <| by
    rw [UInt32.toNat_toUInt64]
    nlinarith [x.property, P.modulus_pos]

/-- Convert a fast element to its canonical natural representative. -/
@[inline]
def toNat (x : FastField modulus) : ℕ := x.toUInt32.toNat

/-- Convert a fast element to the canonical `ZMod` field. -/
@[inline]
def toField (x : FastField modulus) : ZMod modulus := (x.toNat : ZMod modulus)
end FastField

open FastField

/-! ### Field operations -/

/-- The zero fast element. -/
def zero (modulus : ℕ) [P : Mont32Field modulus] : FastField modulus := .mk 0 <| by simp

/-- The one fast element. -/
def one (modulus : ℕ) [P : Mont32Field modulus] : FastField modulus := .mk P.rModModulus <| by
  simp [Nat.mod_lt _ P.modulus_pos]

/-- Fast modular addition in Montgomery form. -/
@[inline]
def add (x y : FastField modulus) : FastField modulus :=
  .mk (conditionalSubtract P.modulus32 (x.val + y.val)) <| by
    simp_rw [← P.modulus32_toNat]
    apply conditionalSubtract_lt
    simp only [UInt32.toNat_add, P.modulus32_toNat]
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    linarith [x.property, y.property]

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : FastField modulus) : FastField modulus :=
  if hx : x.val = 0 then
    zero modulus
  else
    .mk (P.modulus32 - x.val) <| by
      have hle : x.val ≤ P.modulus32 := by
        simp [Nat.le_of_lt, UInt32.le_iff_toNat_le, x.property]
      simp [UInt32.toNat_sub_of_le _ _ hle]
      rw [← UInt32.toNat_inj] at hx
      change x.val.toNat ≠ 0 at hx
      omega

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : FastField modulus) : FastField modulus :=
  if hyx : y.val ≤ x.val then
    .mk (x.val - y.val) <| by
      rw [UInt32.toNat_sub_of_le _ _ hyx]
      have := x.property
      omega
  else
    .mk (x.val + P.modulus32 - y.val) <| by
      simp only [UInt32.le_iff_toNat_le] at hyx
      have hsum_lt : x.val.toNat + modulus < 2 ^ 32 := by
        have := x.property
        have := P.modulus_lt_two_pow_31
        omega
      have hyle : y.val ≤ x.val + P.modulus32 := by
        simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add, P.modulus32_toNat,
          Nat.mod_eq_of_lt hsum_lt]
        have := y.property
        omega
      rw [UInt32.toNat_sub_of_le _ _ hyle, UInt32.toNat_add, P.modulus32_toNat,
        Nat.mod_eq_of_lt hsum_lt]
      have := y.property
      omega

/-- Fast modular multiplication in Montgomery form. -/
@[inline]
def mul (x y : FastField modulus) : FastField modulus :=
  reduce (x.val.toUInt64 * y.val.toUInt64) (by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.modulus_lt_two_pow_32, P.modulus_pos])

/-- Fast squaring. -/
@[inline]
def square (x : FastField modulus) : FastField modulus := mul x x

/-- Exponentiation over the fast representation using repeated squaring. -/
@[specialize]
def pow (x : FastField modulus) (n : ℕ) : FastField modulus :=
  @npowBinRec (FastField modulus) ⟨one modulus⟩ ⟨mul⟩ n x

/-- Inversion in Montgomery form via Fermat's little theorem (`x⁻¹ = x^(p-2)`),
by binary exponentiation (`pow`). -/
@[inline]
def inv (x : FastField modulus) : FastField modulus :=
  pow x (modulus - 2)

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : FastField modulus) : FastField modulus :=
  mul x (inv y)

instance : Zero (FastField modulus) := ⟨zero modulus⟩
instance : One (FastField modulus) := ⟨one modulus⟩
instance : Add (FastField modulus) where add
instance : Neg (FastField modulus) where neg
instance : Sub (FastField modulus) where sub
instance : Mul (FastField modulus) where mul
instance : Inv (FastField modulus) where inv
instance : Div (FastField modulus) where div

theorem zero_def : (0 : FastField modulus) = zero modulus := rfl
theorem one_def : (1 : FastField modulus) = one modulus := rfl
theorem add_def (x y : FastField modulus) : x + y = add x y := rfl
theorem neg_def (x : FastField modulus) : -x = neg x := rfl
theorem sub_def (x y : FastField modulus) : x - y = sub x y := rfl
theorem mul_def (x y : FastField modulus) : x * y = mul x y := rfl
theorem inv_def (x : FastField modulus) : x⁻¹ = inv x := rfl
theorem div_def (x y : FastField modulus) : x / y = x * y⁻¹ := rfl
theorem square_def (x : FastField modulus) : square x = x * x := rfl

instance : NatCast (FastField modulus) := ⟨ofNat modulus⟩
instance : IntCast (FastField modulus) := ⟨ofInt modulus⟩

instance : SMul ℕ (FastField modulus) where
  smul n x := ofNat modulus n * x

instance : SMul Int (FastField modulus) where
  smul n x := ofInt modulus n * x

instance : Pow (FastField modulus) ℕ where pow

instance : Pow (FastField modulus) Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

instance : NNRatCast (FastField modulus) where
  nnratCast q := ofField (q : ZMod modulus)

instance : RatCast (FastField modulus) where
  ratCast q := ofField (q : ZMod modulus)

instance : SMul ℚ≥0 (FastField modulus) where
  smul q x := ofField (q • toField x)

instance : SMul ℚ (FastField modulus) where
  smul q x := ofField (q • toField x)

/-! ## Correctness -/

/-! ### Reduction and conversions -/

private theorem reduce_val_toNat_cast {x : UInt64}
    (h : x.toNat < modulus * 2 ^ 32) :
    ((reduce x h).val.toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  apply reduceRaw_cast <;>
    simp [P.montgomeryNegInv_mul_modulus_mod_two_pow_32, P.two_ne_zero, *]

@[simp]
theorem FastField.val_toNat_lt (x : FastField modulus) : x.val.toNat < modulus := x.property

theorem toNat_lt_modulus {x : FastField modulus} : toNat x < modulus := by
  simp [FastField.toNat, FastField.toUInt32]

private theorem toField_eq_val_toNat_cast_mul_inv {x : FastField modulus} :
    toField x =
      (x.val.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  have hb : (x.val.toUInt64).toNat < modulus * 2 ^ 32 := by
    rw [UInt32.toNat_toUInt64]; nlinarith [x.property, P.modulus_pos]
  rw [show toField x
        = (x.val.toUInt64.toNat : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ from
      reduce_val_toNat_cast (P := P) (x := x.val.toUInt64) hb, UInt32.toNat_toUInt64]

private theorem val_toNat_cast_eq_toField_mul {x : FastField modulus} :
    (x.val.toNat : ZMod modulus) =
      toField x * ((2 ^ 32 : ℕ) : ZMod modulus) := by
  rw [toField_eq_val_toNat_cast_mul_inv, mul_assoc]
  rw [inv_mul_cancel₀ P.two_pow_32_ne_zero, mul_one]

private theorem ofCanonicalNat_val_toNat_cast {n : ℕ} (h : n < modulus) :
    ((ofCanonicalNat n h).val.toNat : ZMod modulus) =
      (n : ZMod modulus) * ((2 ^ 32 : ℕ) : ZMod modulus) := by
  have hb : (UInt64.ofNat n * P.r2ModModulus).toNat < modulus * 2 ^ 32 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_ofNat', P.r2ModModulus_toNat, Nat.mod_mul_mod]
    apply Nat.mod_lt_of_lt
    have hr : (2 ^ 32) ^ 2 % modulus < modulus := Nat.mod_lt _ P.modulus_pos
    have h1 : n * ((2 ^ 32) ^ 2 % modulus) < modulus * modulus :=
      Nat.mul_lt_mul_of_lt_of_lt h hr
    have h2 : modulus * modulus < modulus * 2 ^ 32 :=
      (Nat.mul_lt_mul_left P.modulus_pos).mpr P.modulus_lt_two_pow_32
    exact lt_trans h1 h2
  rw [show ((ofCanonicalNat n h).val.toNat : ZMod modulus)
        = ((UInt64.ofNat n * P.r2ModModulus).toNat : ZMod modulus)
            * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ from
      reduce_val_toNat_cast (P := P) (x := UInt64.ofNat n * P.r2ModModulus) hb]
  simp only [Nat.cast_pow, Nat.cast_ofNat, UInt64.toNat_mul, UInt64.toNat_ofNat',
    P.r2ModModulus_toNat, Nat.mod_mul_mod]
  have hprod : n * ((2 ^ 32) ^ 2 % modulus) < 2 ^ 64 := by
    nlinarith [P.r2ModModulus_lt_modulus, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod]
  grind

@[simp]
theorem toField_ofCanonicalNat {n : ℕ} (h : n < modulus) :
    toField (ofCanonicalNat n h) = (n : ZMod modulus) := by
  rw [toField_eq_val_toNat_cast_mul_inv, ofCanonicalNat_val_toNat_cast, mul_assoc]
  rw [mul_inv_cancel₀ P.two_pow_32_ne_zero, mul_one]

@[simp]
theorem toNat_ofCanonicalNat {n : ℕ} (h : n < modulus) :
    toNat (ofCanonicalNat n h) = n :=
  natCast_inj_of_lt (toField_ofCanonicalNat h) toNat_lt_modulus h

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod modulus) : toField (ofField x) = x := by
  simp [ofField, toField_ofCanonicalNat]

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : FastField modulus) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt32.toNat_inj.mp
  apply natCast_inj_of_lt
  · rw [val_toNat_cast_eq_toField_mul, toField_ofField]
    rw [val_toNat_cast_eq_toField_mul]
  · simp
  · simp

/-- The canonical-field interpretation distinguishes fast values. -/
theorem toField_injective : Function.Injective (toField (modulus := modulus)) :=
  Function.LeftInverse.injective ofField_toField

/-! ### Field operations -/

/-- `toField` maps fast zero to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : FastField modulus) = 0 := by
  simp [toField_eq_val_toNat_cast_mul_inv, zero_def, zero]

/-- `toField` maps fast one to canonical one. -/
@[simp]
theorem toField_one : toField (1 : FastField modulus) = 1 := by
  simp only [toField_eq_val_toNat_cast_mul_inv, one_def, one,
    Mont32Field.rModModulus_toNat, ZMod.natCast_mod]
  exact mul_inv_cancel₀ P.two_pow_32_ne_zero

/-- Fast addition agrees with addition in the canonical field. -/
@[simp]
theorem toField_add (x y : FastField modulus) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_val_toNat_cast_mul_inv, toField_eq_val_toNat_cast_mul_inv (x := x),
    toField_eq_val_toNat_cast_mul_inv (x := y), add_def, add]
  have hred := conditionalSubtract_cast (p32 := P.modulus32) (u := x.val + y.val)
  rw [P.modulus32_toNat] at hred
  rw [hred, UInt32.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < 2 ^ 32 := by
    nlinarith [x.property, y.property, P.modulus_lt_two_pow_31]
  rw [Nat.mod_eq_of_lt hsum_lt, Nat.cast_add]
  ring

/-- Fast subtraction agrees with subtraction in the canonical field. -/
@[simp]
theorem toField_sub (x y : FastField modulus) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_val_toNat_cast_mul_inv, toField_eq_val_toNat_cast_mul_inv (x := x),
    toField_eq_val_toNat_cast_mul_inv (x := y)]
  simp only [sub_def]
  by_cases hyx : y.val ≤ x.val
  · simp only [sub, hyx, ↓reduceDIte]
    rw [UInt32.toNat_sub_of_le _ _ hyx]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le] at hyx
      exact hyx)]
    ring
  · have hsum_lt : x.val.toNat + modulus < 2 ^ 32 := by
      have htwo := P.modulus_lt_two_pow_31
      have := x.property; omega
    have hsum_eq : (x.val + P.modulus32).toNat = x.val.toNat + modulus := by
      rw [UInt32.toNat_add, P.modulus32_toNat, Nat.mod_eq_of_lt hsum_lt]
    have hyle : y.val ≤ x.val + P.modulus32 := by
      rw [UInt32.le_iff_toNat_le, hsum_eq]
      have := y.property; omega
    simp only [sub, hyx, ↓reduceDIte]
    rw [UInt32.toNat_sub_of_le _ _ hyle, hsum_eq]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, hsum_eq] at hyle
      exact hyle)]
    rw [Nat.cast_add, ZMod.natCast_self]
    ring

/-- Fast negation agrees with negation in the canonical field. -/
@[simp]
theorem toField_neg (x : FastField modulus) : toField (-x) = -toField x := by
  rw [toField_eq_val_toNat_cast_mul_inv, toField_eq_val_toNat_cast_mul_inv (x := x)]
  simp only [neg_def]
  by_cases hx : x.val = 0
  · simp only [neg, hx, ↓reduceDIte, zero]
    have hxNat := congrArg UInt32.toNat hx
    simp_all
  · have hle : x.val ≤ P.modulus32 := by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat]
      exact Nat.le_of_lt x.property
    simp only [neg, hx, ↓reduceDIte]
    rw [UInt32.toNat_sub_of_le _ _ hle, P.modulus32_toNat]
    rw [Nat.cast_sub (by
      rw [UInt32.le_iff_toNat_le, P.modulus32_toNat] at hle
      exact hle)]
    rw [ZMod.natCast_self]
    ring

/-- Fast multiplication agrees with multiplication in the canonical field. -/
private theorem mul_val_toNat_cast (x y : FastField modulus) :
  ((mul x y).val.toNat : ZMod modulus) =
    (x.val.toNat : ZMod modulus) * (y.val.toNat : ZMod modulus) *
      ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ := by
  have hb : (x.val.toUInt64 * y.val.toUInt64).toNat < modulus * 2 ^ 32 := by
    simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
      nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
    rw [Nat.mod_eq_of_lt hprod]
    nlinarith [x.property, y.property, P.modulus_lt_two_pow_32, P.modulus_pos]
  rw [show ((mul x y).val.toNat : ZMod modulus)
        = ((x.val.toUInt64 * y.val.toUInt64).toNat : ZMod modulus)
            * ((2 ^ 32 : ℕ) : ZMod modulus)⁻¹ from
      reduce_val_toNat_cast (P := P) (x := x.val.toUInt64 * y.val.toUInt64) hb]
  simp only [UInt64.toNat_mul, UInt32.toNat_toUInt64]
  have hprod : x.val.toNat * y.val.toNat < 2 ^ 64 := by
    nlinarith [x.property, y.property, P.modulus_sq_lt_two_pow_64]
  rw [Nat.mod_eq_of_lt hprod, Nat.cast_mul]

@[simp]
theorem toField_mul (x y : FastField modulus) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_val_toNat_cast_mul_inv, toField_eq_val_toNat_cast_mul_inv (x := x),
    toField_eq_val_toNat_cast_mul_inv (x := y), mul_def, mul_val_toNat_cast]
  ring

private theorem mul_assoc (x y z : FastField modulus) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : FastField modulus) (n : ℕ) : pow x (n + 1) = pow x n * x := by
  unfold pow
  let : Semigroup (FastField modulus) := { mul, mul_assoc }
  exact npowBinRec_succ n x

/-- Fast squaring agrees with multiplication by itself in the canonical field. -/
@[simp]
theorem toField_square (x : FastField modulus) : toField (square x) = toField x * toField x := by
  simp only [square_def, toField_mul]

/-- Fast natural-power computation agrees with powers in the canonical field. -/
@[simp]
theorem toField_pow (x : FastField modulus) (n : ℕ) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero]
      rw [toField_one]
      simp
  | succ n ih =>
      rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

/-- Fermat-style inversion in `ZMod modulus`. -/
private theorem inv_eq_pow {a : ZMod modulus} (ha : a ≠ 0) :
    a⁻¹ = a ^ (modulus - 2) := by
  have hcard : Fintype.card (ZMod modulus) = modulus := ZMod.card modulus
  have h1 : a ^ (modulus - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h; exact h
  have hmul : a * a ^ (modulus - 2) = 1 := by
    rw [← pow_succ']; show a ^ (modulus - 2 + 1) = 1
    have : modulus - 2 + 1 = modulus - 1 := by
      have := P.two_lt_modulus; omega
    rw [this]; exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : FastField modulus) : toField x⁻¹ = (toField x)⁻¹ := by
  simp only [inv_def, inv, toField_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero, zero_pow]
    have := P.two_lt_modulus
    omega
  · rw [inv_eq_pow hx]

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : FastField modulus) : toField (x / y) = toField x / toField y := by
  simp only [div_def, toField_mul, toField_inv]
  rfl

/-- Natural casts into fast form agree with natural casts into the canonical field. -/
@[simp]
theorem toField_natCast (n : ℕ) : toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofNat modulus n) = (n : ZMod modulus)
  rw [ofNat, toField_ofCanonicalNat, ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

/-- Integer casts into fast form agree with integer casts into the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofField n) = (n : ZMod modulus)
  rw [toField_ofField]

/-- Natural scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nsmul (n : ℕ) (x : FastField modulus) : toField (n • x) = n • toField x := by
  change toField ((n : FastField modulus) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

/-- Integer scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_zsmul (n : Int) (x : FastField modulus) : toField (n • x) = n • toField x := by
  change toField ((n : FastField modulus) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

/-- Natural powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_npow (x : FastField modulus) (n : ℕ) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Integer powers through the `Pow` instance are preserved by `toField`. -/
@[simp]
theorem toField_zpow (x : FastField modulus) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := by
        change toField x⁻¹ = (toField x)⁻¹
        rw [toField_inv]
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

/-- Nonnegative rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus)) = (q : ZMod modulus)
  rw [toField_ofField]

/-- Rational casts into fast form agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus)) = (q : ZMod modulus)
  rw [toField_ofField]

/-- Nonnegative rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Rational scalar multiplication is preserved by `toField`. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ### Algebraic structure -/

/-- Ring equivalence between the fast Montgomery representation and the canonical field. -/
def ringEquiv (modulus : ℕ) [P : Mont32Field modulus] : FastField modulus ≃+* ZMod modulus where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp]
theorem ringEquiv_apply {x : FastField modulus} : ringEquiv modulus x = toField x := rfl

@[simp]
theorem ringEquiv_symm_apply {x : ZMod modulus} :
    (ringEquiv modulus).symm x = ofField x := rfl

/-- Field instance transferred from the canonical field through `toField`. -/
instance instField : _root_.Field (FastField modulus) := by
  apply toField_injective.field toField <;> simp

/-- A fast 32-bit-word field is non-binary. -/
instance instNonBinaryField : NonBinaryField (FastField modulus) where
  char_neq_2 := by
    intro h
    apply P.two_ne_zero
    calc
      _ = toField ((2 : ℕ) : FastField modulus) := (toField_natCast 2).symm
      _ = toField (0 : FastField modulus) := congrArg toField h
      _ = 0 := toField_zero

end

end Native32
end Montgomery
