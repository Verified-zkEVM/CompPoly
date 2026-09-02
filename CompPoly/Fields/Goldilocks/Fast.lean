/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/
module

public import CompPoly.Fields.Goldilocks.FastReduction
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Fast Goldilocks Field

Verified `UInt64`-backed implementation of Goldilocks arithmetic, `p = 2^64 - 2^32 + 1`.
The carrier is a subtype of `UInt64` holding canonical representatives, wrapping the raw
kernels from `FastDefs` with the bounds proved in `FastReduction`. Every operation is
identified with its counterpart in the canonical `ZMod` model, and the field instances
are transferred across `toField`.

Reduction rests on `2^64 ≡ 2^32 - 1 (mod p)`, so a 128-bit product folds back into one
word with shifts, one multiply by `2^32 - 1`, and carry corrections.
-/

@[expose] public section

namespace Goldilocks
namespace Fast

/-! ## Carrier and arithmetic -/


/-- The fast native-word Goldilocks field carrier, stored as a canonical residue. -/
abbrev Field : Type := { x : UInt64 // x.toNat < Goldilocks.fieldSize }

/-- Fast representatives have decidable equality through their `UInt64` value. -/
instance : DecidableEq Field := inferInstance

/-- The raw canonical word backing a fast Goldilocks element. -/
@[inline]
def raw (x : Field) : UInt64 := x.val

/-- Reading the raw word from a subtype literal returns its stored word. -/
@[simp]
theorem raw_mk (x : UInt64) (h : x.toNat < Goldilocks.fieldSize) :
    raw ⟨x, h⟩ = x := rfl

/-- `raw` is the underlying `UInt64` value. -/
@[simp]
theorem raw_eq_val (x : Field) : raw x = x.val := rfl

/-- Reduce a native `UInt64` modulo Goldilocks. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  ⟨reduceUInt64Raw x, reduceUInt64Raw_lt x⟩

/-- One-word reduction preserves the represented canonical field element. -/
@[simp]
theorem reduceUInt64_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : Goldilocks.Field) =
      (x.toNat : Goldilocks.Field) := by
  exact reduceUInt64Raw_cast x

/-- The zero fast Goldilocks element. -/
@[inline]
def zero : Field := ⟨0, by decide⟩

/-- The one fast Goldilocks element. -/
@[inline]
def one : Field := ⟨1, by decide⟩

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < Goldilocks.fieldSize) : Field :=
  ⟨UInt64.ofNat n, by
    have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
    rw [UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    · exact h
    · simpa [UInt64.size] using hn⟩

/-- Convert a natural number into fast canonical representation. -/
@[inline]
def ofNat (n : Nat) : Field :=
  ofCanonicalNat (n % Goldilocks.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 64-bit word into fast canonical representation. -/
@[inline]
def ofUInt64 (x : UInt64) : Field :=
  reduceUInt64 x

/-- Convert from the canonical `ZMod` Goldilocks field into fast canonical form. -/
@[inline]
def ofField (x : Goldilocks.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast canonical representation. -/
@[inline]
def ofInt (z : Int) : Field :=
  ofField (z : Goldilocks.Field)

/-- Convert a fast Goldilocks element to its canonical natural representative. -/
@[inline]
def toNat (x : Field) : Nat :=
  x.val.toNat

/-- Reading the natural representative of a subtype literal returns its stored word's
natural value. -/
@[simp]
theorem toNat_mk (x : UInt64) (h : x.toNat < Goldilocks.fieldSize) :
    toNat ⟨x, h⟩ = x.toNat := rfl

/-- `toNat` is the natural value of the underlying `UInt64` word. -/
@[simp]
theorem toNat_eq_val_toNat (x : Field) : toNat x = x.val.toNat := rfl

/-- Convert a fast Goldilocks element to the canonical `ZMod` Goldilocks field. -/
@[inline]
def toField (x : Field) : Goldilocks.Field :=
  (toNat x : Goldilocks.Field)

/-- Fast modular addition in canonical form. -/
@[inline]
def add (x y : Field) : Field :=
  let lo := x.val + y.val
  let carry := decide (lo < x.val)
  ⟨reduceAddWithCarryRaw lo carry,
    reduceAddWithCarryRaw_lt lo carry
      (addWithCarry_bound x.val y.val x.property y.property)⟩

/-- Fast modular negation in canonical form. -/
@[inline]
def neg (x : Field) : Field :=
  ⟨negRaw x.val, negRaw_lt x.val x.property⟩

/-- Fast modular subtraction in canonical form. -/
@[inline]
def sub (x y : Field) : Field :=
  ⟨subRaw x.val y.val, subRaw_lt x.val y.val x.property y.property⟩

/-- Fast modular multiplication in canonical form. -/
@[inline]
def mul (x y : Field) : Field :=
  ⟨reduceMulRaw x.val y.val, reduceMulRaw_lt x.val y.val⟩

/-- Fast squaring. -/
@[inline]
def square (x : Field) : Field :=
  mul x x

/-- Repeated squaring: `squareN x n` computes `x^(2^n)`. -/
@[inline]
def squareN (x : Field) : Nat → Field
  | 0 => x
  | n + 1 => square (squareN x n)

/-- Exponentiation over the fast representation using binary exponentiation. -/
@[inline]
def pow (x : Field) (n : Nat) : Field :=
  @npowBinRec Field ⟨one⟩ ⟨mul⟩ n x

/-- Fermat exponent used for inversion in the Goldilocks prime field. -/
@[inline]
private def invExponent : Nat := Goldilocks.fieldSize - 2

/-- Fast modular inversion using an addition chain for `p - 2`.

For Goldilocks, `p - 2 = 0xFFFFFFFEFFFFFFFF`. The chain builds
`x^(2^31 - 1)`, derives `x^(2^32 - 2)` and `x^(2^32 - 1)`, then combines them as

`(2^32 - 2) * 2^32 + (2^32 - 1) = p - 2`.
-/
def inv (x : Field) : Field :=
  let t2 := mul (square x) x
  let t4 := mul (squareN t2 2) t2
  let t8 := mul (squareN t4 4) t4
  let t16 := mul (squareN t8 8) t8
  let t31 :=
    mul (squareN t16 15)
      (mul (squareN t8 7)
        (mul (squareN t4 3)
          (mul (square t2) x)))
  let t32m2 := square t31
  let t32m1 := mul t32m2 x
  mul (squareN t32m2 32) t32m1

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : Field) : Field :=
  mul x (inv y)

/-- Use fast zero for standard `0` notation. -/
instance instZeroField : Zero Field where
  zero := zero

/-- Use fast one for standard `1` notation. -/
instance instOneField : One Field where
  one := one

/-- The raw word backing fast zero is zero. -/
@[simp]
theorem raw_zero : raw (0 : Field) = 0 := rfl

/-- The raw word backing fast one is one. -/
@[simp]
theorem raw_one : raw (1 : Field) = 1 := rfl

/-- The natural representative of fast zero is zero. -/
@[simp]
theorem toNat_zero : toNat (0 : Field) = 0 := rfl

/-- The natural representative of fast one is one. -/
@[simp]
theorem toNat_one : toNat (1 : Field) = 1 := rfl

/-- Use fast addition for standard `+` notation. -/
instance instAddField : Add Field where
  add := add

/-- Use fast negation for standard unary `-` notation. -/
instance instNegField : Neg Field where
  neg := neg

/-- Use fast subtraction for standard `-` notation. -/
instance instSubField : Sub Field where
  sub := sub

/-- Use fast multiplication for standard `*` notation. -/
instance instMulField : Mul Field where
  mul := mul

/-- Use fast inversion for standard inverse notation. -/
instance instInvField : Inv Field where
  inv := inv

/-- Use fast division for standard `/` notation. -/
instance instDivField : Div Field where
  div := div

/-- Use `ofNat` for natural-number casts into fast Goldilocks. -/
instance instNatCastField : NatCast Field where
  natCast := ofNat

/-- Interpret integer casts through the canonical Goldilocks field. -/
instance instIntCastField : IntCast Field where
  intCast := ofInt

/-- Natural scalar multiplication is multiplication by the corresponding fast natural cast. -/
instance instNatSMulField : SMul Nat Field where
  smul n x := (n : Field) * x

/-- Integer scalar multiplication is multiplication by the corresponding fast integer cast. -/
instance instIntSMulField : SMul Int Field where
  smul n x := (n : Field) * x

/-- Use fast binary exponentiation for natural powers. -/
instance instPowFieldNat : Pow Field Nat where
  pow := pow

/-- Use fast natural powers and inversion for integer powers. -/
instance instPowFieldInt : Pow Field Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

/-- Interpret nonnegative rational casts through the canonical Goldilocks field. -/
instance instNNRatCastField : NNRatCast Field where
  nnratCast q := ofField (q : Goldilocks.Field)

/-- Interpret rational casts through the canonical Goldilocks field. -/
instance instRatCastField : RatCast Field where
  ratCast q := ofField (q : Goldilocks.Field)

/-- Nonnegative rational scalar multiplication is transported through the canonical field. -/
instance instNNRatSMulField : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

/-- Rational scalar multiplication is transported through the canonical field. -/
instance instRatSMulField : SMul ℚ Field where
  smul q x := ofField (q • toField x)

/-! ## Correctness against the canonical model -/


/-- Converting a canonical natural representative to fast form preserves its value. -/
@[simp]
private theorem toField_ofCanonicalNat (n : Nat) (h : n < Goldilocks.fieldSize) :
    toField (ofCanonicalNat n h) = (n : Goldilocks.Field) := by
  unfold toField toNat ofCanonicalNat
  have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
  rw [UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by simpa [UInt64.size] using hn)]

/-- Converting a canonical natural representative to fast form and reading it back is
the identity. -/
@[simp]
private theorem toNat_ofCanonicalNat (n : Nat) (h : n < Goldilocks.fieldSize) :
    toNat (ofCanonicalNat n h) = n := by
  unfold toNat ofCanonicalNat
  have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa [UInt64.size] using hn)

/-- The natural representative of a fast value built from `n` is `n` reduced modulo the
Goldilocks modulus. -/
@[simp]
theorem toNat_ofNat (n : Nat) :
    toNat (ofNat n) = n % Goldilocks.fieldSize := by
  unfold ofNat
  rw [toNat_ofCanonicalNat]

/-- The natural representative of a fast value built from a `UInt64` is that word's
natural value reduced modulo the Goldilocks modulus. -/
@[simp]
theorem toNat_ofUInt64 (x : UInt64) :
    toNat (ofUInt64 x) = x.toNat % Goldilocks.fieldSize := by
  -- Reduce to the raw word first: unfolding the subtype would leave the membership
  -- proof depending on the term being rewritten.
  have hraw : toNat (ofUInt64 x) = (reduceUInt64Raw x).toNat := rfl
  rw [hraw]
  have hx_two := uint64_toNat_lt_two_fieldSize x
  unfold reduceUInt64Raw
  by_cases hx : x < modulus
  · rw [if_pos hx]
    rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
    exact (Nat.mod_eq_of_lt hx).symm
  · rw [if_neg hx]
    rw [UInt64.lt_iff_toNat_lt, modulus_toNat] at hx
    have hp : Goldilocks.fieldSize ≤ x.toNat := Nat.le_of_not_gt hx
    have hle : modulus ≤ x := by
      rw [UInt64.le_iff_toNat_le, modulus_toNat]
      exact hp
    -- One subtraction canonicalizes, because every `UInt64` is below `2 * fieldSize`.
    rw [UInt64.toNat_sub_of_le _ _ hle, modulus_toNat, Nat.mod_eq_sub_mod hp,
      Nat.mod_eq_of_lt (by omega)]

/-- Converting from the canonical `ZMod` field to fast form preserves the canonical
representative. -/
@[simp]
theorem toNat_ofField (x : Goldilocks.Field) : toNat (ofField x) = x.val := by
  unfold ofField
  rw [toNat_ofCanonicalNat]

/-- Converting a natural number to fast form agrees with the same natural cast in the
canonical field. -/
@[simp]
theorem toField_ofNat (n : Nat) :
    toField (ofNat n) = (n : Goldilocks.Field) := by
  unfold ofNat
  rw [toField_ofCanonicalNat]
  rw [← ZMod.natCast_zmod_val (n : Goldilocks.Field)]
  rw [ZMod.val_natCast]

/-- Converting a `UInt64` to fast form agrees with casting its natural value into the
canonical field. -/
@[simp]
theorem toField_ofUInt64 (x : UInt64) :
    toField (ofUInt64 x) = (x.toNat : Goldilocks.Field) := by
  unfold toField toNat ofUInt64
  exact reduceUInt64_cast x

/-- Converting an integer to fast form agrees with casting it into the canonical field. -/
@[simp]
theorem toField_ofInt (z : Int) :
    toField (ofInt z) = (z : Goldilocks.Field) := by
  unfold ofInt ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val (z : Goldilocks.Field)

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : Goldilocks.Field) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : Field) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt64.toNat_inj.mp
  change toNat (ofField (toField x)) = toNat x
  unfold ofField toField
  rw [toNat_ofCanonicalNat]
  exact ZMod.val_natCast_of_lt x.property

/-- The canonical-field interpretation distinguishes fast Goldilocks values. -/
theorem toField_injective : Function.Injective toField :=
  Function.LeftInverse.injective ofField_toField

/-- Fermat-style inversion in the canonical Goldilocks field. -/
private lemma canonical_inv_eq_pow (a : Goldilocks.Field) (ha : a ≠ 0) :
    a⁻¹ = a ^ (Goldilocks.fieldSize - 2) := by
  have hcard : Fintype.card Goldilocks.Field = Goldilocks.fieldSize :=
    ZMod.card Goldilocks.fieldSize
  have h1 : a ^ (Goldilocks.fieldSize - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h
    exact h
  have hmul : a * a ^ (Goldilocks.fieldSize - 2) = 1 := by
    rw [← pow_succ']
    show a ^ (Goldilocks.fieldSize - 2 + 1) = 1
    have : Goldilocks.fieldSize - 2 + 1 = Goldilocks.fieldSize - 1 := by
      unfold Goldilocks.fieldSize
      omega
    rw [this]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

/-- Fast zero maps to canonical zero. -/
@[simp]
theorem toField_zero : toField (0 : Field) = 0 := by
  decide

/-- Fast one maps to canonical one. -/
@[simp]
theorem toField_one : toField (1 : Field) = 1 := by
  decide

/-- Fast addition agrees with canonical-field addition. -/
@[simp]
theorem toField_add (x y : Field) : toField (x + y) = toField x + toField y := by
  change
    (((add x y).val.toNat : Goldilocks.Field) =
      (x.val.toNat : Goldilocks.Field) + (y.val.toNat : Goldilocks.Field))
  unfold add
  rw [reduceAddWithCarryRaw_cast _ _
    (addWithCarry_bound x.val y.val x.property y.property)]
  let lo := x.val + y.val
  let carry := decide (lo < x.val)
  have hvalue := addWithCarry_value x.val y.val
  change lo.toNat + (if carry then UInt64.size else 0) = x.val.toNat + y.val.toNat at hvalue
  change
    ((lo.toNat : Goldilocks.Field) +
        (if carry then (UInt64.size : Goldilocks.Field) else 0) =
      (x.val.toNat : Goldilocks.Field) + (y.val.toNat : Goldilocks.Field))
  by_cases hcarry : carry = true
  · simp only [hcarry, if_true] at hvalue ⊢
    rw [← Nat.cast_add, hvalue, Nat.cast_add]
  · simp only [hcarry, Bool.false_eq_true, if_false, add_zero] at hvalue ⊢
    rw [hvalue, Nat.cast_add]

/-- Fast negation agrees with canonical-field negation. -/
@[simp]
theorem toField_neg (x : Field) : toField (-x) = -toField x := by
  change toField (neg x) = -(toField x)
  unfold neg toField toNat
  exact negRaw_cast x.val x.property

/-- Fast subtraction agrees with canonical-field subtraction. -/
@[simp]
theorem toField_sub (x y : Field) : toField (x - y) = toField x - toField y := by
  change toField (sub x y) = toField x - toField y
  unfold sub toField toNat
  exact subRaw_cast x.val y.val x.property y.property

/-- Fast multiplication agrees with canonical-field multiplication. -/
@[simp]
theorem toField_mul (x y : Field) : toField (x * y) = toField x * toField y := by
  change toField (mul x y) = toField x * toField y
  unfold mul toField toNat
  exact reduceMulRaw_cast x.val y.val

/-- The named fast multiplication function agrees with canonical-field multiplication. -/
@[simp]
theorem toField_mul_def (x y : Field) : toField (mul x y) = toField x * toField y :=
  toField_mul x y

/-- Fast squaring agrees with multiplying the canonical field value by itself. -/
@[simp]
theorem toField_square (x : Field) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

/-- Repeated fast squaring agrees with raising to `2^n` in the canonical field. -/
@[simp]
theorem toField_squareN (x : Field) (n : Nat) :
    toField (squareN x n) = toField x ^ (2 ^ n) := by
  induction n generalizing x with
  | zero =>
      unfold squareN
      simp
  | succ n ih =>
      unfold squareN
      rw [toField_square, ih]
      rw [← pow_add]
      congr 1
      rw [Nat.pow_succ]
      omega

/-- Fast multiplication is associative, proved by transporting to the canonical field. -/
private theorem mul_assoc_field (x y z : Field) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

/-- Binary exponentiation satisfies the expected successor equation. -/
private theorem pow_succ (x : Field) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  let _ : Semigroup Field := {
    mul := (· * ·)
    mul_assoc := mul_assoc_field
  }
  exact npowBinRec_succ n x

/-- Fast natural-power computation agrees with powers in the canonical field. -/
@[simp]
theorem toField_pow (x : Field) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero]
      rw [toField_one]
      simp
  | succ n ih =>
      rw [pow_succ, toField_mul, ih, _root_.pow_succ]

/-- The optimized inversion chain computes the Fermat inverse exponent. -/
private theorem toField_inv_chain (x : Field) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv
  simp only [toField_mul_def, toField_square, toField_squareN]
  ring_nf
  simp [invExponent, Goldilocks.fieldSize]

/-- Fast inversion agrees with canonical inversion before notation is unfolded. -/
private theorem toField_inv_raw (x : Field) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_chain]
  by_cases hx : toField x = 0
  · rw [hx]
    simp [invExponent, Goldilocks.fieldSize]
  · simpa [invExponent] using (canonical_inv_eq_pow (toField x) hx).symm

/-- Fast inversion agrees with inversion in the canonical field. -/
@[simp]
theorem toField_inv (x : Field) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

/-- Division is multiplication by inverse at the level of canonical interpretation. -/
private theorem toField_div_mul_inv (x y : Field) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div
  change toField (x * inv y) = toField x * toField (inv y)
  exact toField_mul x (inv y)

/-- Fast division agrees with division in the canonical field. -/
@[simp]
theorem toField_div (x y : Field) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  rw [toField_div_mul_inv, toField_inv_raw y]
  rfl

/-- Natural casts in the fast field agree with natural casts in the canonical field. -/
@[simp]
theorem toField_natCast (n : Nat) : toField (n : Field) = (n : Goldilocks.Field) := by
  change toField (ofNat n) = (n : Goldilocks.Field)
  rw [toField_ofNat]

/-- Integer casts in the fast field agree with integer casts in the canonical field. -/
@[simp]
theorem toField_intCast (n : Int) : toField (n : Field) = (n : Goldilocks.Field) := by
  change toField (ofInt n) = (n : Goldilocks.Field)
  rw [toField_ofInt]

/-- Fast natural scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_nsmul (n : Nat) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_natCast]
  rw [nsmul_eq_mul]

/-- Fast integer scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_zsmul (n : Int) (x : Field) : toField (n • x) = n • toField x := by
  change toField ((n : Field) * x) = n • toField x
  rw [toField_mul, toField_intCast]
  rw [zsmul_eq_mul]

/-- Standard fast natural powers agree with powers in the canonical field. -/
@[simp]
theorem toField_npow (x : Field) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

/-- Standard fast integer powers agree with integer powers in the canonical field. -/
@[simp]
theorem toField_zpow (x : Field) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]
      exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := toField_inv_raw x
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

/-- Nonnegative rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : Field) = (q : Goldilocks.Field) := by
  change toField (ofField (q : Goldilocks.Field)) = (q : Goldilocks.Field)
  rw [toField_ofField]

/-- Rational casts in the fast field agree with canonical-field casts. -/
@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : Field) = (q : Goldilocks.Field) := by
  change toField (ofField (q : Goldilocks.Field)) = (q : Goldilocks.Field)
  rw [toField_ofField]

/-- Fast nonnegative rational scalar multiplication agrees with canonical-field scalar
multiplication. -/
@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : Field) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-- Fast rational scalar multiplication agrees with canonical-field scalar multiplication. -/
@[simp]
theorem toField_qsmul (q : ℚ) (x : Field) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ## Canonical bridge and field instances -/


/-- Ring equivalence between the fast representation and canonical Goldilocks. -/
def ringEquiv : Field ≃+* Goldilocks.Field where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

/-- Applying `ringEquiv` is the same as interpreting a fast value canonically. -/
@[simp]
theorem ringEquiv_apply (x : Field) : ringEquiv x = toField x := rfl

/-- Applying the inverse `ringEquiv` converts a canonical value into fast form. -/
@[simp]
theorem ringEquiv_symm_apply (x : Goldilocks.Field) : ringEquiv.symm x = ofField x := rfl

/-- Field instance transferred from canonical Goldilocks through `toField`. -/
instance (priority := low) instField : _root_.Field Field :=
  toField_injective.field toField
    toField_zero
    toField_one
    toField_add
    toField_mul
    toField_neg
    toField_sub
    toField_inv
    toField_div
    toField_nsmul
    toField_zsmul
    toField_nnqsmul
    toField_qsmul
    toField_npow
    toField_zpow
    toField_natCast
    toField_intCast
    toField_nnratCast
    toField_ratCast

/-- Commutative-ring instance inherited from the transferred field structure. -/
instance (priority := low) instCommRing : CommRing Field := by
  infer_instance

/-- Fast Goldilocks is a non-binary field. -/
instance (priority := low) instNonBinaryField : NonBinaryField Field where
  char_neq_2 := by
    intro h
    have hv := congrArg Subtype.val h
    exact (by decide : (2 : UInt64) ≠ 0) hv

end Fast
end Goldilocks
