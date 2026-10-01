/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos, Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Basic
public import CompPoly.Fields.Montgomery.Native64x4Mul
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Fast four-limb Montgomery fields

The carrier `{ x : Limbs4 // x.toNat < modulus }` stores the Montgomery residue
`x * 2 ^ 256 mod modulus` for any prime modulus below `2 ^ 256`; `toField` divides by `2 ^ 256`
and lands in `ZMod modulus`, and all arithmetic is transported along that ring isomorphism.

## Main results

* `FastField` — the carrier, `{ x : Limbs4 // x.toNat < modulus }`
* `toField_add`, `toField_mul`, … — `@[simp]` equivalences with the canonical field
* `Mont64x4Field` — the per-field constants class
* `ringEquiv`, `instField` — the ring isomorphism and the transferred `Field` instance
-/

@[expose] public section

namespace Montgomery
namespace Native64x4

/-! ## Per-field constants -/

/-- Per-field data for a fast four-limb Montgomery field with radix `R = 2 ^ 256`.  All side
conditions are concrete numeral facts, discharged by `decide` at instantiation. -/
class Mont64x4Field (modulus : ℕ) where
  /-- `modulus` is prime. -/
  prime : modulus.Prime
  /-- The modulus in four 64-bit limbs. -/
  modulusLimbs : Limbs4
  /-- `2 ^ 256 mod modulus`, the Montgomery representation of one. -/
  rModModulus : Limbs4
  /-- `(2 ^ 256) ^ 2 mod modulus`, used to enter Montgomery form. -/
  r2ModModulus : Limbs4
  /-- `-modulus⁻¹ mod 2 ^ 64`, used by Montgomery reduction. -/
  montgomeryNegInv : UInt64
  modulusLimbs_toNat : modulusLimbs.toNat = modulus := by decide
  two_lt_modulus : 2 < modulus := by decide
  rModModulus_toNat : rModModulus.toNat = 2 ^ 256 % modulus := by decide
  r2ModModulus_toNat : r2ModModulus.toNat = (2 ^ 256) ^ 2 % modulus := by decide
  montgomeryNegInv_mul_modulus_mod_two_pow_64 :
    montgomeryNegInv.toNat * modulus % 2 ^ 64 = 2 ^ 64 - 1 := by decide

/-! ## Modulus facts -/

namespace Mont64x4Field

variable {modulus : ℕ} [P : Mont64x4Field modulus]

instance : Fact (Nat.Prime modulus) := ⟨P.prime⟩

theorem modulus_pos : 0 < modulus := Nat.zero_lt_of_lt P.two_lt_modulus

theorem modulus_lt : modulus < 2 ^ 256 := by
  have h := Limbs4.toNat_lt P.modulusLimbs
  rwa [P.modulusLimbs_toNat] at h

theorem q_toNat : P.modulusLimbs.toNat = modulus := P.modulusLimbs_toNat

theorem negInv_mul_q : P.montgomeryNegInv.toNat * P.modulusLimbs.toNat % 2 ^ 64 = 2 ^ 64 - 1 := by
  rw [q_toNat]
  exact P.montgomeryNegInv_mul_modulus_mod_two_pow_64

instance : NeZero modulus := ⟨modulus_pos.ne'⟩

theorem two_ne_zero : (2 : ZMod modulus) ≠ 0 := by
  intro h
  have hdvd : modulus ∣ 2 := (ZMod.natCast_eq_zero_iff 2 modulus).mp h
  exact (Nat.not_le_of_gt P.two_lt_modulus) (Nat.le_of_dvd (by decide) hdvd)

theorem r_ne_zero : ((2 ^ 256 : ℕ) : ZMod modulus) ≠ 0 := by
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact pow_ne_zero _ two_ne_zero

end Mont64x4Field

/-! ## The carrier -/

/-- The fast carrier: four 64-bit limbs holding a Montgomery residue below `modulus`, erasing
to `Limbs4` at runtime. -/
@[implicit_reducible]
def FastField (modulus : ℕ) [Mont64x4Field modulus] : Type :=
  { x : Limbs4 // x.toNat < modulus }

section

variable {modulus : ℕ} [P : Mont64x4Field modulus]

instance : DecidableEq (FastField modulus) :=
  inferInstanceAs (DecidableEq { x : Limbs4 // x.toNat < modulus })

namespace FastField

theorem val_lt (x : FastField modulus) : x.val.toNat < P.modulusLimbs.toNat := by
  rw [Mont64x4Field.q_toNat]
  exact x.property

/-! ### Arithmetic -/

/-- The zero element. -/
def zero (modulus : ℕ) [P : Mont64x4Field modulus] : FastField modulus :=
  ⟨Limbs4.zero, by
    rw [Limbs4.zero_toNat]
    exact Mont64x4Field.modulus_pos⟩

/-- The one element, the Montgomery residue `2 ^ 256 mod modulus`. -/
def one (modulus : ℕ) [P : Mont64x4Field modulus] : FastField modulus :=
  ⟨P.rModModulus, by
    rw [P.rModModulus_toNat]
    exact Nat.mod_lt _ Mont64x4Field.modulus_pos⟩

/-- Fast modular addition in Montgomery form. Borrow the second operand so chained additions
can reuse the first operand's storage. Keep the function specialized rather than inline so
this ownership boundary survives at call sites. -/
@[specialize P] def add (x : FastField modulus) (y : @& FastField modulus) : FastField modulus :=
  ⟨Native64x4.add P.modulusLimbs x.val y.val, by
    have h := add_lt _ _ _ x.val_lt y.val_lt
    rwa [Mont64x4Field.q_toNat] at h⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline] def sub (x y : FastField modulus) : FastField modulus :=
  ⟨Native64x4.sub P.modulusLimbs x.val y.val, by
    have h := sub_lt _ _ _ x.val_lt y.val_lt
    rwa [Mont64x4Field.q_toNat] at h⟩

/-- Fast modular negation in Montgomery form. -/
@[inline] def neg (x : FastField modulus) : FastField modulus :=
  ⟨Native64x4.neg P.modulusLimbs x.val, by
    have h := neg_lt _ _ x.val_lt
    rwa [Mont64x4Field.q_toNat] at h⟩

/-- Keep modulus words dynamic so clang recognizes widening products. The scalar API
continues to inline `Native64x4.mul` directly for callers that retain unboxed state. -/
@[noinline] def mulKernel (q : Limbs4) (negInv : UInt64) (a b : Limbs4) : Limbs4 :=
  Native64x4.mul q negInv a b

/-- The same code-generation boundary for the dedicated symmetric square. -/
@[noinline] def squareKernel (q : Limbs4) (negInv : UInt64) (a : Limbs4) : Limbs4 :=
  Native64x4.squareCached q negInv a

/-- Fast Montgomery multiplication. -/
@[inline] def mul (x y : FastField modulus) : FastField modulus :=
  ⟨mulKernel P.modulusLimbs P.montgomeryNegInv x.val y.val, by
    have h := (mul_spec P.modulusLimbs P.montgomeryNegInv x.val y.val
      Mont64x4Field.negInv_mul_q x.val_lt).1
    rwa [Mont64x4Field.q_toNat] at h⟩

/-- Fast squaring. -/
@[inline] def square (x : FastField modulus) : FastField modulus := mul x x

/-- Exponentiation by repeated squaring. -/
@[specialize] def pow (x : FastField modulus) (n : ℕ) : FastField modulus :=
  @npowBinRec (FastField modulus) ⟨one modulus⟩ ⟨mul⟩ n x

/-- Dedicated square with shared symmetric limb products. -/
@[specialize P] def squareCached (x : FastField modulus) : FastField modulus :=
  ⟨squareKernel P.modulusLimbs P.montgomeryNegInv x.val, by
    unfold squareKernel
    rw [squareCached_eq_mul]
    exact (mul x x).property⟩

private theorem squareCached_eq (x : FastField modulus) : squareCached x = mul x x := by
  apply Subtype.ext
  exact squareCached_eq_mul P.modulusLimbs P.montgomeryNegInv x.val

/-- Binary powering without the final unused square. -/
@[specialize P] def powTrimmedGo (n : ℕ) (a x : FastField modulus) : FastField modulus :=
  if _h : n ≤ 1 then if n == 0 then a else mul a x
  else powTrimmedGo (n / 2) (if n % 2 == 1 then mul a x else a) (squareCached x)
termination_by n

/-- Start with the first selected power instead of multiplying by one. -/
@[specialize P] def powTrimmedStart (n : ℕ) (x : FastField modulus) : FastField modulus :=
  if _h : n ≤ 1 then if n == 0 then one modulus else x
  else if n % 2 == 1 then powTrimmedGo (n / 2) x (squareCached x)
  else powTrimmedStart (n / 2) (squareCached x)
termination_by n

/-- Exponentiation skipping the initial identity product and final unused square. -/
@[specialize P] def powTrimmed (x : FastField modulus) (n : ℕ) : FastField modulus :=
  powTrimmedStart n x

/-- Inversion by Fermat's little theorem, `x⁻¹ = x ^ (modulus - 2)`. -/
@[inline] def inv (x : FastField modulus) : FastField modulus := pow x (modulus - 2)

/-- Division through inversion. -/
@[inline] def div (x y : FastField modulus) : FastField modulus := mul x (inv y)

/-! ### Conversions -/

/-- The canonical limb representative of a fast element: one Montgomery reduction. -/
@[inline] def toLimbs4 (x : FastField modulus) : Limbs4 :=
  Native64x4.mul P.modulusLimbs P.montgomeryNegInv x.val Limbs4.one

/-- The canonical natural representative of a fast element. -/
@[inline] def toNat (x : FastField modulus) : ℕ := (toLimbs4 x).toNat

/-- The canonical `ZMod` value of a fast element. -/
@[inline] def toField (x : FastField modulus) : ZMod modulus := (toNat x : ZMod modulus)

private theorem ofNat_lt_of_lt {n : ℕ} (h : n < modulus) :
    (Limbs4.ofNat n).toNat < P.modulusLimbs.toNat := by
  rw [Limbs4.ofNat_toNat, Mont64x4Field.q_toNat,
    Nat.mod_eq_of_lt (h.trans Mont64x4Field.modulus_lt)]
  exact h

/-- Build a fast element from a canonical natural representative. -/
@[inline] def ofCanonicalNat (n : ℕ) (h : n < modulus) : FastField modulus :=
  ⟨Native64x4.mul P.modulusLimbs P.montgomeryNegInv (Limbs4.ofNat n) P.r2ModModulus, by
    have hlt := (mul_spec P.modulusLimbs P.montgomeryNegInv (Limbs4.ofNat n) P.r2ModModulus
      Mont64x4Field.negInv_mul_q (ofNat_lt_of_lt h)).1
    rwa [Mont64x4Field.q_toNat] at hlt⟩

/-- Convert a natural number into fast Montgomery form. -/
@[inline] def ofNat (modulus : ℕ) [P : Mont64x4Field modulus] (n : ℕ) : FastField modulus :=
  ofCanonicalNat (n % modulus) (Nat.mod_lt _ Mont64x4Field.modulus_pos)

/-- Convert from the canonical field into fast Montgomery form. -/
@[inline] def ofField (x : ZMod modulus) : FastField modulus :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast Montgomery form. -/
@[inline] def ofInt (modulus : ℕ) [P : Mont64x4Field modulus] (n : Int) :
    FastField modulus :=
  ofField (n : ZMod modulus)

instance : Zero (FastField modulus) := ⟨FastField.zero modulus⟩
instance : One (FastField modulus) := ⟨FastField.one modulus⟩
instance : Add (FastField modulus) := ⟨FastField.add⟩
instance : Neg (FastField modulus) := ⟨FastField.neg⟩
instance : Sub (FastField modulus) := ⟨FastField.sub⟩
instance : Mul (FastField modulus) := ⟨FastField.mul⟩
instance : Inv (FastField modulus) := ⟨FastField.inv⟩
instance : Div (FastField modulus) := ⟨FastField.div⟩
instance : NatCast (FastField modulus) := ⟨FastField.ofNat modulus⟩
instance : IntCast (FastField modulus) := ⟨FastField.ofInt modulus⟩
instance : Pow (FastField modulus) ℕ := ⟨FastField.pow⟩

instance : SMul ℕ (FastField modulus) where
  smul n x := FastField.ofNat modulus n * x

instance : SMul Int (FastField modulus) where
  smul n x := FastField.ofInt modulus n * x

instance : Pow (FastField modulus) Int where
  pow x n :=
    match n with
    | Int.ofNat k => FastField.pow x k
    | Int.negSucc k => FastField.pow (FastField.inv x) (k + 1)

theorem zero_def : (0 : FastField modulus) = FastField.zero modulus := rfl
theorem one_def : (1 : FastField modulus) = FastField.one modulus := rfl
theorem add_def (x y : FastField modulus) : x + y = FastField.add x y := rfl
theorem neg_def (x : FastField modulus) : -x = FastField.neg x := rfl
theorem sub_def (x y : FastField modulus) : x - y = FastField.sub x y := rfl
theorem mul_def (x y : FastField modulus) : x * y = FastField.mul x y := rfl
theorem inv_def (x : FastField modulus) : x⁻¹ = FastField.inv x := rfl
theorem div_def (x y : FastField modulus) : x / y = x * y⁻¹ := rfl
theorem square_def (x : FastField modulus) : FastField.square x = x * x := rfl

/-- The limbs of a product. -/
theorem val_mul (x y : FastField modulus) :
    (x * y).val = Native64x4.mul P.modulusLimbs P.montgomeryNegInv x.val y.val :=
  Subtype.coe_mk _ _

/-! ## Correctness -/

section Bridge

instance : NNRatCast (FastField modulus) where
  nnratCast q := FastField.ofField (q : ZMod modulus)

instance : RatCast (FastField modulus) where
  ratCast q := FastField.ofField (q : ZMod modulus)

instance : SMul ℚ≥0 (FastField modulus) where
  smul q x := FastField.ofField (q • FastField.toField x)

instance : SMul ℚ (FastField modulus) where
  smul q x := FastField.ofField (q • FastField.toField x)

/-- The raw Montgomery product divides by `2 ^ 256` in the canonical field. -/
private theorem mul_cast (x y : Limbs4) (hxq : x.toNat < modulus) :
    ((Native64x4.mul P.modulusLimbs P.montgomeryNegInv x y).toNat : ZMod modulus) =
      (x.toNat : ZMod modulus) * (y.toNat : ZMod modulus) *
        ((2 ^ 256 : ℕ) : ZMod modulus)⁻¹ := by
  have hmod := (mul_spec P.modulusLimbs P.montgomeryNegInv x y Mont64x4Field.negInv_mul_q
    (by rw [Mont64x4Field.q_toNat]; exact hxq)).2
  rw [Mont64x4Field.q_toNat] at hmod
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  rw [Nat.cast_mul, Nat.cast_mul] at hcast
  rw [← hcast, mul_comm ((2 ^ 256 : ℕ) : ZMod modulus), mul_assoc,
    mul_inv_cancel₀ Mont64x4Field.r_ne_zero, mul_one]

/-- The canonical value of a fast element is its residue divided by `2 ^ 256`. -/
private theorem toField_eq (x : FastField modulus) :
    toField x = (x.val.toNat : ZMod modulus) * ((2 ^ 256 : ℕ) : ZMod modulus)⁻¹ := by
  rw [toField, toNat, toLimbs4, mul_cast x.val Limbs4.one x.property, Limbs4.one_toNat]
  simp

private theorem val_cast (x : FastField modulus) :
    (x.val.toNat : ZMod modulus) = toField x * ((2 ^ 256 : ℕ) : ZMod modulus) := by
  rw [toField_eq, mul_assoc, inv_mul_cancel₀ Mont64x4Field.r_ne_zero, mul_one]

theorem toNat_lt (x : FastField modulus) : toNat x < modulus := by
  have := (mul_spec P.modulusLimbs P.montgomeryNegInv x.val Limbs4.one
    Mont64x4Field.negInv_mul_q x.val_lt).1
  rwa [Mont64x4Field.q_toNat] at this

private theorem ofCanonicalNat_val_cast {n : ℕ} (h : n < modulus) :
    ((ofCanonicalNat n h).val.toNat : ZMod modulus) =
      (n : ZMod modulus) * ((2 ^ 256 : ℕ) : ZMod modulus) := by
  have hR2 : ((((2 ^ 256) ^ 2 : ℕ) % modulus : ℕ) : ZMod modulus)
      = ((2 ^ 256 : ℕ) : ZMod modulus) * ((2 ^ 256 : ℕ) : ZMod modulus) := by
    rw [ZMod.natCast_mod, pow_two, Nat.cast_mul]
  rw [ofCanonicalNat,
    mul_cast _ _
      (by rw [Limbs4.ofNat_toNat, Nat.mod_eq_of_lt (h.trans Mont64x4Field.modulus_lt)]; exact h),
    Limbs4.ofNat_toNat, Nat.mod_eq_of_lt (h.trans Mont64x4Field.modulus_lt),
    P.r2ModModulus_toNat, hR2, mul_assoc, mul_assoc,
    mul_inv_cancel₀ Mont64x4Field.r_ne_zero, mul_one]

@[simp]
theorem toField_ofCanonicalNat {n : ℕ} (h : n < modulus) :
    toField (ofCanonicalNat n h) = (n : ZMod modulus) := by
  rw [toField_eq, ofCanonicalNat_val_cast h, mul_assoc,
    mul_inv_cancel₀ Mont64x4Field.r_ne_zero, mul_one]

@[simp]
theorem toNat_ofCanonicalNat {n : ℕ} (h : n < modulus) : toNat (ofCanonicalNat n h) = n :=
  Montgomery.natCast_inj_of_lt (toField_ofCanonicalNat h) (toNat_lt _) h

/-- Converting from the canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod modulus) : toField (ofField x) = x := by
  simp [ofField, toField_ofCanonicalNat]

/-- Converting from fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : FastField modulus) : ofField (toField x) = x := by
  apply Subtype.ext
  have hval : ((ofField (toField x)).val.toNat : ZMod modulus) = (x.val.toNat : ZMod modulus) := by
    rw [val_cast, val_cast, toField_ofField]
  have hnat : (ofField (toField x)).val.toNat = x.val.toNat :=
    Montgomery.natCast_inj_of_lt hval (ofField (toField x)).property x.property
  exact Limbs4.ext_of_toNat hnat

/-- The canonical-field interpretation distinguishes fast values. -/
theorem toField_injective : Function.Injective (toField (modulus := modulus)) :=
  Function.LeftInverse.injective ofField_toField

/-! ### Field operations -/

@[simp]
theorem toField_zero : toField (0 : FastField modulus) = 0 := by
  rw [toField_eq, zero_def, zero]
  simp [Limbs4.zero_toNat]

@[simp]
theorem toField_one : toField (1 : FastField modulus) = 1 := by
  rw [toField_eq, one_def, one]
  simp only [P.rModModulus_toNat, ZMod.natCast_mod]
  exact mul_inv_cancel₀ Mont64x4Field.r_ne_zero

@[simp]
theorem toField_add (x y : FastField modulus) : toField (x + y) = toField x + toField y := by
  rw [toField_eq, toField_eq x, toField_eq y, add_def, add]
  have h := add_toNat P.modulusLimbs x.val y.val x.val_lt y.val_lt
  rw [h, Mont64x4Field.q_toNat, ZMod.natCast_mod, Nat.cast_add]
  ring

@[simp]
theorem toField_sub (x y : FastField modulus) : toField (x - y) = toField x - toField y := by
  rw [toField_eq, toField_eq x, toField_eq y, sub_def, sub]
  have h := sub_toNat P.modulusLimbs x.val y.val x.val_lt y.val_lt
  rw [h, Mont64x4Field.q_toNat, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (le_of_lt y.property), ZMod.natCast_self]
  ring

@[simp]
theorem toField_neg (x : FastField modulus) : toField (-x) = -toField x := by
  rw [toField_eq, toField_eq x, neg_def, neg]
  have h := neg_toNat P.modulusLimbs x.val x.val_lt
  rw [h, Mont64x4Field.q_toNat, ZMod.natCast_mod, Nat.cast_sub (le_of_lt x.property),
    ZMod.natCast_self]
  ring

@[simp]
theorem toField_mul (x y : FastField modulus) : toField (x * y) = toField x * toField y := by
  rw [toField_eq, toField_eq x, toField_eq y, mul_def]
  simp only [mul, mulKernel]
  rw [mul_cast x.val y.val x.property]
  ring

private theorem mul_assoc' (x y z : FastField modulus) : x * y * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : FastField modulus) (n : ℕ) : pow x (n + 1) = pow x n * x := by
  unfold pow
  let : Semigroup (FastField modulus) := { mul, mul_assoc := mul_assoc' }
  exact npowBinRec_succ n x

@[simp]
theorem toField_square (x : FastField modulus) : toField (square x) = toField x * toField x := by
  simp only [square_def, toField_mul]

@[simp]
theorem toField_pow (x : FastField modulus) (n : ℕ) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero =>
      unfold pow
      rw [npowBinRec_zero, toField_one]
      simp
  | succ n ih => rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

/-- Fermat-style inversion in `ZMod modulus`. -/
private theorem inv_eq_pow {a : ZMod modulus} (ha : a ≠ 0) : a⁻¹ = a ^ (modulus - 2) := by
  have hcard : Fintype.card (ZMod modulus) = modulus := ZMod.card modulus
  have h1 : a ^ (modulus - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hcard] at h
    exact h
  have hmul : a * a ^ (modulus - 2) = 1 := by
    rw [← pow_succ']
    show a ^ (modulus - 2 + 1) = 1
    have hsucc : modulus - 2 + 1 = modulus - 1 := by
      have := P.two_lt_modulus
      omega
    rw [hsucc]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

@[simp]
theorem toField_inv (x : FastField modulus) : toField x⁻¹ = (toField x)⁻¹ := by
  simp only [inv_def, inv, toField_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero, zero_pow]
    have := P.two_lt_modulus
    omega
  · rw [inv_eq_pow hx]

@[simp]
theorem toField_div (x y : FastField modulus) : toField (x / y) = toField x / toField y := by
  simp only [div_def, toField_mul, toField_inv]
  rfl

@[simp]
theorem toField_natCast (n : ℕ) : toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofNat modulus n) = (n : ZMod modulus)
  rw [ofNat, toField_ofCanonicalNat, ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

@[simp]
theorem toField_intCast (n : Int) : toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofField n) = (n : ZMod modulus)
  rw [toField_ofField]

@[simp]
theorem toField_nsmul (n : ℕ) (x : FastField modulus) : toField (n • x) = n • toField x := by
  change toField ((n : FastField modulus) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

@[simp]
theorem toField_zsmul (n : Int) (x : FastField modulus) : toField (n • x) = n • toField x := by
  change toField ((n : FastField modulus) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

@[simp]
theorem toField_npow (x : FastField modulus) (n : ℕ) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

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

@[simp]
theorem toField_nnratCast (q : ℚ≥0) : toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus)) = (q : ZMod modulus)
  rw [toField_ofField]

@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus)) = (q : ZMod modulus)
  rw [toField_ofField]

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

@[simp]
theorem toField_qsmul (q : ℚ) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ### Algebraic structure -/

/-- Ring equivalence between the fast Montgomery representation and the canonical field. -/
def ringEquiv (modulus : ℕ) [P : Mont64x4Field modulus] :
    FastField modulus ≃+* ZMod modulus where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp]
theorem ringEquiv_apply {x : FastField modulus} : ringEquiv modulus x = toField x := rfl

@[simp]
theorem ringEquiv_symm_apply {x : ZMod modulus} : (ringEquiv modulus).symm x = ofField x := rfl

/-- Field instance transferred from the canonical field through `toField`. -/
instance instField : _root_.Field (FastField modulus) := by
  apply toField_injective.field toField <;> simp

private theorem toField_powTrimmedGo (n : ℕ) (a x : FastField modulus) :
    toField (powTrimmedGo n a x) = toField a * toField x ^ n := by
  induction n using Nat.strong_induction_on generalizing a x with
  | h n ih =>
    rw [powTrimmedGo]
    split
    · next hn =>
      interval_cases n <;> simp only [beq_iff_eq, ite_true, ite_false, pow_zero,
        mul_one, Nat.one_ne_zero, pow_one, ← mul_def, toField_mul]
    · next hn =>
      rw [ih (n / 2) (by omega), squareCached_eq]
      simp only [← mul_def, toField_mul]
      by_cases hb : n % 2 = 1
      · simp only [hb, beq_iff_eq, ite_true, toField_mul]
        have he : n = 1 + 2 * (n / 2) := by omega
        conv_rhs => rw [he]
        simp only [pow_add, pow_mul, pow_one, pow_two]
        ring
      · have hb0 : n % 2 = 0 := by omega
        simp only [hb0, beq_iff_eq, Nat.zero_ne_one, ite_false]
        have he : n = 2 * (n / 2) := by omega
        conv_rhs => rw [he]
        simp only [pow_mul, pow_two]

private theorem toField_powTrimmedStart (n : ℕ) (x : FastField modulus) :
    toField (powTrimmedStart n x) = toField x ^ n := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rw [powTrimmedStart]
    split
    · next hn =>
      interval_cases n <;> simp only [beq_iff_eq, ite_true, ite_false, pow_zero,
        ← one_def, toField_one, Nat.one_ne_zero, pow_one]
    · next hn =>
      by_cases hb : n % 2 = 1
      · simp only [hb, beq_iff_eq, ite_true, toField_powTrimmedGo,
          squareCached_eq, ← mul_def, toField_mul]
        have he : n = 1 + 2 * (n / 2) := by omega
        conv_rhs => rw [he]
        simp only [pow_add, pow_mul, pow_one, pow_two]
      · have hb0 : n % 2 = 0 := by omega
        simp only [hb0, beq_iff_eq, Nat.zero_ne_one, ite_false]
        rw [ih (n / 2) (by omega), squareCached_eq]
        simp only [← mul_def, toField_mul]
        have he : n = 2 * (n / 2) := by omega
        conv_rhs => rw [he]
        simp only [pow_mul, pow_two]

/-- The optimized exponentiation implements the original field power. -/
@[csimp] theorem pow_eq_powTrimmed : @pow = @powTrimmed := by
  funext modulus P x n
  apply toField_injective
  rw [toField_pow, powTrimmed, toField_powTrimmedStart]

/-- A fast four-limb field is non-binary. -/
instance instNonBinaryField : NonBinaryField (FastField modulus) where
  char_neq_2 := by
    intro h
    apply Mont64x4Field.two_ne_zero (modulus := modulus)
    calc
      _ = toField ((2 : ℕ) : FastField modulus) := (toField_natCast 2).symm
      _ = toField (0 : FastField modulus) := congrArg toField h
      _ = 0 := toField_zero

end Bridge

end FastField

end

end Native64x4
end Montgomery
