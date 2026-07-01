/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.Montgomery.Native256
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.Finite.Basic

/-!
# Native 256-bit Montgomery field — operations and `Field` instance

The field layer over `Montgomery.Native256` (the analogue of `Montgomery.Native32Field` for
four-`UInt64`-limb fields): the `toField`/`ofField` bridge to the canonical `ZMod p` model, the
native-word operations (`add`/`neg`/`sub`/`mul`/`square`/`pow`/the 4-bit window `inv`/`div`),
their `Zero`/`One`/`Add`/`Mul`/… instances, the `toField_*` preservation lemmas, the transferred
`Field`/`CommRing`/`NonBinaryField` instances, and `ringEquiv : FastField F ≃+* ZMod p`.
-/

set_option maxRecDepth 4000

namespace Montgomery
namespace Native256

variable {F : Type} [P : Mont256Field F]

/-! ## Generic field facts -/

/-- `2^256` is a unit in `ZMod p` (an odd prime cannot divide a power of two). -/
theorem r256_ne_zero : ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact Mont256Field.two_ne_zero_in_field (F := F)
    ((ZMod.natCast_eq_zero_iff _ _).mpr (P.prime.out.dvd_of_dvd_pow hdvd))

/-- The field has more than two elements (characteristic `≠ 2` for a prime field). -/
theorem two_lt_fieldSize : 2 < Mont256Field.fieldSize F := by
  have h2 : Mont256Field.fieldSize F ≠ 2 := by
    intro h
    apply Mont256Field.two_ne_zero_in_field (F := F)
    rw [← h]; exact ZMod.natCast_self _
  have := P.prime.out.two_le
  omega

/-! ## `toField` bridge (exiting Montgomery form) -/

/-- The raw 256-bit word for the integer `1` (NOT the Montgomery one `R`). -/
def oneRaw : UInt256L := ⟨1, 0, 0, 0⟩

@[simp] theorem oneRaw_toNat : oneRaw.toNat = 1 := by decide

/-- Exit Montgomery form: the canonical native-word representative of `x`. -/
@[inline]
def toCanonicalUInt256L (x : FastField F) : UInt256L := montgomeryMul (F := F) x.val oneRaw

/-- The canonical natural representative of a fast element. -/
@[inline]
def toNat (x : FastField F) : Nat := (toCanonicalUInt256L x).toNat

/-- Interpret a fast element in the canonical `ZMod p` field. -/
@[inline]
def toField (x : FastField F) : ZMod (Mont256Field.fieldSize F) :=
  (toNat x : ZMod (Mont256Field.fieldSize F))

theorem toNat_lt_fieldSize (x : FastField F) : toNat x < Mont256Field.fieldSize F :=
  (montgomeryMul_spec (F := F) x.val oneRaw x.property).1

/-- `toField` is the Montgomery interpretation: the stored word times `(2²⁵⁶)⁻¹`. -/
theorem toField_eq_raw_mul_inv (x : FastField F) :
    toField x = (x.val.toNat : ZMod (Mont256Field.fieldSize F))
      * ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ := by
  have h := (montgomeryMul_spec (F := F) x.val oneRaw x.property).2
  unfold toField toNat toCanonicalUInt256L
  rw [h, oneRaw_toNat]
  simp only [Nat.cast_one, mul_one]

/-- The stored word equals `toField x · 2²⁵⁶` in `ZMod p`. -/
theorem raw_cast_eq_toField_mul (x : FastField F) :
    (x.val.toNat : ZMod (Mont256Field.fieldSize F))
      = toField x * ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F)) := by
  rw [toField_eq_raw_mul_inv, mul_assoc, inv_mul_cancel₀ r256_ne_zero, mul_one]

/-- Two naturals below `p` with equal `ZMod p` casts are equal. -/
theorem nat_eq_of_field_eq {a b : Nat} (ha : a < Mont256Field.fieldSize F)
    (hb : b < Mont256Field.fieldSize F)
    (h : (a : ZMod (Mont256Field.fieldSize F)) = (b : ZMod (Mont256Field.fieldSize F))) : a = b :=
  Montgomery.natCast_inj ha hb h

/-! ## `ofField` (entering Montgomery form) and the round trips -/

/-- Build a fast element from a canonical natural representative `n < p`. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < Mont256Field.fieldSize F) : FastField F :=
  ⟨montgomeryMul (F := F) (UInt256L.ofNat n) P.r2ModModulus, by
    have hlt : (UInt256L.ofNat n).toNat < Mont256Field.fieldSize F := by
      rw [UInt256L.toNat_ofNat n (by have := fieldSize_lt_two256 (F := F); omega)]
      exact h
    exact (montgomeryMul_spec (F := F) (UInt256L.ofNat n) P.r2ModModulus hlt).1⟩

/-- The stored word of `ofCanonicalNat n` is the Montgomery residue `n · 2²⁵⁶` in `ZMod p`. -/
theorem ofCanonicalNat_raw_cast (n : Nat) (h : n < Mont256Field.fieldSize F) :
    ((ofCanonicalNat n h).val.toNat : ZMod (Mont256Field.fieldSize F))
      = (n : ZMod (Mont256Field.fieldSize F))
        * ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F)) := by
  have hn : n < 2 ^ 256 := by have := fieldSize_lt_two256 (F := F); omega
  have hlt : (UInt256L.ofNat n).toNat < Mont256Field.fieldSize F := by
    rw [UInt256L.toNat_ofNat n hn]; exact h
  have hspec := (montgomeryMul_spec (F := F) (UInt256L.ofNat n) P.r2ModModulus hlt).2
  change ((montgomeryMul (F := F) (UInt256L.ofNat n) P.r2ModModulus).toNat :
      ZMod (Mont256Field.fieldSize F)) = _
  rw [hspec, UInt256L.toNat_ofNat n hn, P.r2ModModulus_cast, mul_assoc, pow_two,
    mul_assoc ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F)), mul_inv_cancel₀ r256_ne_zero,
    mul_one]

/-- `toField` recovers the canonical representative fed to `ofCanonicalNat`. -/
@[simp]
theorem toField_ofCanonicalNat (n : Nat) (h : n < Mont256Field.fieldSize F) :
    toField (ofCanonicalNat n h) = (n : ZMod (Mont256Field.fieldSize F)) := by
  rw [toField_eq_raw_mul_inv, ofCanonicalNat_raw_cast, mul_assoc, mul_inv_cancel₀ r256_ne_zero,
    mul_one]

/-- Convert from the canonical `ZMod p` field into fast Montgomery form. -/
@[inline]
def ofField (x : ZMod (Mont256Field.fieldSize F)) : FastField F :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert a natural number into fast Montgomery form (reducing modulo `p` first). -/
@[inline]
def ofNat (n : Nat) : FastField F :=
  ofCanonicalNat (n % Mont256Field.fieldSize F) (Nat.mod_lt _ P.prime.out.pos)

/-- Convert an integer into fast Montgomery form. -/
@[inline]
def ofInt (n : Int) : FastField F := ofField (n : ZMod (Mont256Field.fieldSize F))

/-- Canonical field → fast form → canonical field is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod (Mont256Field.fieldSize F)) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Fast form → canonical field → fast form is the identity. -/
@[simp]
theorem ofField_toField (x : FastField F) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt256L.toNat_inj.mp
  apply nat_eq_of_field_eq (ofField (toField x)).property x.property
  rw [raw_cast_eq_toField_mul, toField_ofField, raw_cast_eq_toField_mul]

/-- `toField` is injective: the gateway lemma for the `Field` transfer. -/
theorem toField_injective : Function.Injective (toField (F := F)) :=
  Function.LeftInverse.injective ofField_toField

/-! ## Field operations -/

/-- Fast modular addition in Montgomery form. The sum `x + y < 2·p` may reach `2²⁵⁶` (when
`2·p ≥ 2²⁵⁶`), so the carry-out is captured and reduced by `reduceWide`. -/
@[inline]
def add (x y : FastField F) : FastField F :=
  reduceWide (F := F) (UInt256L.addCarryOut x.val y.val 0).1
    (UInt256L.addCarryOut x.val y.val 0).2
    (UInt256L.toNat_addCarryOut x.val y.val 0 (by decide)).2
    (by
      rw [(UInt256L.toNat_addCarryOut x.val y.val 0 (by decide)).1,
        show (0 : UInt64).toNat = 0 from rfl]
      have hx := x.property; have hy := y.property
      omega)

/-- Fast zero in Montgomery form. -/
def zero : FastField F := ⟨0, by
  have h0 : (0 : UInt256L).toNat = 0 := by decide
  rw [h0]; exact P.prime.out.pos⟩

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : FastField F) : FastField F :=
  if hx : x.val = 0 then
    zero
  else
    ⟨P.modulus - x.val, by
      have hle : x.val.toNat ≤ P.modulus.toNat := by
        rw [P.modulus_toNat]; exact Nat.le_of_lt x.property
      rw [UInt256L.toNat_sub_of_le hle, P.modulus_toNat]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt256L.toNat_inj.mp
        simpa using hzero
      have := x.property; omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : FastField F) : FastField F :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt256L.le_iff_toNat_le] at hyx
      rw [UInt256L.toNat_sub_of_le hyx]
      have := x.property; omega⟩
  else
    ⟨x.val + (P.modulus - y.val), by
      have hb := x.property; have hyb := y.property
      have hm := P.modulus_toNat; have hp := fieldSize_lt_two256 (F := F)
      rw [UInt256L.le_iff_toNat_le] at hyx
      have hyle : y.val.toNat ≤ P.modulus.toNat := by rw [hm]; omega
      rw [UInt256L.toNat_add, UInt256L.toNat_sub_of_le hyle, hm, Nat.mod_eq_of_lt (by omega)]
      omega⟩

/-- Fast one in Montgomery form (the residue `R mod p`). -/
def one : FastField F := ⟨P.rModModulus, P.rModModulus_lt_fieldSize⟩

/-- Fast modular multiplication in Montgomery form (CIOS Montgomery product). -/
@[inline]
def mul (x y : FastField F) : FastField F :=
  ⟨montgomeryMul (F := F) x.val y.val, (montgomeryMul_spec (F := F) x.val y.val x.property).1⟩

/-- Fast squaring. -/
@[inline]
def square (x : FastField F) : FastField F := mul x x

/-- Exponentiation by binary repeated squaring over the fast representation. -/
@[specialize]
def pow (x : FastField F) (n : Nat) : FastField F :=
  @npowBinRec (FastField F) ⟨one⟩ ⟨mul⟩ n x

/-- Shared 4-bit window table builder: `[s, s*x, ..., s*x^(n-1)]` (`n` entries, one multiply
each, threaded through `s`). -/
@[specialize]
def tableAux (x : FastField F) : Nat → FastField F → List (FastField F)
  | 0, _ => []
  | n + 1, cur => cur :: tableAux x n (mul cur x)

/-- The 4-bit window table `[x^0, ..., x^15]`, precomputed once with 15 multiplications. -/
def windowTable (x : FastField F) : List (FastField F) := tableAux x 16 one

/-- Fermat exponent used for inversion in the prime field (`x⁻¹ = x^(p-2)`). -/
def invExponent : Nat := Mont256Field.fieldSize F - 2

/-- The base-16 digits of `p-2`, most significant first (64 nibbles). -/
def p2HexDigits : List Nat :=
  (List.range 64).map (fun i => (invExponent (F := F) >>> ((63 - i) * 4)) &&& 0xF)

/-- `x^16` by four explicit squarings. -/
@[inline]
def sq4 (acc : FastField F) : FastField F := square (square (square (square acc)))

/-- The window table as an `Array`, for O(1) digit lookup during inversion. -/
@[inline]
def windowTableArr (x : FastField F) : Array (FastField F) := (windowTable x).toArray

/-- One window step: four squarings, then a table multiply unless the digit is `0`. -/
@[inline]
def windowStep (tbl : Array (FastField F)) (acc : FastField F) (d : Nat) : FastField F :=
  if d = 0 then sq4 acc else mul (sq4 acc) (tbl.getD d one)

/-- Base-16 Horner exponentiation to the fixed exponent `p-2` against a precomputed table. -/
def invFold (tbl : Array (FastField F)) : FastField F :=
  (p2HexDigits (F := F)).tail.foldl (windowStep tbl)
    (tbl.getD ((p2HexDigits (F := F)).headD 0) one)

/-- Inversion in Montgomery form via Fermat's little theorem, evaluated by fixed 4-bit window
exponentiation over the precomputed digits of `p-2`. -/
@[inline]
def inv (x : FastField F) : FastField F := invFold (windowTableArr x)

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : FastField F) : FastField F := mul x (inv y)

instance instZero : Zero (FastField F) where zero := zero
instance instOne : One (FastField F) where one := one
instance instAdd : Add (FastField F) where add := add
instance instNeg : Neg (FastField F) where neg := neg
instance instSub : Sub (FastField F) where sub := sub
instance instMul : Mul (FastField F) where mul := mul
instance instInv : Inv (FastField F) where inv := inv
instance instDiv : Div (FastField F) where div := div
instance instNatCast : NatCast (FastField F) where natCast := ofNat
instance instIntCast : IntCast (FastField F) where intCast := ofInt
instance instNatSMul : SMul Nat (FastField F) where smul n x := ofNat n * x
instance instIntSMul : SMul Int (FastField F) where smul n x := ofInt n * x
instance instPowNat : Pow (FastField F) Nat where pow := pow
instance instPowInt : Pow (FastField F) Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)
instance instNNRatCast : NNRatCast (FastField F) where
  nnratCast q := ofField (q : ZMod (Mont256Field.fieldSize F))
instance instRatCast : RatCast (FastField F) where
  ratCast q := ofField (q : ZMod (Mont256Field.fieldSize F))
instance instNNRatSMul : SMul ℚ≥0 (FastField F) where smul q x := ofField (q • toField x)
instance instRatSMul : SMul ℚ (FastField F) where smul q x := ofField (q • toField x)

/-! ## Operation-preservation lemmas -/

theorem inv_eq_pow_field (a : ZMod (Mont256Field.fieldSize F)) (ha : a ≠ 0) :
    a⁻¹ = a ^ (Mont256Field.fieldSize F - 2) := by
  have h1 : a ^ (Mont256Field.fieldSize F - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hmul : a * a ^ (Mont256Field.fieldSize F - 2) = 1 := by
    have h2 := P.prime.out.two_le
    rw [← pow_succ',
      show Mont256Field.fieldSize F - 2 + 1 = Mont256Field.fieldSize F - 1 from by omega]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

@[simp]
theorem toField_zero : toField (0 : FastField F) = 0 := by
  have h0 : (0 : FastField F).val.toNat = 0 := by show (0 : UInt256L).toNat = 0; decide
  rw [toField_eq_raw_mul_inv, h0, Nat.cast_zero, zero_mul]

@[simp]
theorem toField_one : toField (1 : FastField F) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (P.rModModulus.toNat : ZMod (Mont256Field.fieldSize F))
    * ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ = 1
  rw [P.rModModulus_cast]
  exact mul_inv_cancel₀ r256_ne_zero

@[simp]
theorem toField_add (x y : FastField F) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv (x + y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  obtain ⟨hsc, hscb⟩ := UInt256L.toNat_addCarryOut x.val y.val 0 (by decide)
  have hbnd : (UInt256L.addCarryOut x.val y.val 0).1.toNat
      + (UInt256L.addCarryOut x.val y.val 0).2.toNat * 2 ^ 256
      < 2 * Mont256Field.fieldSize F := by
    rw [hsc, show (0 : UInt64).toNat = 0 from rfl]
    have := x.property; have := y.property; omega
  show ((reduceWideRaw (F := F) (UInt256L.addCarryOut x.val y.val 0).1
        (UInt256L.addCarryOut x.val y.val 0).2).toNat : ZMod (Mont256Field.fieldSize F))
      * ((2 ^ 256 : Nat) : ZMod (Mont256Field.fieldSize F))⁻¹ = _
  rw [reduceWideRaw_cast _ _ hscb hbnd, hsc, show (0 : UInt64).toNat = 0 from rfl,
    Nat.add_zero, Nat.cast_add]
  ring

private theorem modulus_cast_zero : (P.modulus.toNat : ZMod (Mont256Field.fieldSize F)) = 0 := by
  rw [P.modulus_toNat]; exact ZMod.natCast_self (Mont256Field.fieldSize F)

@[simp]
theorem toField_neg (x : FastField F) : toField (-x) = -toField x := by
  rw [toField_eq_raw_mul_inv (-x), toField_eq_raw_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegN : (-x : FastField F).val.toNat = 0 := by
      show (neg x).val.toNat = 0; unfold neg; rw [dif_pos hx]
      show (0 : UInt256L).toNat = 0; decide
    have hxN : x.val.toNat = 0 := by rw [hx]; decide
    rw [hnegN, hxN]; simp
  · have hle : x.val.toNat ≤ P.modulus.toNat := by
      rw [P.modulus_toNat]; exact Nat.le_of_lt x.property
    have hnegval : (-x : FastField F).val = P.modulus - x.val := by
      show (neg x).val = _; unfold neg; rw [dif_neg hx]
    rw [hnegval, UInt256L.toNat_sub_of_le hle, Nat.cast_sub hle, modulus_cast_zero]
    ring

@[simp]
theorem toField_sub (x y : FastField F) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_raw_mul_inv (x - y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hyxN : y.val.toNat ≤ x.val.toNat := (UInt256L.le_iff_toNat_le).mp hyx
    have hsubval : (x - y : FastField F).val = x.val - y.val := by
      show (sub x y).val = _; unfold sub; rw [dif_pos hyx]
    rw [hsubval, UInt256L.toNat_sub_of_le hyxN, Nat.cast_sub hyxN]
    ring
  · have hb := x.property; have hyb := y.property
    have hm := P.modulus_toNat; have hp := fieldSize_lt_two256 (F := F)
    have hxy : x.val.toNat < y.val.toNat := by rw [UInt256L.le_iff_toNat_le] at hyx; omega
    have hyle : y.val.toNat ≤ P.modulus.toNat := by rw [hm]; omega
    have htval : (P.modulus - y.val).toNat = P.modulus.toNat - y.val.toNat :=
      UInt256L.toNat_sub_of_le hyle
    have hsubval : (x - y : FastField F).val = x.val + (P.modulus - y.val) := by
      show (sub x y).val = _; unfold sub; rw [dif_neg hyx]
    rw [hsubval, UInt256L.toNat_add, htval, hm, Nat.mod_eq_of_lt (by omega),
      Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hyb), ZMod.natCast_self]
    ring

@[simp]
theorem toField_mul (x y : FastField F) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv (x * y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  have hval : (x * y).val = montgomeryMul (F := F) x.val y.val := rfl
  rw [hval, (montgomeryMul_spec (F := F) x.val y.val x.property).2]
  ring

def ringEquiv : FastField F ≃+* ZMod (Mont256Field.fieldSize F) where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp] theorem ringEquiv_apply (x : FastField F) : ringEquiv x = toField x := rfl
@[simp] theorem ringEquiv_symm_apply (x : ZMod (Mont256Field.fieldSize F)) :
    ringEquiv.symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : FastField F) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]; ring

private theorem pow_succ_field (x : FastField F) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup (FastField F) := { mul := (· * ·), mul_assoc := mul_assoc_field }
  exact npowBinRec_succ n x

@[simp]
theorem toField_square (x : FastField F) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

@[simp]
theorem toField_pow (x : FastField F) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero => unfold pow; rw [npowBinRec_zero, toField_one]; simp
  | succ n ih => rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

private theorem toField_mul_raw (x y : FastField F) :
    toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

private theorem tableAux_toField (x : FastField F) (n : Nat) :
    ∀ (s : FastField F) (d : Nat), d < n →
      toField ((tableAux x n s).getD d one) = toField s * toField x ^ d := by
  induction n with
  | zero => intro s d hd; omega
  | succ n ih =>
    intro s d hd
    cases d with
    | zero => simp only [tableAux, List.getD_cons_zero, pow_zero, mul_one]
    | succ d =>
      simp only [tableAux, List.getD_cons_succ]
      rw [ih (mul s x) d (by omega), toField_mul_raw, pow_succ]; ring

private theorem windowTable_toField (x : FastField F) :
    ∀ d, d < 16 → toField ((windowTable x).getD d one) = toField x ^ d := by
  intro d hd
  have h1 : toField (one : FastField F) = 1 := toField_one
  rw [windowTable, tableAux_toField x 16 one d hd, h1, one_mul]

private theorem toField_sq4 (acc : FastField F) : toField (sq4 acc) = toField acc ^ 16 := by
  unfold sq4; simp only [toField_square]; ring

private theorem windowTableArr_toField (x : FastField F) :
    ∀ d, d < 16 → toField ((windowTableArr x).getD d one) = toField x ^ d := by
  intro d hd
  rw [windowTableArr]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  exact windowTable_toField x d hd

private theorem windowFold_toField (x : FastField F) (tbl : Array (FastField F))
    (htbl : ∀ d, d < 16 → toField (tbl.getD d one) = toField x ^ d) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 16) → ∀ (acc : FastField F) (E : Nat),
      toField acc = toField x ^ E →
        toField (ds.foldl (windowStep tbl) acc)
          = toField x ^ (ds.foldl (fun n d => n * 16 + d) E) := by
  intro ds
  induction ds with
  | nil => intro _ acc E hacc; simpa using hacc
  | cons d ds ih =>
    intro hds acc E hacc
    simp only [List.foldl_cons]
    apply ih (fun d' hd' => hds d' (List.mem_cons_of_mem _ hd'))
    have hd : d < 16 := hds d (List.mem_cons_self ..)
    unfold windowStep
    by_cases h0 : d = 0
    · rw [if_pos h0, toField_sq4, hacc, ← pow_mul]; congr 1; omega
    · rw [if_neg h0, toField_mul_raw, toField_sq4, hacc, htbl d hd, ← pow_mul, ← pow_add]

private theorem p2HexDigits_tail_lt : ∀ d ∈ (p2HexDigits (F := F)).tail, d < 16 := by
  intro d hd
  have hmem : d ∈ p2HexDigits (F := F) := List.mem_of_mem_tail hd
  rw [p2HexDigits, List.mem_map] at hmem
  obtain ⟨i, _, rfl⟩ := hmem
  exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

private theorem p2HexDigits_head_lt : (p2HexDigits (F := F)).headD 0 < 16 := by
  rcases hl : p2HexDigits (F := F) with _ | ⟨a, t⟩
  · simp
  · have hmem : a ∈ p2HexDigits (F := F) := by rw [hl]; exact List.mem_cons_self ..
    rw [p2HexDigits, List.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    rw [List.headD_cons, ← hi]
    exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

private theorem p2HexDigits_reconstruct :
    (p2HexDigits (F := F)).tail.foldl (fun n d => n * 16 + d) ((p2HexDigits (F := F)).headD 0)
      = invExponent (F := F) := by
  unfold p2HexDigits invExponent
  exact P.p2HexDigits_reconstruct

private theorem toField_invFold (x : FastField F) (tbl : Array (FastField F))
    (htbl : ∀ d, d < 16 → toField (tbl.getD d one) = toField x ^ d) :
    toField (invFold tbl) = toField x ^ invExponent (F := F) := by
  unfold invFold
  rw [windowFold_toField x tbl htbl (p2HexDigits (F := F)).tail p2HexDigits_tail_lt
        (tbl.getD ((p2HexDigits (F := F)).headD 0) one) ((p2HexDigits (F := F)).headD 0)
        (htbl _ p2HexDigits_head_lt),
      p2HexDigits_reconstruct]

private theorem toField_inv_pow (x : FastField F) :
    toField (inv x) = toField x ^ invExponent (F := F) := by
  unfold inv; exact toField_invFold x (windowTableArr x) (windowTableArr_toField x)

private theorem toField_inv_raw (x : FastField F) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero]
    refine zero_pow ?_
    show Mont256Field.fieldSize F - 2 ≠ 0
    have := two_lt_fieldSize (F := F); omega
  · simpa [invExponent] using (inv_eq_pow_field (toField x) hx).symm

@[simp]
theorem toField_inv (x : FastField F) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_div_mul_inv (x y : FastField F) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div; exact toField_mul_raw x (inv y)

@[simp]
theorem toField_div (x y : FastField F) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : ZMod (Mont256Field.fieldSize F), c = b⁻¹ → a * c = a / b := by
    intro a b c hc; rw [hc]; rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

@[simp]
theorem toField_natCast (n : Nat) :
    toField (n : FastField F) = (n : ZMod (Mont256Field.fieldSize F)) := by
  change toField (ofNat n) = (n : ZMod (Mont256Field.fieldSize F))
  unfold ofNat
  rw [toField_ofCanonicalNat, ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

@[simp]
theorem toField_intCast (n : Int) :
    toField (n : FastField F) = (n : ZMod (Mont256Field.fieldSize F)) := by
  change toField (ofInt n) = (n : ZMod (Mont256Field.fieldSize F))
  unfold ofInt; rw [toField_ofField]

@[simp]
theorem toField_nsmul (n : Nat) (x : FastField F) : toField (n • x) = n • toField x := by
  change toField ((n : FastField F) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

@[simp]
theorem toField_zsmul (n : Int) (x : FastField F) : toField (n • x) = n • toField x := by
  change toField ((n : FastField F) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

@[simp]
theorem toField_npow (x : FastField F) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

@[simp]
theorem toField_zpow (x : FastField F) (n : Int) : toField (x ^ n) = toField x ^ n := by
  cases n with
  | ofNat n =>
      change toField (pow x n) = toField x ^ (Int.ofNat n)
      rw [toField_pow]; exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := by
        change toField x⁻¹ = (toField x)⁻¹; rw [toField_inv]
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

@[simp]
theorem toField_nnratCast (q : ℚ≥0) :
    toField (q : FastField F) = (q : ZMod (Mont256Field.fieldSize F)) := by
  change toField (ofField (q : ZMod (Mont256Field.fieldSize F)))
    = (q : ZMod (Mont256Field.fieldSize F))
  rw [toField_ofField]

@[simp]
theorem toField_ratCast (q : ℚ) :
    toField (q : FastField F) = (q : ZMod (Mont256Field.fieldSize F)) := by
  change toField (ofField (q : ZMod (Mont256Field.fieldSize F)))
    = (q : ZMod (Mont256Field.fieldSize F))
  rw [toField_ofField]

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : FastField F) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

@[simp]
theorem toField_qsmul (q : ℚ) (x : FastField F) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ## Transferred instances -/

instance (priority := low) instField : _root_.Field (FastField F) :=
  toField_injective.field toField
    toField_zero toField_one toField_add toField_mul toField_neg toField_sub
    toField_inv toField_div toField_nsmul toField_zsmul toField_nnqsmul toField_qsmul
    toField_npow toField_zpow toField_natCast toField_intCast toField_nnratCast toField_ratCast

instance (priority := low) instCommRing : CommRing (FastField F) := by infer_instance

instance (priority := low) instNonBinaryField : NonBinaryField (FastField F) where
  char_neq_2 := by
    change ((2 : Nat) : FastField F) ≠ 0
    intro h
    exact Mont256Field.two_ne_zero_in_field (F := F) (by
      calc ((2 : Nat) : ZMod (Mont256Field.fieldSize F))
          = toField ((2 : Nat) : FastField F) := (toField_natCast 2).symm
        _ = toField (0 : FastField F) := congrArg toField h
        _ = 0 := toField_zero)

end Native256
end Montgomery
