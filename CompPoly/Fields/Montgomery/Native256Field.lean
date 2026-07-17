/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Basic
import CompPoly.Fields.Montgomery.Native256
import CompPoly.Fields.Montgomery.Native256Gcd
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fast 256-bit Montgomery Fields

The bounded carrier's conversions, arithmetic, and field instances built on the
`Montgomery.Native256` CIOS core. Inversion runs the proof-free Pornin binary GCD
(`gcdInvCandidate`) and verifies the candidate with one proven Montgomery multiplication,
falling back to the proven 4-bit-window Fermat exponentiation, so correctness never depends
on the GCD internals.
-/

set_option maxRecDepth 4000

namespace Montgomery
namespace Native256

variable {modulus : ℕ} [P : Mont256Field modulus]

/-! ## Conversions -/

/-- The raw 256-bit word for the integer `1` (NOT the Montgomery one `R`). -/
def oneRaw : UInt256L := ⟨1, 0, 0, 0⟩

@[simp] theorem oneRaw_toNat : oneRaw.toNat = 1 := by decide

namespace FastField

/-- Exit Montgomery form: the canonical native-word representative of `x`. -/
@[inline]
def toUInt256L (x : FastField modulus) : UInt256L :=
  montgomeryMul (modulus := modulus) x.val oneRaw

/-- The canonical natural representative of a fast element. -/
@[inline]
def toNat (x : FastField modulus) : ℕ := x.toUInt256L.toNat

/-- Interpret a fast element in the canonical `ZMod modulus` field. -/
@[inline]
def toField (x : FastField modulus) : ZMod modulus := (x.toNat : ZMod modulus)

/-- Build a fast element from a canonical natural representative `n < modulus`. -/
@[inline]
def ofCanonicalNat (n : ℕ) (h : n < modulus) : FastField modulus :=
  .mk (montgomeryMul (modulus := modulus) (UInt256L.ofNat n) P.r2ModModulus) <| by
    have hlt : (UInt256L.ofNat n).toNat < modulus := by
      rw [UInt256L.toNat_ofNat n (by have := P.modulus_lt_two_pow_256; omega)]
      exact h
    exact (montgomeryMul_spec (modulus := modulus) (UInt256L.ofNat n) P.r2ModModulus hlt).1

/-- Convert from the canonical `ZMod modulus` field into fast Montgomery form. -/
@[inline]
def ofField (x : ZMod modulus) : FastField modulus :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert a natural number into fast Montgomery form (reducing modulo `modulus` first). -/
@[inline]
def ofNat (modulus : ℕ) [P : Mont256Field modulus] (n : ℕ) : FastField modulus :=
  ofCanonicalNat (n % modulus) (Nat.mod_lt _ P.modulus_pos)

/-- Convert an integer into fast Montgomery form. -/
@[inline]
private def ofInt (modulus : ℕ) [P : Mont256Field modulus] (n : Int) : FastField modulus :=
  ofField (n : ZMod modulus)

end FastField

open FastField

/-! ## Correctness of the bridge -/

theorem toNat_lt_modulus {x : FastField modulus} : toNat x < modulus :=
  (montgomeryMul_spec (modulus := modulus) x.val oneRaw x.property).1

/-- `toField` is the Montgomery interpretation: the stored word times `(2²⁵⁶)⁻¹`. -/
private theorem toField_eq_val_toNat_cast_mul_inv (x : FastField modulus) :
    toField x = (x.val.toNat : ZMod modulus)
      * ((2 ^ 256 : ℕ) : ZMod modulus)⁻¹ := by
  have h := (montgomeryMul_spec (modulus := modulus) x.val oneRaw x.property).2
  unfold toField toNat toUInt256L
  rw [h, oneRaw_toNat]
  simp only [Nat.cast_one, mul_one]

/-- The stored word equals `toField x · 2²⁵⁶` in `ZMod modulus`. -/
private theorem val_toNat_cast_eq_toField_mul (x : FastField modulus) :
    (x.val.toNat : ZMod modulus)
      = toField x * ((2 ^ 256 : ℕ) : ZMod modulus) := by
  rw [toField_eq_val_toNat_cast_mul_inv, mul_assoc, inv_mul_cancel₀ P.two_pow_256_ne_zero,
    mul_one]

/-- The stored word of `ofCanonicalNat n` is the Montgomery residue `n · 2²⁵⁶`. -/
private theorem ofCanonicalNat_val_toNat_cast (n : ℕ) (h : n < modulus) :
    ((ofCanonicalNat n h).val.toNat : ZMod modulus)
      = (n : ZMod modulus)
        * ((2 ^ 256 : ℕ) : ZMod modulus) := by
  have hn : n < 2 ^ 256 := by have := P.modulus_lt_two_pow_256; omega
  have hlt : (UInt256L.ofNat n).toNat < modulus := by
    rw [UInt256L.toNat_ofNat n hn]; exact h
  have hspec := (montgomeryMul_spec (modulus := modulus) (UInt256L.ofNat n) P.r2ModModulus hlt).2
  change ((montgomeryMul (modulus := modulus) (UInt256L.ofNat n) P.r2ModModulus).toNat :
      ZMod modulus) = _
  rw [hspec, UInt256L.toNat_ofNat n hn, P.r2ModModulus_cast, mul_assoc, pow_two,
    mul_assoc ((2 ^ 256 : ℕ) : ZMod modulus), mul_inv_cancel₀ P.two_pow_256_ne_zero,
    mul_one]

/-- `toField` recovers the canonical representative fed to `ofCanonicalNat`. -/
@[simp]
theorem toField_ofCanonicalNat (n : ℕ) (h : n < modulus) :
    toField (ofCanonicalNat n h) = (n : ZMod modulus) := by
  rw [toField_eq_val_toNat_cast_mul_inv, ofCanonicalNat_val_toNat_cast, mul_assoc,
    mul_inv_cancel₀ P.two_pow_256_ne_zero, mul_one]

/-- Canonical field to fast form and back is the identity. -/
@[simp]
theorem toField_ofField (x : ZMod modulus) : toField (ofField x) = x := by
  unfold ofField
  rw [toField_ofCanonicalNat]
  exact ZMod.natCast_zmod_val x

/-- Fast form to the canonical field and back is the identity. -/
@[simp]
theorem ofField_toField (x : FastField modulus) : ofField (toField x) = x := by
  apply Subtype.ext
  apply UInt256L.toNat_inj.mp
  refine Montgomery.natCast_inj_of_lt ?_ (ofField (toField x)).property x.property
  rw [val_toNat_cast_eq_toField_mul, toField_ofField, val_toNat_cast_eq_toField_mul]

/-- `toField` is injective: the gateway lemma for the `Field` transfer. -/
theorem toField_injective : Function.Injective (toField (modulus := modulus)) :=
  Function.LeftInverse.injective ofField_toField

/-! ## Field operations -/

/-- Fast modular addition in Montgomery form. The sum `x + y < 2·p` may reach `2²⁵⁶` (when
`2·p ≥ 2²⁵⁶`), so the carry-out is captured and reduced by `reduceWide`. -/
@[inline]
def add (x y : FastField modulus) : FastField modulus :=
  reduceWide (modulus := modulus) (UInt256L.addCarryOut x.val y.val 0).1
    (UInt256L.addCarryOut x.val y.val 0).2
    (UInt256L.toNat_addCarryOut x.val y.val 0 (by decide)).2
    (by
      rw [(UInt256L.toNat_addCarryOut x.val y.val 0 (by decide)).1,
        show (0 : UInt64).toNat = 0 from rfl]
      have hx := x.property; have hy := y.property
      omega)

/-- Fast zero in Montgomery form. -/
def zero (modulus : ℕ) [P : Mont256Field modulus] : FastField modulus := .mk 0 <| by
  have h0 : (0 : UInt256L).toNat = 0 := by decide
  rw [h0]; exact P.modulus_pos

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : FastField modulus) : FastField modulus :=
  if hx : x.val = 0 then
    zero modulus
  else
    ⟨P.modulus256 - x.val, by
      have hle : x.val.toNat ≤ P.modulus256.toNat := by
        rw [P.modulus256_toNat]; exact Nat.le_of_lt x.property
      rw [UInt256L.toNat_sub_of_le hle, P.modulus256_toNat]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt256L.toNat_inj.mp
        simpa using hzero
      have := x.property; omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : FastField modulus) : FastField modulus :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt256L.le_iff_toNat_le] at hyx
      rw [UInt256L.toNat_sub_of_le hyx]
      have := x.property; omega⟩
  else
    ⟨x.val + (P.modulus256 - y.val), by
      have hb := x.property; have hyb := y.property
      have hm := P.modulus256_toNat; have hp := P.modulus_lt_two_pow_256
      rw [UInt256L.le_iff_toNat_le] at hyx
      have hyle : y.val.toNat ≤ P.modulus256.toNat := by rw [hm]; omega
      rw [UInt256L.toNat_add, UInt256L.toNat_sub_of_le hyle, hm, Nat.mod_eq_of_lt (by omega)]
      omega⟩

/-- Fast one in Montgomery form (the residue `R mod modulus`). -/
def one (modulus : ℕ) [P : Mont256Field modulus] : FastField modulus :=
  .mk P.rModModulus P.rModModulus_lt_modulus

/-- Fast modular multiplication in Montgomery form (CIOS Montgomery product). -/
@[inline]
def mul (x y : FastField modulus) : FastField modulus :=
  .mk (montgomeryMul (modulus := modulus) x.val y.val)
    (montgomeryMul_spec (modulus := modulus) x.val y.val x.property).1

/-- Fast squaring. -/
@[inline]
def square (x : FastField modulus) : FastField modulus := mul x x

/-- Exponentiation by binary repeated squaring over the fast representation. -/
@[specialize]
def pow (x : FastField modulus) (n : ℕ) : FastField modulus :=
  @npowBinRec (FastField modulus) ⟨one modulus⟩ ⟨mul⟩ n x

/-- Shared 4-bit window table builder: `[s, s*x, ..., s*x^(n-1)]` (`n` entries, one multiply
each, threaded through `s`). -/
@[specialize]
private def tableAux (x : FastField modulus) : ℕ → FastField modulus → List (FastField modulus)
  | 0, _ => []
  | n + 1, cur => cur :: tableAux x n (mul cur x)

/-- The 4-bit window table `[x^0, ..., x^15]`, precomputed once with 15 multiplications. -/
private def windowTable (x : FastField modulus) : List (FastField modulus) :=
  tableAux x 16 (one modulus)

/-- The base-16 digits of `modulus - 2`, most significant first (64 nibbles). -/
private def p2HexDigits (modulus : ℕ) : List ℕ :=
  (List.range 64).map (fun i => ((modulus - 2) >>> ((63 - i) * 4)) &&& 0xF)

/-- `x^16` by four explicit squarings. -/
@[inline]
private def sq4 (acc : FastField modulus) : FastField modulus :=
  square (square (square (square acc)))

/-- The window table as an `Array`, for O(1) digit lookup during inversion. -/
@[inline]
private def windowTableArr (x : FastField modulus) : Array (FastField modulus) :=
  (windowTable x).toArray

/-- One window step: four squarings, then a table multiply unless the digit is `0`. -/
@[inline]
private def windowStep (tbl : Array (FastField modulus)) (acc : FastField modulus) (d : ℕ) :
    FastField modulus :=
  if d = 0 then sq4 acc else mul (sq4 acc) (tbl.getD d (one modulus))

/-- Base-16 Horner exponentiation to the fixed exponent `modulus - 2` against a precomputed
table. -/
private def invFold (tbl : Array (FastField modulus)) : FastField modulus :=
  (p2HexDigits modulus).tail.foldl (windowStep tbl)
    (tbl.getD ((p2HexDigits modulus).headD 0) (one modulus))

/-- Inversion via Fermat's little theorem (`x⁻¹ = x^(p-2)`), evaluated by fixed 4-bit window
exponentiation over the precomputed digits of `p-2`: the proven fallback path of `inv`. -/
@[inline]
def invWindow (x : FastField modulus) : FastField modulus := invFold (windowTableArr x)

/-- Accept a raw candidate `z` for `x⁻¹` if it verifies (canonical range and `z · x = 1`
under the proven Montgomery multiplier), else fall back to the proven `invWindow`. The check
makes the candidate's provenance irrelevant to correctness. -/
@[inline]
def invWithCandidate (x : FastField modulus) (z : UInt256L) : FastField modulus :=
  if h : z < P.modulus256 ∧ montgomeryMul (modulus := modulus) z x.val = P.rModModulus then
    ⟨z, by rw [← P.modulus256_toNat]; exact UInt256L.lt_iff_toNat_lt.mp h.1⟩
  else invWindow x

/-- Inversion in Montgomery form: the Pornin binary-GCD candidate (`gcdInvCandidate`),
verified by one Montgomery multiplication, with the windowed Fermat exponentiation as proven
fallback (taken only for `x = 0`, where it correctly yields `0`, or a candidate miss). -/
@[inline]
def inv (x : FastField modulus) : FastField modulus :=
  invWithCandidate x (gcdInvCandidate (modulus := modulus) x.val)

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : FastField modulus) : FastField modulus := mul x (inv y)

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

/-! ## Correctness of the operations -/

/-- Fermat-style inversion in `ZMod modulus`. -/
private theorem inv_eq_pow (a : ZMod modulus) (ha : a ≠ 0) :
    a⁻¹ = a ^ (modulus - 2) := by
  have h1 : a ^ (modulus - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hmul : a * a ^ (modulus - 2) = 1 := by
    have h2 := P.two_lt_modulus
    rw [← pow_succ',
      show modulus - 2 + 1 = modulus - 1 from by omega]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

@[simp]
theorem toField_zero : toField (0 : FastField modulus) = 0 := by
  have h0 : (0 : FastField modulus).val.toNat = 0 := by show (0 : UInt256L).toNat = 0; decide
  rw [toField_eq_val_toNat_cast_mul_inv, h0, Nat.cast_zero, zero_mul]

@[simp]
theorem toField_one : toField (1 : FastField modulus) = 1 := by
  rw [toField_eq_val_toNat_cast_mul_inv]
  change (P.rModModulus.toNat : ZMod modulus)
    * ((2 ^ 256 : ℕ) : ZMod modulus)⁻¹ = 1
  rw [P.rModModulus_cast]
  exact mul_inv_cancel₀ P.two_pow_256_ne_zero

@[simp]
theorem toField_add (x y : FastField modulus) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_val_toNat_cast_mul_inv (x + y), toField_eq_val_toNat_cast_mul_inv x,
    toField_eq_val_toNat_cast_mul_inv y]
  obtain ⟨hsc, hscb⟩ := UInt256L.toNat_addCarryOut x.val y.val 0 (by decide)
  have hbnd : (UInt256L.addCarryOut x.val y.val 0).1.toNat
      + (UInt256L.addCarryOut x.val y.val 0).2.toNat * 2 ^ 256
      < 2 * modulus := by
    rw [hsc, show (0 : UInt64).toNat = 0 from rfl]
    have := x.property; have := y.property; omega
  show ((reduceWideRaw (modulus := modulus) (UInt256L.addCarryOut x.val y.val 0).1
        (UInt256L.addCarryOut x.val y.val 0).2).toNat : ZMod modulus)
      * ((2 ^ 256 : ℕ) : ZMod modulus)⁻¹ = _
  rw [reduceWideRaw_cast _ _ hscb hbnd, hsc, show (0 : UInt64).toNat = 0 from rfl,
    Nat.add_zero, Nat.cast_add]
  ring

private theorem modulus_cast_zero : (P.modulus256.toNat : ZMod modulus) = 0 := by
  rw [P.modulus256_toNat]; exact ZMod.natCast_self (modulus)

@[simp]
theorem toField_neg (x : FastField modulus) : toField (-x) = -toField x := by
  rw [toField_eq_val_toNat_cast_mul_inv (-x), toField_eq_val_toNat_cast_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegN : (-x : FastField modulus).val.toNat = 0 := by
      show (neg x).val.toNat = 0; unfold neg; rw [dif_pos hx]
      show (0 : UInt256L).toNat = 0; decide
    have hxN : x.val.toNat = 0 := by rw [hx]; decide
    rw [hnegN, hxN]; simp
  · have hle : x.val.toNat ≤ P.modulus256.toNat := by
      rw [P.modulus256_toNat]; exact Nat.le_of_lt x.property
    have hnegval : (-x : FastField modulus).val = P.modulus256 - x.val := by
      show (neg x).val = _; unfold neg; rw [dif_neg hx]
    rw [hnegval, UInt256L.toNat_sub_of_le hle, Nat.cast_sub hle, modulus_cast_zero]
    ring

@[simp]
theorem toField_sub (x y : FastField modulus) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_val_toNat_cast_mul_inv (x - y), toField_eq_val_toNat_cast_mul_inv x,
    toField_eq_val_toNat_cast_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hyxN : y.val.toNat ≤ x.val.toNat := (UInt256L.le_iff_toNat_le).mp hyx
    have hsubval : (x - y : FastField modulus).val = x.val - y.val := by
      show (sub x y).val = _; unfold sub; rw [dif_pos hyx]
    rw [hsubval, UInt256L.toNat_sub_of_le hyxN, Nat.cast_sub hyxN]
    ring
  · have hb := x.property; have hyb := y.property
    have hm := P.modulus256_toNat; have hp := P.modulus_lt_two_pow_256
    have hxy : x.val.toNat < y.val.toNat := by rw [UInt256L.le_iff_toNat_le] at hyx; omega
    have hyle : y.val.toNat ≤ P.modulus256.toNat := by rw [hm]; omega
    have htval : (P.modulus256 - y.val).toNat = P.modulus256.toNat - y.val.toNat :=
      UInt256L.toNat_sub_of_le hyle
    have hsubval : (x - y : FastField modulus).val = x.val + (P.modulus256 - y.val) := by
      show (sub x y).val = _; unfold sub; rw [dif_neg hyx]
    rw [hsubval, UInt256L.toNat_add, htval, hm, Nat.mod_eq_of_lt (by omega),
      Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hyb), ZMod.natCast_self]
    ring

@[simp]
theorem toField_mul (x y : FastField modulus) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_val_toNat_cast_mul_inv (x * y), toField_eq_val_toNat_cast_mul_inv x,
    toField_eq_val_toNat_cast_mul_inv y]
  have hval : (x * y).val = montgomeryMul (modulus := modulus) x.val y.val := rfl
  rw [hval, (montgomeryMul_spec (modulus := modulus) x.val y.val x.property).2]
  ring

/-- Ring equivalence between the fast Montgomery representation and the canonical field. -/
def ringEquiv (modulus : ℕ) [P : Mont256Field modulus] : FastField modulus ≃+* ZMod modulus where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp] theorem ringEquiv_apply {x : FastField modulus} : ringEquiv modulus x = toField x := rfl
@[simp] theorem ringEquiv_symm_apply {x : ZMod modulus} :
    (ringEquiv modulus).symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : FastField modulus) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]; ring

private theorem pow_succ_field (x : FastField modulus) (n : ℕ) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup (FastField modulus) := { mul := (· * ·), mul_assoc := mul_assoc_field }
  exact npowBinRec_succ n x

@[simp]
theorem toField_square (x : FastField modulus) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

@[simp]
theorem toField_pow (x : FastField modulus) (n : ℕ) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero => unfold pow; rw [npowBinRec_zero, toField_one]; simp
  | succ n ih => rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

private theorem toField_mul_raw (x y : FastField modulus) :
    toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

private theorem tableAux_toField (x : FastField modulus) (n : ℕ) :
    ∀ (s : FastField modulus) (d : ℕ), d < n →
      toField ((tableAux x n s).getD d (one modulus)) = toField s * toField x ^ d := by
  induction n with
  | zero => intro s d hd; omega
  | succ n ih =>
    intro s d hd
    cases d with
    | zero => simp only [tableAux, List.getD_cons_zero, pow_zero, mul_one]
    | succ d =>
      simp only [tableAux, List.getD_cons_succ]
      rw [ih (mul s x) d (by omega), toField_mul_raw, pow_succ]; ring

private theorem windowTable_toField (x : FastField modulus) :
    ∀ d, d < 16 → toField ((windowTable x).getD d (one modulus)) = toField x ^ d := by
  intro d hd
  have h1 : toField (one modulus) = 1 := toField_one
  rw [windowTable, tableAux_toField x 16 (one modulus) d hd, h1, one_mul]

private theorem toField_sq4 (acc : FastField modulus) : toField (sq4 acc) = toField acc ^ 16 := by
  unfold sq4; simp only [toField_square]; ring

private theorem windowTableArr_toField (x : FastField modulus) :
    ∀ d, d < 16 → toField ((windowTableArr x).getD d (one modulus)) = toField x ^ d := by
  intro d hd
  rw [windowTableArr]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  exact windowTable_toField x d hd

private theorem windowFold_toField (x : FastField modulus) (tbl : Array (FastField modulus))
    (htbl : ∀ d, d < 16 → toField (tbl.getD d (one modulus)) = toField x ^ d) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < 16) → ∀ (acc : FastField modulus) (E : ℕ),
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

omit P in
private theorem p2HexDigits_tail_lt : ∀ d ∈ (p2HexDigits modulus).tail, d < 16 := by
  intro d hd
  have hmem : d ∈ p2HexDigits modulus := List.mem_of_mem_tail hd
  rw [p2HexDigits, List.mem_map] at hmem
  obtain ⟨i, _, rfl⟩ := hmem
  exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

omit P in
private theorem p2HexDigits_head_lt : (p2HexDigits modulus).headD 0 < 16 := by
  rcases hl : p2HexDigits modulus with _ | ⟨a, t⟩
  · simp
  · have hmem : a ∈ p2HexDigits modulus := by rw [hl]; exact List.mem_cons_self ..
    rw [p2HexDigits, List.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    rw [List.headD_cons, ← hi]
    exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)

private theorem p2HexDigits_reconstruct :
    (p2HexDigits modulus).tail.foldl (fun n d => n * 16 + d) ((p2HexDigits modulus).headD 0)
      = modulus - 2 := by
  unfold p2HexDigits
  exact P.p2HexDigits_reconstruct

private theorem toField_invFold (x : FastField modulus) (tbl : Array (FastField modulus))
    (htbl : ∀ d, d < 16 → toField (tbl.getD d (one modulus)) = toField x ^ d) :
    toField (invFold tbl) = toField x ^ (modulus - 2) := by
  unfold invFold
  rw [windowFold_toField x tbl htbl (p2HexDigits modulus).tail p2HexDigits_tail_lt
        (tbl.getD ((p2HexDigits modulus).headD 0) (one modulus)) ((p2HexDigits modulus).headD 0)
        (htbl _ p2HexDigits_head_lt),
      p2HexDigits_reconstruct]

private theorem toField_invWindow_pow (x : FastField modulus) :
    toField (invWindow x) = toField x ^ (modulus - 2) := by
  unfold invWindow; exact toField_invFold x (windowTableArr x) (windowTableArr_toField x)

private theorem toField_invWindow_raw (x : FastField modulus) :
    toField (invWindow x) = (toField x)⁻¹ := by
  rw [toField_invWindow_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero]
    refine zero_pow ?_
    show modulus - 2 ≠ 0
    have := P.two_lt_modulus; omega
  · exact (inv_eq_pow (toField x) hx).symm

/-- The certificate lemma behind `inv`: a canonical element `w` whose Montgomery product with
`x` is the Montgomery one (`R mod p`) interprets to the field inverse of `x`. This is all the
binary-GCD fast path needs: one proven multiplication certifies the candidate. -/
private theorem toField_eq_inv_of_montMul_eq_one (x w : FastField modulus)
    (heq : montgomeryMul (modulus := modulus) w.val x.val = P.rModModulus) :
    toField w = (toField x)⁻¹ := by
  have hspec := (montgomeryMul_spec (modulus := modulus) w.val x.val w.property).2
  rw [heq, P.rModModulus_cast] at hspec
  apply eq_inv_of_mul_eq_one_left
  rw [toField_eq_val_toNat_cast_mul_inv, toField_eq_val_toNat_cast_mul_inv]
  set R := ((2 ^ 256 : ℕ) : ZMod modulus) with hR
  calc (w.val.toNat : ZMod modulus) * R⁻¹
        * ((x.val.toNat : ZMod modulus) * R⁻¹)
      = (w.val.toNat : ZMod modulus)
        * (x.val.toNat : ZMod modulus) * R⁻¹ * R⁻¹ := by ring
    _ = R * R⁻¹ := by rw [← hspec]
    _ = 1 := mul_inv_cancel₀ (P.two_pow_256_ne_zero (modulus := modulus))

private theorem toField_invWithCandidate (x : FastField modulus) (z : UInt256L) :
    toField (invWithCandidate x z) = (toField x)⁻¹ := by
  unfold invWithCandidate
  by_cases h : z < P.modulus256 ∧ montgomeryMul (modulus := modulus) z x.val = P.rModModulus
  · rw [dif_pos h]
    exact toField_eq_inv_of_montMul_eq_one x
      ⟨z, by rw [← P.modulus256_toNat]; exact UInt256L.lt_iff_toNat_lt.mp h.1⟩ h.2
  · rw [dif_neg h]
    exact toField_invWindow_raw x

private theorem toField_inv_raw (x : FastField modulus) : toField (inv x) = (toField x)⁻¹ :=
  toField_invWithCandidate x (gcdInvCandidate (modulus := modulus) x.val)

@[simp]
theorem toField_inv (x : FastField modulus) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_div_mul_inv (x y : FastField modulus) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div; exact toField_mul_raw x (inv y)

@[simp]
theorem toField_div (x y : FastField modulus) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : ZMod modulus, c = b⁻¹ → a * c = a / b := by
    intro a b c hc; rw [hc]; rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

@[simp]
theorem toField_natCast (n : ℕ) :
    toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofNat modulus n) = (n : ZMod modulus)
  unfold ofNat
  rw [toField_ofCanonicalNat, ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

@[simp]
theorem toField_intCast (n : Int) :
    toField (n : FastField modulus) = (n : ZMod modulus) := by
  change toField (ofInt modulus n) = (n : ZMod modulus)
  unfold ofInt; rw [toField_ofField]

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
      rw [toField_pow]; exact (zpow_natCast (toField x) n).symm
  | negSucc n =>
      change toField (pow (inv x) (n + 1)) = toField x ^ (Int.negSucc n)
      have hinv : toField (inv x) = (toField x)⁻¹ := by
        change toField x⁻¹ = (toField x)⁻¹; rw [toField_inv]
      rw [toField_pow, hinv, zpow_negSucc, inv_pow]

@[simp]
theorem toField_nnratCast (q : ℚ≥0) :
    toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus))
    = (q : ZMod modulus)
  rw [toField_ofField]

@[simp]
theorem toField_ratCast (q : ℚ) :
    toField (q : FastField modulus) = (q : ZMod modulus) := by
  change toField (ofField (q : ZMod modulus))
    = (q : ZMod modulus)
  rw [toField_ofField]

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

@[simp]
theorem toField_qsmul (q : ℚ) (x : FastField modulus) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

/-! ## Algebraic structure -/

/-- Field instance transferred from the canonical field through `toField`. -/
instance instField : _root_.Field (FastField modulus) := by
  apply toField_injective.field toField <;> simp

/-- A fast 256-bit Montgomery field is non-binary. -/
instance instNonBinaryField : NonBinaryField (FastField modulus) where
  char_neq_2 := by
    change ((2 : ℕ) : FastField modulus) ≠ 0
    intro h
    apply P.two_ne_zero
    have h2 : ((2 : ℕ) : ZMod modulus) = 0 := by
      rw [← toField_natCast 2, h, toField_zero]
    simpa using h2

end Native256
end Montgomery
