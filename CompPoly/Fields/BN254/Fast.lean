/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.Finite.Basic
import CompPoly.Fields.Basic
import CompPoly.Fields.BN254.Fast.Convert

/-!
# Fast BN254 Scalar Field — Operations and Field Instance

Native-word field operations on the fast Montgomery representation `ScalarField`: addition,
negation, subtraction, the CIOS Montgomery `mul`/`square`, exponentiation `pow`, and Fermat
inversion `inv`/`div`, together with their `Zero`/`One`/`Add`/`Mul`/… typeclass instances. The
`toField_*` family bridges each operation to the canonical `ZMod p` field; `toField_injective`
then transfers the full `Field` structure onto `ScalarField` (with `CommRing` and
`NonBinaryField` following), and `ringEquiv` packages the bridge as a ring isomorphism
`ScalarField ≃+* ZMod p`.
-/

set_option maxRecDepth 4000

namespace BN254
namespace Fast

open BN254 (scalarFieldSize)

@[inline]
def add (x y : ScalarField) : ScalarField :=
  reduceUInt256Lt2Modulus (x.val + y.val) (by
    rw [UInt256L.toNat_add]
    have hx := x.property
    have hy := y.property
    have hm := modulus_toNat
    omega)

/-- Fast zero in Montgomery form (the zero residue). -/
def zero : ScalarField := ⟨0, by decide⟩

/-- Fast modular negation in Montgomery form. -/
@[inline]
def neg (x : ScalarField) : ScalarField :=
  if hx : x.val = 0 then
    zero
  else
    ⟨modulus - x.val, by
      have hle : x.val.toNat ≤ modulus.toNat := Nat.le_of_lt x.property
      rw [UInt256L.toNat_sub_of_le hle]
      have hxpos : 0 < x.val.toNat := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hx
        apply UInt256L.toNat_inj.mp
        simpa using hzero
      omega⟩

/-- Fast modular subtraction in Montgomery form. -/
@[inline]
def sub (x y : ScalarField) : ScalarField :=
  if hyx : y.val ≤ x.val then
    ⟨x.val - y.val, by
      rw [UInt256L.le_iff_toNat_le] at hyx
      rw [UInt256L.toNat_sub_of_le hyx]
      have hx := x.property
      omega⟩
  else
    ⟨x.val + modulus - y.val, by
      have hb := x.property
      have hyb := y.property
      have hm := modulus_toNat
      have h2 := two_mul_scalarFieldSize_lt_two256
      rw [UInt256L.le_iff_toNat_le] at hyx
      have hbound : x.val.toNat + modulus.toNat < 2 ^ 256 := by omega
      have hsum_eq : (x.val + modulus).toNat = x.val.toNat + modulus.toNat := by
        rw [UInt256L.toNat_add, Nat.mod_eq_of_lt hbound]
      have hyle : y.val.toNat ≤ (x.val + modulus).toNat := by rw [hsum_eq]; omega
      rw [UInt256L.toNat_sub_of_le hyle, hsum_eq]
      omega⟩



/-- Fast one in Montgomery form (the residue `R mod p`). -/
def one : ScalarField := ⟨rModModulus, by decide⟩

/-- Fast modular multiplication in Montgomery form (CIOS Montgomery product). -/
@[inline]
def mul (x y : ScalarField) : ScalarField :=
  ⟨montgomeryMul x.val y.val, (montgomeryMul_spec x.val y.val (property_lt x)).1⟩

/-- Fast squaring. -/
@[inline]
def square (x : ScalarField) : ScalarField := mul x x

/-- Exponentiation by binary repeated squaring over the fast representation. -/
@[specialize]
def pow (x : ScalarField) (n : Nat) : ScalarField :=
  @npowBinRec ScalarField ⟨one⟩ ⟨mul⟩ n x

/-- Shared 4-bit window table builder: `tableAux x n s = [s, s*x, ..., s*x^(n-1)]` (`n` entries,
each one multiply, threaded through the running power `s`). -/
def tableAux (x : ScalarField) : Nat → ScalarField → List ScalarField
  | 0, _ => []
  | n + 1, cur => cur :: tableAux x n (mul cur x)

/-- The 4-bit window table `[x^0, x^1, ..., x^15]`, precomputed once with 15 multiplications. -/
def windowTable (x : ScalarField) : List ScalarField := tableAux x 16 one

/-- Fermat exponent used for inversion in the prime field (`x⁻¹ = x^(p-2)`). -/
def invExponent : Nat := scalarFieldSize - 2

/-- The base-16 digits of the inversion exponent `p-2`, most significant first (64 nibbles).
A `List` CAF, built once at initialization, so inversion never decomposes the 254-bit exponent
nor materializes a list at runtime (`.tail`/`.headD` are O(1) on the cached list). -/
def p2HexDigits : List Nat :=
  (List.range 64).map (fun i => (invExponent >>> ((63 - i) * 4)) &&& 0xF)

/-- `x^16` by four explicit squarings (no exponentiation-by-squaring dispatch). -/
@[inline]
def sq4 (acc : ScalarField) : ScalarField := square (square (square (square acc)))

/-- The window table as an `Array`, for O(1) digit lookup during inversion. -/
@[inline]
def windowTableArr (x : ScalarField) : Array ScalarField := (windowTable x).toArray

/-- One window step: four squarings, then a table multiply unless the digit is `0`. -/
@[inline]
def windowStep (tbl : Array ScalarField) (acc : ScalarField) (d : Nat) : ScalarField :=
  if d = 0 then sq4 acc else mul (sq4 acc) (tbl.getD d one)

/-- Base-16 Horner exponentiation to the fixed exponent `p-2` against a precomputed window
table: four squarings and (for nonzero digits) one table multiply per digit, most significant
first. The leading digit seeds the accumulator directly, sparing a wasted initial squaring. -/
def invFold (tbl : Array ScalarField) : ScalarField :=
  p2HexDigits.tail.foldl (windowStep tbl) (tbl.getD (p2HexDigits.headD 0) one)

/-- Inversion in Montgomery form via Fermat's little theorem (`x⁻¹ = x^(p-2)`), evaluated by
fixed 4-bit window exponentiation over the precomputed digits of `p-2`. -/
@[inline]
def inv (x : ScalarField) : ScalarField := invFold (windowTableArr x)

/-- Division through inversion and fast multiplication. -/
@[inline]
def div (x y : ScalarField) : ScalarField := mul x (inv y)


instance instZero : Zero ScalarField where zero := zero
instance instOne : One ScalarField where one := one
instance instAdd : Add ScalarField where add := add
instance instNeg : Neg ScalarField where neg := neg
instance instSub : Sub ScalarField where sub := sub
instance instMul : Mul ScalarField where mul := mul
instance instInv : Inv ScalarField where inv := inv
instance instDiv : Div ScalarField where div := div
instance instNatCast : NatCast ScalarField where natCast := ofNat
instance instIntCast : IntCast ScalarField where intCast := ofInt
instance instNatSMul : SMul Nat ScalarField where smul n x := ofNat n * x
instance instIntSMul : SMul Int ScalarField where smul n x := ofInt n * x
instance instPowNat : Pow ScalarField Nat where pow := pow
instance instPowInt : Pow ScalarField Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)
instance instNNRatCast : NNRatCast ScalarField where nnratCast q := ofField (q : BN254.ScalarField)
instance instRatCast : RatCast ScalarField where ratCast q := ofField (q : BN254.ScalarField)
instance instNNRatSMul : SMul ℚ≥0 ScalarField where smul q x := ofField (q • toField x)
instance instRatSMul : SMul ℚ ScalarField where smul q x := ofField (q • toField x)


theorem inv_eq_pow_field (a : BN254.ScalarField) (ha : a ≠ 0) :
    a⁻¹ = a ^ (scalarFieldSize - 2) := by
  have h1 : a ^ (scalarFieldSize - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hmul : a * a ^ (scalarFieldSize - 2) = 1 := by
    have h2 : 2 < scalarFieldSize := by decide
    rw [← pow_succ', show scalarFieldSize - 2 + 1 = scalarFieldSize - 1 from by omega]
    exact h1
  exact (eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm

theorem two_ne_zero_in_field : ((2 : Nat) : BN254.ScalarField) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd (by decide) hd) (by decide)


@[simp]
theorem toField_zero : toField (0 : ScalarField) = 0 := by
  have h0 : (0 : ScalarField).val.toNat = 0 := by decide
  rw [toField_eq_raw_mul_inv, h0, Nat.cast_zero, zero_mul]

@[simp]
theorem toField_one : toField (1 : ScalarField) = 1 := by
  rw [toField_eq_raw_mul_inv]
  change (rModModulus.toNat : BN254.ScalarField) * ((2 ^ 256 : Nat) : BN254.ScalarField)⁻¹ = 1
  rw [rModModulus_cast]
  exact mul_inv_cancel₀ r256_ne_zero

@[simp]
theorem toField_add (x y : ScalarField) : toField (x + y) = toField x + toField y := by
  rw [toField_eq_raw_mul_inv (x + y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  show ((reduceUInt256Lt2ModulusRaw (x.val + y.val)).toNat : BN254.ScalarField)
      * ((2 ^ 256 : Nat) : BN254.ScalarField)⁻¹ = _
  rw [reduceUInt256Lt2ModulusRaw_cast, UInt256L.toNat_add]
  have hsum_lt : x.val.toNat + y.val.toNat < 2 ^ 256 := by
    have := two_mul_scalarFieldSize_lt_two256
    have := property_lt x; have := property_lt y; omega
  rw [Nat.mod_eq_of_lt hsum_lt, Nat.cast_add]
  ring

private theorem modulus_cast_zero : (modulus.toNat : BN254.ScalarField) = 0 := by
  rw [modulus_toNat]; exact ZMod.natCast_self scalarFieldSize

@[simp]
theorem toField_neg (x : ScalarField) : toField (-x) = -toField x := by
  rw [toField_eq_raw_mul_inv (-x), toField_eq_raw_mul_inv x]
  by_cases hx : x.val = 0
  · have hnegN : (-x : ScalarField).val.toNat = 0 := by
      show (neg x).val.toNat = 0; unfold neg; rw [dif_pos hx]; decide
    have hxN : x.val.toNat = 0 := by rw [hx]; decide
    rw [hnegN, hxN]; simp
  · have hle : x.val.toNat ≤ modulus.toNat := Nat.le_of_lt x.property
    have hnegval : (-x : ScalarField).val = modulus - x.val := by
      show (neg x).val = _; unfold neg; rw [dif_neg hx]
    rw [hnegval, UInt256L.toNat_sub_of_le hle, Nat.cast_sub hle, modulus_cast_zero]
    ring

@[simp]
theorem toField_sub (x y : ScalarField) : toField (x - y) = toField x - toField y := by
  rw [toField_eq_raw_mul_inv (x - y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  by_cases hyx : y.val ≤ x.val
  · have hyxN : y.val.toNat ≤ x.val.toNat := (UInt256L.le_iff_toNat_le).mp hyx
    have hsubval : (x - y : ScalarField).val = x.val - y.val := by
      show (sub x y).val = _; unfold sub; rw [dif_pos hyx]
    rw [hsubval, UInt256L.toNat_sub_of_le hyxN, Nat.cast_sub hyxN]
    ring
  · have hb := x.property
    have hm := modulus_toNat
    have h2 := two_mul_scalarFieldSize_lt_two256
    have hbound : x.val.toNat + modulus.toNat < 2 ^ 256 := by omega
    have hsum_eq : (x.val + modulus).toNat = x.val.toNat + modulus.toNat := by
      rw [UInt256L.toNat_add, Nat.mod_eq_of_lt hbound]
    have hyle : y.val.toNat ≤ x.val.toNat + modulus.toNat := by have := y.property; omega
    have hsubval : (x - y : ScalarField).val = x.val + modulus - y.val := by
      show (sub x y).val = _; unfold sub; rw [dif_neg hyx]
    rw [hsubval, UInt256L.toNat_sub_of_le (by rw [hsum_eq]; exact hyle), hsum_eq,
        Nat.cast_sub hyle, Nat.cast_add, modulus_cast_zero]
    ring

@[simp]
theorem toField_mul (x y : ScalarField) : toField (x * y) = toField x * toField y := by
  rw [toField_eq_raw_mul_inv (x * y), toField_eq_raw_mul_inv x, toField_eq_raw_mul_inv y]
  have hval : (x * y).val = montgomeryMul x.val y.val := rfl
  rw [hval, (montgomeryMul_spec x.val y.val (property_lt x)).2]
  ring

def ringEquiv : ScalarField ≃+* BN254.ScalarField where
  toFun := toField
  invFun := ofField
  left_inv := ofField_toField
  right_inv := toField_ofField
  map_add' := toField_add
  map_mul' := toField_mul

@[simp] theorem ringEquiv_apply (x : ScalarField) : ringEquiv x = toField x := rfl
@[simp] theorem ringEquiv_symm_apply (x : BN254.ScalarField) :
    ringEquiv.symm x = ofField x := rfl

private theorem mul_assoc_field (x y z : ScalarField) : (x * y) * z = x * (y * z) := by
  apply toField_injective
  rw [toField_mul, toField_mul, toField_mul, toField_mul]
  ring

private theorem pow_succ_field (x : ScalarField) (n : Nat) : pow x (n + 1) = pow x n * x := by
  unfold pow
  letI : Semigroup ScalarField := { mul := (· * ·), mul_assoc := mul_assoc_field }
  exact npowBinRec_succ n x

@[simp]
theorem toField_square (x : ScalarField) : toField (square x) = toField x * toField x := by
  change toField (x * x) = toField x * toField x
  rw [toField_mul]

@[simp]
theorem toField_pow (x : ScalarField) (n : Nat) : toField (pow x n) = toField x ^ n := by
  induction n with
  | zero => unfold pow; rw [npowBinRec_zero, toField_one]; simp
  | succ n ih => rw [pow_succ_field, toField_mul, ih, _root_.pow_succ]

private theorem toField_mul_raw (x y : ScalarField) :
    toField (mul x y) = toField x * toField y := by
  change toField (x * y) = toField x * toField y
  exact toField_mul x y

/-- Each window-table entry `d` casts to `x ^ d` (offset by the threaded `s`). -/
private theorem tableAux_toField (x : ScalarField) (n : Nat) :
    ∀ (s : ScalarField) (d : Nat), d < n →
      toField ((tableAux x n s).getD d one) = toField s * toField x ^ d := by
  induction n with
  | zero => intro s d hd; omega
  | succ n ih =>
    intro s d hd
    cases d with
    | zero => simp only [tableAux, List.getD_cons_zero, pow_zero, mul_one]
    | succ d =>
      simp only [tableAux, List.getD_cons_succ]
      rw [ih (mul s x) d (by omega), toField_mul_raw, pow_succ]
      ring

/-- The window table entry `d` is `x ^ d` in the canonical field. -/
private theorem windowTable_toField (x : ScalarField) :
    ∀ d, d < 16 → toField ((windowTable x).getD d one) = toField x ^ d := by
  intro d hd
  have h1 : toField one = 1 := toField_one
  rw [windowTable, tableAux_toField x 16 one d hd, h1, one_mul]

/-- `sq4` is the 16th power in the canonical field. -/
private theorem toField_sq4 (acc : ScalarField) : toField (sq4 acc) = toField acc ^ 16 := by
  unfold sq4; simp only [toField_square]; ring

/-- The `Array` window table casts entrywise to powers of `toField x` (via the `List` table). -/
private theorem windowTableArr_toField (x : ScalarField) :
    ∀ d, d < 16 → toField ((windowTableArr x).getD d one) = toField x ^ d := by
  intro d hd
  rw [windowTableArr]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  exact windowTable_toField x d hd

/-- Folding the window step over any list of base-16 digits computes the Horner value of those
digits as an exponent of `toField x` (a zero digit contributes only the four squarings). -/
private theorem windowFold_toField (x : ScalarField) (tbl : Array ScalarField)
    (htbl : ∀ d, d < 16 → toField (tbl.getD d one) = toField x ^ d) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 16) → ∀ (acc : ScalarField) (E : Nat),
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

/-- Every precomputed tail digit is a base-16 digit. -/
private theorem p2HexDigits_tail_lt : ∀ d ∈ p2HexDigits.tail, d < 16 := by decide

/-- The leading precomputed digit is a base-16 digit. -/
private theorem p2HexDigits_head_lt : p2HexDigits.headD 0 < 16 := by decide

/-- The precomputed digits reconstruct the inversion exponent `p-2` via base-16 Horner, the
leading digit seeding the accumulator. -/
private theorem p2HexDigits_reconstruct :
    p2HexDigits.tail.foldl (fun n d => n * 16 + d) (p2HexDigits.headD 0) = invExponent := by
  decide

/-- `invFold` against a correct table computes `x ^ (p-2)` in the canonical field. -/
private theorem toField_invFold (x : ScalarField) (tbl : Array ScalarField)
    (htbl : ∀ d, d < 16 → toField (tbl.getD d one) = toField x ^ d) :
    toField (invFold tbl) = toField x ^ invExponent := by
  unfold invFold
  rw [windowFold_toField x tbl htbl p2HexDigits.tail p2HexDigits_tail_lt
        (tbl.getD (p2HexDigits.headD 0) one) (p2HexDigits.headD 0)
        (htbl _ p2HexDigits_head_lt),
      p2HexDigits_reconstruct]

private theorem toField_inv_pow (x : ScalarField) :
    toField (inv x) = toField x ^ invExponent := by
  unfold inv; exact toField_invFold x (windowTableArr x) (windowTableArr_toField x)

private theorem toField_inv_raw (x : ScalarField) : toField (inv x) = (toField x)⁻¹ := by
  rw [toField_inv_pow]
  by_cases hx : toField x = 0
  · rw [hx, inv_zero]
    refine zero_pow ?_
    show scalarFieldSize - 2 ≠ 0
    have : 2 < scalarFieldSize := by decide
    omega
  · simpa [invExponent] using (inv_eq_pow_field (toField x) hx).symm

@[simp]
theorem toField_inv (x : ScalarField) : toField x⁻¹ = (toField x)⁻¹ := by
  change toField (inv x) = (toField x)⁻¹
  exact toField_inv_raw x

private theorem toField_div_mul_inv (x y : ScalarField) :
    toField (div x y) = toField x * toField (inv y) := by
  unfold div; exact toField_mul_raw x (inv y)

@[simp]
theorem toField_div (x y : ScalarField) : toField (x / y) = toField x / toField y := by
  change toField (div x y) = toField x / toField y
  have h : ∀ a b c : BN254.ScalarField, c = b⁻¹ → a * c = a / b := by
    intro a b c hc; rw [hc]; rfl
  exact (toField_div_mul_inv x y).trans
    (h (toField x) (toField y) (toField (inv y)) (toField_inv_raw y))

@[simp]
theorem toField_natCast (n : Nat) : toField (n : ScalarField) = (n : BN254.ScalarField) := by
  change toField (ofNat n) = (n : BN254.ScalarField)
  unfold ofNat
  rw [toField_ofCanonicalNat, ZMod.natCast_eq_natCast_iff]
  exact Nat.mod_modEq _ _

@[simp]
theorem toField_intCast (n : Int) : toField (n : ScalarField) = (n : BN254.ScalarField) := by
  change toField (ofInt n) = (n : BN254.ScalarField)
  unfold ofInt; rw [toField_ofField]

@[simp]
theorem toField_nsmul (n : Nat) (x : ScalarField) : toField (n • x) = n • toField x := by
  change toField ((n : ScalarField) * x) = n • toField x
  rw [toField_mul, toField_natCast, nsmul_eq_mul]

@[simp]
theorem toField_zsmul (n : Int) (x : ScalarField) : toField (n • x) = n • toField x := by
  change toField ((n : ScalarField) * x) = n • toField x
  rw [toField_mul, toField_intCast, zsmul_eq_mul]

@[simp]
theorem toField_npow (x : ScalarField) (n : Nat) : toField (x ^ n) = toField x ^ n := by
  change toField (pow x n) = toField x ^ n
  rw [toField_pow]

@[simp]
theorem toField_zpow (x : ScalarField) (n : Int) : toField (x ^ n) = toField x ^ n := by
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
theorem toField_nnratCast (q : ℚ≥0) : toField (q : ScalarField) = (q : BN254.ScalarField) := by
  change toField (ofField (q : BN254.ScalarField)) = (q : BN254.ScalarField)
  rw [toField_ofField]

@[simp]
theorem toField_ratCast (q : ℚ) : toField (q : ScalarField) = (q : BN254.ScalarField) := by
  change toField (ofField (q : BN254.ScalarField)) = (q : BN254.ScalarField)
  rw [toField_ofField]

@[simp]
theorem toField_nnqsmul (q : ℚ≥0) (x : ScalarField) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

@[simp]
theorem toField_qsmul (q : ℚ) (x : ScalarField) : toField (q • x) = q • toField x := by
  change toField (ofField (q • toField x)) = q • toField x
  rw [toField_ofField]

instance (priority := low) instField : _root_.Field ScalarField :=
  toField_injective.field toField
    toField_zero toField_one toField_add toField_mul toField_neg toField_sub
    toField_inv toField_div toField_nsmul toField_zsmul toField_nnqsmul toField_qsmul
    toField_npow toField_zpow toField_natCast toField_intCast toField_nnratCast toField_ratCast

instance (priority := low) instCommRing : CommRing ScalarField := by infer_instance

instance (priority := low) instNonBinaryField : NonBinaryField ScalarField where
  char_neq_2 := by
    change ((2 : Nat) : ScalarField) ≠ 0
    intro h
    exact two_ne_zero_in_field (by
      calc ((2 : Nat) : BN254.ScalarField)
          = toField ((2 : Nat) : ScalarField) := (toField_natCast 2).symm
        _ = toField (0 : ScalarField) := congrArg toField h
        _ = 0 := toField_zero)

end Fast
end BN254
