/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Fields.Binary.Extension.Basic
import Mathlib.Data.BitVec

/-!
# Direct Binary-Extension Executable Operations

Executable `BitVec` operations for direct binary extensions. These definitions
are the computation layer used by concrete fields; algebraic field instances and
operation-equivalence proofs are supplied only after irreducibility and reduction
certificates are available.
-/

namespace BinaryField

namespace Extension

open Polynomial

/-- Executable metadata for a direct binary extension. -/
structure ExecutableParams where
  degree : Nat
  tailExponents : List Nat
  tailExponents_bound : ∀ exponent ∈ tailExponents, exponent < degree

/-- Executable carrier for a direct binary extension. -/
@[reducible]
def ConcreteField (params : ExecutableParams) : Type :=
  BitVec params.degree

namespace Concrete

variable (params : ExecutableParams)

/-- View an executable field element as its raw bit-vector representation. -/
def toBitVec (a : ConcreteField params) : BitVec params.degree :=
  a

/-- Reinterpret a raw bit-vector as an executable field element. -/
def ofBitVec (a : BitVec params.degree) : ConcreteField params :=
  a

@[simp]
lemma toBitVec_ofBitVec (a : BitVec params.degree) :
    toBitVec params (ofBitVec params a) = a :=
  rfl

@[simp]
lemma ofBitVec_toBitVec (a : ConcreteField params) :
    ofBitVec params (toBitVec params a) = a :=
  rfl

/-- Raw natural-number encoding of an executable field element. -/
def toNat (a : ConcreteField params) : Nat :=
  (toBitVec params a).toNat

/-- Raw bit-pattern constructor. This is not a field `NatCast`. -/
def ofNat (n : Nat) : ConcreteField params :=
  ofBitVec params (BitVec.ofNat params.degree n)

/-- Zero bit-pattern. -/
def zero : ConcreteField params :=
  ofNat params 0

/-- One bit-pattern. -/
def one : ConcreteField params :=
  ofNat params 1

/-- Polynomial-basis generator bit-pattern, representing `X`. -/
def root : ConcreteField params :=
  ofNat params 2

/-- Characteristic-two addition by XOR. -/
def add (a b : ConcreteField params) : ConcreteField params :=
  ofBitVec params (toBitVec params a ^^^ toBitVec params b)

/-- Characteristic-two negation. -/
def neg (a : ConcreteField params) : ConcreteField params :=
  a

/-- Characteristic-two subtraction by XOR. -/
def sub (a b : ConcreteField params) : ConcreteField params :=
  add params a b

/-- One high-degree reduction step for `X^degree + tail`. -/
def reduceNatStep (x : Nat) (exponent : Nat) : Nat :=
  if x.testBit exponent then
    let shift := exponent - params.degree
    x ^^^ (1 <<< exponent) ^^^ sparseMulByNat params.tailExponents (1 <<< shift)
  else
    x

/-- One high-degree reduction step preserves the polynomial residue modulo `P`. -/
theorem reduceNatStep_mod_eq {P : Polynomial (ZMod 2)}
    (hP_ne_zero : P ≠ 0)
    (hP : P = X ^ params.degree + sparsePolynomial params.tailExponents)
    {x exponent : Nat}
    (hdeg : params.degree ≤ exponent)
    (hexp : exponent < 2 * params.degree)
    (hshift : exponent - params.degree < params.degree) :
    toPoly (BitVec.ofNat (2 * params.degree) (reduceNatStep params x exponent)) % P =
      toPoly (BitVec.ofNat (2 * params.degree) x) % P := by
  unfold reduceNatStep
  by_cases hbit : x.testBit exponent
  · simp [hbit]
    rw [toPoly_xor, toPoly_xor]
    let shift := exponent - params.degree
    have hOneExp :
        toPoly (BitVec.ofNat (2 * params.degree) (1 <<< exponent)) =
          (X : Polynomial (ZMod 2)) ^ exponent := by
      simpa using Extension.toPoly_one_shiftLeft (w := 2 * params.degree) exponent hexp
    have hShiftToNat : ((1 <<< shift : BitVec params.degree).toNat) = 1 <<< shift := by
      change (BitVec.ofNat params.degree (1 <<< shift)).toNat = 1 <<< shift
      rw [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by norm_num) hshift
    have hSparse := Extension.toPoly_sparseMulByNat
      (w := params.degree) (W := 2 * params.degree)
      (hW := by omega) (exponents := params.tailExponents)
      (hExp := by
        intro e he
        have he_lt := params.tailExponents_bound e he
        omega)
      (a := (1 <<< shift : BitVec params.degree))
    rw [hShiftToNat] at hSparse
    have hShiftPoly :
        toPoly (BitVec.zeroExtend (2 * params.degree)
          (1 <<< shift : BitVec params.degree)) = (X : Polynomial (ZMod 2)) ^ shift := by
      rw [Extension.toPoly_zeroExtend (by omega)]
      simpa using Extension.toPoly_one_shiftLeft shift hshift
    rw [hShiftPoly] at hSparse
    have hTerm :
        toPoly (BitVec.ofNat (2 * params.degree) (1 <<< exponent)) +
            toPoly
              (BitVec.ofNat (2 * params.degree)
                (sparseMulByNat params.tailExponents (1 <<< shift))) =
          (X : Polynomial (ZMod 2)) ^ shift * P := by
      rw [hOneExp, hSparse, hP]
      have hExpEq : exponent = shift + params.degree := by
        unfold shift
        omega
      rw [hExpEq, pow_add]
      ring
    rw [add_assoc, hTerm]
    rw [CanonicalEuclideanDomain.add_mod_eq (hn := hP_ne_zero)]
    rw [CanonicalEuclideanDomain.mul_mod_eq (hn := hP_ne_zero)]
    simp only [EuclideanDomain.mod_self, mul_zero, EuclideanDomain.zero_mod, add_zero]
    rw [CanonicalEuclideanDomain.mod_mod_eq_mod (hn := hP_ne_zero)]
  · have hfalse : x.testBit exponent = false := Bool.eq_false_iff.mpr hbit
    simp [hfalse]

/-- Clearing a known high bit by XOR drops a value below that bit. -/
theorem xor_clear_high_bit_lt {x exponent : Nat} (hx : x < 2 ^ (exponent + 1))
    (hbit : x.testBit exponent = true) :
    x ^^^ (1 <<< exponent) < 2 ^ exponent := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor]
  by_cases hie : i = exponent
  · subst i
    have hOne : (1 <<< exponent).testBit exponent = true := by
      rw [Nat.testBit_shiftLeft]
      simp
    rw [hbit, hOne]
    rfl
  · have hx_i : x.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le hx (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) (by omega))
    have hshift_i : (1 <<< exponent).testBit i = false := by
      rw [Nat.testBit_shiftLeft]
      simp only [ge_iff_le, hi, decide_true, Bool.true_and]
      apply Nat.testBit_eq_false_of_lt
      exact Nat.one_lt_two_pow (Nat.ne_of_gt (by omega : 0 < i - exponent))
    rw [hx_i, hshift_i]
    rfl

/-- A value below `2^(exponent+1)` with top bit unset is below `2^exponent`. -/
theorem lt_two_pow_of_top_bit_false {x exponent : Nat}
    (hx : x < 2 ^ (exponent + 1)) (hbit : x.testBit exponent = false) :
    x < 2 ^ exponent := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hie : i = exponent
  · subst i
    exact hbit
  · apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le hx (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) (by omega))

/-- XORing shifted one-hot tail terms stays below a common bound. -/
theorem sparseMulByNat_one_shiftLeft_lt (exponents : List Nat) {shift bound : Nat}
    (hExp : ∀ exponent ∈ exponents, shift + exponent < bound) :
    sparseMulByNat exponents (1 <<< shift) < 2 ^ bound := by
  induction exponents with
  | nil =>
      simp [sparseMulByNat]
  | cons exponent rest ih =>
      simp only [sparseMulByNat]
      apply Nat.xor_lt_two_pow
      · rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, ← Nat.pow_add]
        exact Nat.pow_lt_pow_right (by norm_num) (hExp exponent (by simp))
      · apply ih
        intro e he
        exact hExp e (by simp [he])

/-- One high-degree reduction step clears the processed bit and preserves lower width. -/
theorem reduceNatStep_lt_two_pow {x exponent : Nat}
    (hx : x < 2 ^ (exponent + 1))
    (hdeg : params.degree ≤ exponent) :
    reduceNatStep params x exponent < 2 ^ exponent := by
  unfold reduceNatStep
  by_cases hbit : x.testBit exponent
  · simp [hbit]
    apply Nat.xor_lt_two_pow
    · exact xor_clear_high_bit_lt hx hbit
    · apply sparseMulByNat_one_shiftLeft_lt
      intro tail htail
      have htail_lt := params.tailExponents_bound tail htail
      omega
  · have hfalse : x.testBit exponent = false := Bool.eq_false_iff.mpr hbit
    simp [hfalse]
    exact lt_two_pow_of_top_bit_false hx hfalse

/-- Reduce high bits `degree + extra - 1` down through `degree`. -/
def reduceNatAux : Nat → Nat → Nat
  | 0, x => x
  | extra + 1, x =>
      reduceNatAux extra (reduceNatStep params x (params.degree + extra))

/-- Repeated high-degree reduction preserves the polynomial residue modulo `P`. -/
theorem reduceNatAux_mod_eq {P : Polynomial (ZMod 2)}
    (hP_ne_zero : P ≠ 0)
    (hP : P = X ^ params.degree + sparsePolynomial params.tailExponents)
    {n x : Nat} (hn : n ≤ params.degree) :
    toPoly (BitVec.ofNat (2 * params.degree) (reduceNatAux params n x)) % P =
      toPoly (BitVec.ofNat (2 * params.degree) x) % P := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp [reduceNatAux]
      rw [ih (x := reduceNatStep params x (params.degree + n)) (by omega)]
      exact reduceNatStep_mod_eq params hP_ne_zero hP
        (x := x) (exponent := params.degree + n)
        (by omega) (by omega) (by omega)

/-- Repeated high-degree reduction returns a value below the base field width. -/
theorem reduceNatAux_lt_two_pow {n x : Nat} (hn : n ≤ params.degree)
    (hx : x < 2 ^ (params.degree + n)) :
    reduceNatAux params n x < 2 ^ params.degree := by
  induction n generalizing x with
  | zero =>
      simpa [reduceNatAux] using hx
  | succ n ih =>
      simp [reduceNatAux]
      apply ih (by omega)
      exact reduceNatStep_lt_two_pow params
        (x := x) (exponent := params.degree + n)
        (by simpa [Nat.add_assoc] using hx)
        (by omega)

/-- Reduce a carry-less product modulo the executable defining polynomial. -/
def reduceNat (x : Nat) : Nat :=
  reduceNatAux params params.degree x % 2 ^ params.degree

/-- Polynomial semantics of natural-number reduction modulo a direct defining polynomial. -/
theorem toPoly_reduceNat {P : Polynomial (ZMod 2)}
    (hP_ne_zero : P ≠ 0)
    (hP : P = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : P.degree = params.degree)
    {x : Nat} (hx : x < 2 ^ (2 * params.degree)) :
    toPoly (BitVec.ofNat params.degree (reduceNat params x)) =
      toPoly (BitVec.ofNat (2 * params.degree) x) % P := by
  have hWidth : params.degree ≤ 2 * params.degree := by omega
  have hxAux : x < 2 ^ (params.degree + params.degree) := by
    simpa [two_mul] using hx
  have hAuxBound : reduceNatAux params params.degree x < 2 ^ params.degree :=
    reduceNatAux_lt_two_pow params le_rfl hxAux
  let aux := reduceNatAux params params.degree x
  let v : BitVec params.degree := BitVec.ofNat params.degree aux
  have hReduceNat : reduceNat params x = aux := by
    dsimp [aux]
    unfold reduceNat
    rw [Nat.mod_eq_of_lt hAuxBound]
  have hWideBound : aux < 2 ^ (2 * params.degree) := by
    dsimp [aux]
    exact lt_of_lt_of_le hAuxBound (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) hWidth)
  have hWideEq :
      (BitVec.ofNat (2 * params.degree) aux : BitVec (2 * params.degree)) =
        BitVec.zeroExtend (2 * params.degree) v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Extension.zeroExtend_toNat hWidth]
    dsimp [v, aux]
    rw [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hWideBound, Nat.mod_eq_of_lt hAuxBound]
  have hNarrowWide :
      toPoly v =
        toPoly (BitVec.ofNat (2 * params.degree) aux : BitVec (2 * params.degree)) := by
    rw [hWideEq]
    exact (Extension.toPoly_zeroExtend hWidth v).symm
  have hWideReduced :
      toPoly (BitVec.ofNat (2 * params.degree) aux : BitVec (2 * params.degree)) % P =
        toPoly (BitVec.ofNat (2 * params.degree) aux : BitVec (2 * params.degree)) := by
    rw [Polynomial.mod_eq_self_iff (hq0 := hP_ne_zero), hP_degree]
    apply toPoly_degree_of_lt_two_pow
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hWideBound]
    dsimp [aux]
    exact hAuxBound
  calc
    toPoly (BitVec.ofNat params.degree (reduceNat params x))
        = toPoly v := by
            dsimp [v]
            rw [hReduceNat]
    _ = toPoly (BitVec.ofNat (2 * params.degree) aux : BitVec (2 * params.degree)) :=
            hNarrowWide
    _ = toPoly (BitVec.ofNat (2 * params.degree) aux : BitVec (2 * params.degree)) % P :=
            hWideReduced.symm
    _ = toPoly (BitVec.ofNat (2 * params.degree) x) % P := by
            dsimp [aux]
            exact reduceNatAux_mod_eq params hP_ne_zero hP (n := params.degree) (x := x) le_rfl

/-- Reduce a natural-number polynomial encoding to the executable carrier. -/
def reduce (x : Nat) : ConcreteField params :=
  ofNat params (reduceNat params x)

/-- Polynomial semantics of executable reduction modulo a direct defining polynomial. -/
theorem toPoly_reduce {P : Polynomial (ZMod 2)}
    (hP_ne_zero : P ≠ 0)
    (hP : P = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : P.degree = params.degree)
    {x : Nat} (hx : x < 2 ^ (2 * params.degree)) :
    toPoly (toBitVec params (reduce params x)) =
      toPoly (BitVec.ofNat (2 * params.degree) x) % P := by
  change toPoly (BitVec.ofNat params.degree (reduceNat params x)) =
    toPoly (BitVec.ofNat (2 * params.degree) x) % P
  exact toPoly_reduceNat params hP_ne_zero hP hP_degree hx

/-- Carry-less multiplication of `n` low bits of `a` by a `width`-bit value stays bounded. -/
theorem clMulNat_lt_two_pow {a b width n : Nat} (hb : b < 2 ^ width) :
    clMulNat a b n < 2 ^ (width + n) := by
  induction n with
  | zero =>
      simp [clMulNat]
  | succ n ih =>
      simp [clMulNat]
      by_cases hbit : a.testBit n
      · simp [hbit]
        have hterm : b <<< n < 2 ^ (width + n) := by
          exact Nat.shiftLeft_lt hb
        have hxor : clMulNat a b n ^^^ (b <<< n) < 2 ^ (width + n) :=
          Nat.xor_lt_two_pow ih hterm
        exact lt_of_lt_of_le hxor
          (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) (by omega))
      · simp [hbit]
        exact lt_of_lt_of_le ih
          (pow_le_pow_right' (by decide : (1 : Nat) ≤ 2) (by omega))

/-- Carry-less multiplication followed by defining-polynomial reduction. -/
def mul (a b : ConcreteField params) : ConcreteField params :=
  reduce params (clMulNat (toNat params a) (toNat params b) params.degree)

/-- Squaring in the executable carrier. -/
def square (a : ConcreteField params) : ConcreteField params :=
  mul params a a

/-- Fast exponentiation by repeated squaring. -/
def pow (a : ConcreteField params) : Nat → ConcreteField params
  | 0 => one params
  | exponent + 1 =>
      let half := pow a ((exponent + 1) / 2)
      let halfSq := square params half
      if (exponent + 1) % 2 = 0 then halfSq else mul params halfSq a
termination_by exponent => exponent
decreasing_by
  omega

/-- Fermat-style inverse candidate. Correctness is proved after field certification. -/
def inv (a : ConcreteField params) : ConcreteField params :=
  if toNat params a = 0 then zero params
  else pow params a (2 ^ params.degree - 2)

/-- Repeated Frobenius-squaring trace accumulator. -/
def traceLoop : Nat → ConcreteField params → ConcreteField params → ConcreteField params
  | 0, acc, _cur => acc
  | steps + 1, acc, cur =>
      traceLoop steps (add params acc cur) (square params cur)

/-- Executable absolute-trace candidate `z + z^2 + ... + z^(2^(degree-1))`. -/
def traceValue (z : ConcreteField params) : ConcreteField params :=
  traceLoop params params.degree (zero params) z

/-- Polynomial basis `#[1, alpha, ..., alpha^(degree-1)]`. -/
def polynomialBasis : Array (ConcreteField params) :=
  Array.ofFn fun exponent : Fin params.degree ↦ pow params (root params) exponent.val

/-- Base constants for characteristic two. -/
def baseConstants : Array (ConcreteField params) :=
  #[zero params, one params]

instance instBEqConcreteField : BEq (ConcreteField params) :=
  inferInstanceAs (BEq (BitVec params.degree))

instance instLawfulBEqConcreteField : LawfulBEq (ConcreteField params) :=
  inferInstanceAs (LawfulBEq (BitVec params.degree))

instance instInhabitedConcreteField : Inhabited (ConcreteField params) :=
  ⟨zero params⟩

instance instZeroConcreteField : Zero (ConcreteField params) where
  zero := zero params

instance instOneConcreteField : One (ConcreteField params) where
  one := one params

instance instAddConcreteField : Add (ConcreteField params) where
  add := add params

instance instNegConcreteField : Neg (ConcreteField params) where
  neg := neg params

instance instSubConcreteField : Sub (ConcreteField params) where
  sub := sub params

instance instMulConcreteField : Mul (ConcreteField params) where
  mul := mul params

instance instPowConcreteField : Pow (ConcreteField params) Nat where
  pow := pow params

instance instInvConcreteField : Inv (ConcreteField params) where
  inv := inv params

instance instDivConcreteField : Div (ConcreteField params) where
  div a b := mul params a (inv params b)

instance instHDivConcreteField :
    HDiv (ConcreteField params) (ConcreteField params) (ConcreteField params) where
  hDiv a b := mul params a (inv params b)

/-- XOR addition is associative on the executable carrier. -/
theorem add_assoc (a b c : ConcreteField params) :
    add params (add params a b) c = add params a (add params b c) := by
  exact BitVec.xor_assoc a b c

/-- XOR addition is commutative on the executable carrier. -/
theorem add_comm (a b : ConcreteField params) :
    add params a b = add params b a := by
  exact BitVec.xor_comm a b

/-- Zero is a right identity for executable addition. -/
theorem add_zero (a : ConcreteField params) :
    add params a (zero params) = a := by
  change a ^^^ 0 = a
  exact BitVec.xor_zero

/-- Zero is a left identity for executable addition. -/
theorem zero_add (a : ConcreteField params) :
    add params (zero params) a = a := by
  change 0 ^^^ a = a
  exact BitVec.zero_xor

/-- Executable negation is additive inverse in characteristic two. -/
theorem neg_add_cancel (a : ConcreteField params) :
    add params (neg params a) a = zero params := by
  change a ^^^ a = 0
  exact BitVec.xor_self

/-- Parity form of natural scalar recursion for the XOR additive group. -/
theorem nsmul_succ (n : Nat) (x : ConcreteField params) :
    (if (n + 1) % 2 = 0 then zero params else x) =
      add params (if n % 2 = 0 then zero params else x) x := by
  have h_mod : (n + 1) % 2 = (n % 2 + 1) % 2 := Nat.add_mod n 1 2
  by_cases h : n % 2 = 0
  · rw [h, Nat.zero_add] at h_mod
    rw [h]
    have h_succ : (n + 1) % 2 = 1 := by omega
    rw [h_succ]
    simp only [↓reduceIte]
    change x = 0 ^^^ x
    exact (BitVec.zero_xor).symm
  · have h1 : n % 2 = 1 := Nat.mod_two_ne_zero.mp h
    rw [h1] at h_mod ⊢
    have h_succ : (n + 1) % 2 = 0 := by omega
    rw [h_succ]
    simp only [↓reduceIte]
    change 0 = x ^^^ x
    exact (BitVec.xor_self).symm

/-- Parity form of integer scalar recursion for the XOR additive group. -/
theorem zsmul_succ (n : Nat) (x : ConcreteField params) :
    (if (n + 1 : Int) % 2 = 0 then zero params else x) =
      add params (if (n : Int) % 2 = 0 then zero params else x) x := by
  norm_cast
  exact nsmul_succ params n x

private theorem int_neg_mod_two (n : Int) : (-n) % 2 = n % 2 := by
  simp only [Int.neg_emod_two]

/-- Parity form of negative integer scalar recursion for the XOR additive group. -/
theorem zsmul_neg (n : Nat) (x : ConcreteField params) :
    (if (Int.negSucc n) % 2 = 0 then zero params else x) =
      neg params (if (n + 1 : Int) % 2 = 0 then zero params else x) := by
  have h_neg : Int.negSucc n = - (n + 1 : Int) := rfl
  rw [h_neg]
  rw [int_neg_mod_two]
  simp
  rfl

instance instAddCommGroupConcreteField : AddCommGroup (ConcreteField params) where
  add := add params
  zero := zero params
  neg := neg params
  sub := sub params
  add_assoc := add_assoc params
  add_comm := add_comm params
  add_zero := add_zero params
  zero_add := zero_add params
  neg_add_cancel := neg_add_cancel params
  sub_eq_add_neg := by intro _ _; rfl
  nsmul := fun n x => if n % 2 = 0 then zero params else x
  zsmul := fun n x => if n % 2 = 0 then zero params else x
  nsmul_zero := fun _ => rfl
  nsmul_succ := nsmul_succ params
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := zsmul_succ params
  zsmul_neg' := zsmul_neg params

/-- Natural casts for characteristic-two executable fields use parity. -/
def natCast (n : Nat) : ConcreteField params :=
  if n % 2 = 0 then zero params else one params

instance instNatCastConcreteField : NatCast (ConcreteField params) where
  natCast := natCast params

@[simp]
theorem natCast_eq (n : Nat) : (↑n : ConcreteField params) = natCast params n :=
  rfl

theorem natCast_zero :
    natCast params 0 = zero params := by
  simp [natCast]

theorem natCast_succ (n : Nat) :
    natCast params (n + 1) = add params (natCast params n) (one params) := by
  unfold natCast
  by_cases h : n % 2 = 0
  · have h_succ : (n + 1) % 2 = 1 := by omega
    simp [h, h_succ, zero_add]
  · have h_succ : (n + 1) % 2 = 0 := by omega
    simp only [h, h_succ, ↓reduceIte]
    exact (neg_add_cancel params (one params)).symm

/-- Integer casts for characteristic-two executable fields use parity. -/
def intCast (n : Int) : ConcreteField params :=
  if n % 2 = 0 then zero params else one params

instance instIntCastConcreteField : IntCast (ConcreteField params) where
  intCast := intCast params

@[simp]
theorem intCast_eq (n : Int) : (↑n : ConcreteField params) = intCast params n :=
  rfl

theorem intCast_ofNat (n : Nat) :
    intCast params (n : Int) = natCast params n := by
  unfold intCast natCast
  by_cases h : n % 2 = 0
  · have h_int : (n : Int) % 2 = 0 := by norm_cast
    simp [h, h_int]
  · have h_n : n % 2 = 1 := by omega
    have h_int : (n : Int) % 2 = 1 := by norm_cast
    simp [h_n, h_int]

theorem intCast_negSucc (n : Nat) :
    intCast params (Int.negSucc n) = neg params (natCast params (n + 1)) := by
  by_cases h_mod : (n + 1) % 2 = 0
  · have h_neg : (-(n + 1 : Int)) % 2 = 0 := by omega
    unfold intCast natCast
    have int_neg_succ : Int.negSucc n = -(n + 1 : Int) := by rfl
    rw [int_neg_succ, h_neg, h_mod]
    rfl
  · have h_neg : (-(n + 1 : Int)) % 2 = 1 := by omega
    unfold intCast natCast
    have int_neg_succ : Int.negSucc n = -(n + 1 : Int) := by rfl
    rw [int_neg_succ, h_neg]
    simp [h_mod, neg]

/-- Plain equivalence between the executable carrier and its bounded natural encoding. -/
noncomputable def equivFin : ConcreteField params ≃ Fin (2 ^ params.degree) where
  toFun a := ⟨toNat params a, (toBitVec params a).isLt⟩
  invFun i := ofNat params i.val
  left_inv := by
    intro a
    apply BitVec.eq_of_toNat_eq
    simp [toNat, toBitVec, ofNat, ofBitVec]
  right_inv := by
    intro i
    apply Fin.ext
    simp [toNat, toBitVec, ofNat, ofBitVec]

/-- Fintype instance for the raw executable carrier. -/
noncomputable instance instFintypeConcreteField : Fintype (ConcreteField params) :=
  Fintype.ofEquiv (Fin (2 ^ params.degree)) (equivFin params).symm

/-- Finite instance for the raw executable carrier. -/
instance instFiniteConcreteField : Finite (ConcreteField params) :=
  Fintype.finite (instFintypeConcreteField params)

/-- The executable carrier has `2^degree` bit-patterns. -/
theorem concreteField_card :
    Fintype.card (ConcreteField params) = 2 ^ params.degree := by
  rw [Fintype.card_congr (equivFin params)]
  simp

section QuotientCompatibility

variable {data : DefiningPolynomialData}

/-- Canonical map from the executable bit-vector carrier to the quotient specification. -/
noncomputable def toSpec (a : ConcreteField params) : SpecField data :=
  AdjoinRoot.mk (polynomial data) (toPoly (toBitVec params a))

/-- The executable-to-specification map is injective when the defining degree matches. -/
theorem toSpec_injective (hDegree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree) :
    Function.Injective (toSpec params (data := data)) := by
  intro a b h
  unfold toSpec at h
  have h_sub :
      toPoly (toBitVec params a) - toPoly (toBitVec params b) =
        toPoly (toBitVec params a ^^^ toBitVec params b) := by
    rw [toPoly_xor]
    ring_nf
    exact ZMod2Poly.sub_eq_add (toPoly (toBitVec params a)) (toPoly (toBitVec params b))
  let diff := toBitVec params a ^^^ toBitVec params b
  have h_deg : (toPoly diff).degree < params.degree :=
    toPoly_degree_lt_w hDegree_pos diff
  have h_dvd :
      polynomial data ∣
        (toPoly (toBitVec params a) - toPoly (toBitVec params b)) := by
    rw [AdjoinRoot.mk_eq_mk] at h
    exact h
  have h_zero : toPoly diff = 0 := by
    by_contra h_nz
    have h_diff_nz :
        toPoly (toBitVec params a) - toPoly (toBitVec params b) ≠ 0 := by
      rw [h_sub]
      exact h_nz
    have h_deg_poly :
        (polynomial data).degree ≤
          (toPoly (toBitVec params a) - toPoly (toBitVec params b)).degree :=
      Polynomial.degree_le_of_dvd (h1 := h_dvd) (h2 := h_diff_nz)
    have h_eq_deg :
        (toPoly (toBitVec params a) - toPoly (toBitVec params b)).degree =
          (toPoly diff).degree := by
      rw [h_sub.symm]
    rw [hDegree, h_eq_deg] at h_deg_poly
    exact not_le_of_gt h_deg h_deg_poly
  have h_diff_eq_zero : diff = 0 := by
    by_contra h_nz
    have h_diff_ne_zero : diff ≠ 0 := h_nz
    rw [← toPoly_ne_zero_iff_ne_zero (v := diff)] at h_diff_ne_zero
    exact h_diff_ne_zero h_zero
  exact BitVec.xor_eq_zero_iff.mp h_diff_eq_zero

/-- The executable zero maps to the quotient zero. -/
theorem toSpec_zero :
    toSpec params (data := data) (zero params) = 0 := by
  simp [toSpec, zero, ofNat, ofBitVec, toBitVec, toPoly_zero_eq_zero]

/-- The executable one maps to the quotient one. -/
theorem toSpec_one (hDegree_pos : 0 < params.degree) :
    toSpec params (data := data) (one params) = 1 := by
  simp [toSpec, one, ofNat, ofBitVec, toBitVec, toPoly_one_eq_one hDegree_pos, map_one]

/-- The executable polynomial-basis generator maps to the quotient root. -/
theorem toSpec_root (hDegree_root : 1 < params.degree) :
    toSpec params (data := data) (root params) = Extension.root data := by
  unfold toSpec root ofNat ofBitVec toBitVec Extension.root
  congr
  change BinaryField.toPoly (BitVec.ofNat params.degree 2) =
    (Polynomial.X : Polynomial (ZMod 2))
  let oneShift : BitVec params.degree := BitVec.ofNat params.degree (1 <<< 1)
  have hvec : (BitVec.ofNat params.degree 2 : BitVec params.degree) = oneShift := by
    unfold oneShift
    congr
  rw [hvec]
  have hpoly : BinaryField.toPoly oneShift = (Polynomial.X : Polynomial (ZMod 2)) := by
    unfold oneShift
    simpa [BitVec.ofNat_eq_ofNat] using
      (Extension.toPoly_one_shiftLeft (w := params.degree) 1 hDegree_root)
  exact hpoly

/-- Executable XOR addition maps to quotient addition. -/
theorem toSpec_add (a b : ConcreteField params) :
    toSpec params (data := data) (add params a b) =
      toSpec params (data := data) a + toSpec params (data := data) b := by
  unfold toSpec add ofBitVec toBitVec
  rw [toPoly_xor]
  exact map_add (AdjoinRoot.mk (polynomial data)) (toPoly a) (toPoly b)

/-- Executable characteristic-two negation maps to quotient negation. -/
theorem toSpec_neg (a : ConcreteField params) :
    toSpec params (data := data) (neg params a) =
      -toSpec params (data := data) a := by
  unfold toSpec neg toBitVec
  rw [← map_neg (AdjoinRoot.mk (polynomial data))]
  congr
  exact (ZMod2Poly.neg_eq_self (toPoly a)).symm

/-- Executable characteristic-two subtraction maps to quotient subtraction. -/
theorem toSpec_sub (a b : ConcreteField params) :
    toSpec params (data := data) (sub params a b) =
      toSpec params (data := data) a - toSpec params (data := data) b := by
  rw [sub, toSpec_add, sub_eq_add_neg, ← toSpec_neg]
  rfl

/-- Executable multiplication maps to quotient multiplication. -/
theorem toSpec_mul
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (a b : ConcreteField params) :
    toSpec params (data := data) (mul params a b) =
      toSpec params (data := data) a * toSpec params (data := data) b := by
  unfold toSpec mul
  have hMulBound : clMulNat (toNat params a) (toNat params b) params.degree <
      2 ^ (2 * params.degree) := by
    have hb : (toNat params b) < 2 ^ params.degree := (toBitVec params b).isLt
    have h := clMulNat_lt_two_pow
      (a := toNat params a) (b := toNat params b)
      (width := params.degree) (n := params.degree) hb
    simpa [two_mul] using h
  have hReduce := toPoly_reduce params (P := polynomial data)
    (polynomial_ne_zero data) hP hP_degree hMulBound
  change AdjoinRoot.mk (polynomial data)
      (toPoly (toBitVec params (reduce params
        (clMulNat (toNat params a) (toNat params b) params.degree)))) =
    AdjoinRoot.mk (polynomial data) (toPoly (toBitVec params a)) *
      AdjoinRoot.mk (polynomial data) (toPoly (toBitVec params b))
  rw [hReduce]
  have hCl :
      toPoly (BitVec.ofNat (2 * params.degree)
        (clMulNat (toNat params a) (toNat params b) params.degree)) =
        toPoly (toBitVec params a) * toPoly (toBitVec params b) := by
    simpa [toNat] using Extension.toPoly_clMulNat (toBitVec params a) (toBitVec params b)
  rw [hCl]
  rw [← map_mul (AdjoinRoot.mk (polynomial data)), AdjoinRoot.mk_eq_mk]
  apply dvd_sub_comm.mp
  exact CanonicalEuclideanDomain.dvd_sub_mod
    (a := toPoly (toBitVec params a) * toPoly (toBitVec params b))
    (b := polynomial data)

/-- Executable fast exponentiation maps to quotient exponentiation. -/
theorem toSpec_pow
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a : ConcreteField params) :
    ∀ n : Nat,
      toSpec params (data := data) (pow params a n) =
        (toSpec params (data := data) a) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [pow, toSpec_one params (data := data) hDegree_pos]
      | succ exponent =>
          have hhalf : (exponent + 1) / 2 < exponent + 1 := by
            exact Nat.div_lt_self (by omega) (by norm_num)
          have hih := ih ((exponent + 1) / 2) hhalf
          rw [pow]
          by_cases hEven : (exponent + 1) % 2 = 0
          · simp [hEven, square]
            rw [toSpec_mul params (data := data) hP hP_degree, hih]
            rw [← pow_add]
            congr 1
            have hmod := Nat.mod_add_div (exponent + 1) 2
            omega
          · simp [hEven, square]
            rw [toSpec_mul params (data := data) hP hP_degree,
              toSpec_mul params (data := data) hP hP_degree, hih]
            rw [← pow_add, ← pow_succ]
            congr 1
            have hmod := Nat.mod_add_div (exponent + 1) 2
            have hmod_lt : (exponent + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega

/-- A zero natural encoding denotes executable zero. -/
theorem eq_zero_of_toNat_eq_zero {a : ConcreteField params}
    (h : toNat params a = 0) :
    a = zero params := by
  apply BitVec.eq_of_toNat_eq
  simpa [toNat, toBitVec, zero, ofNat, ofBitVec] using h

/-- A nonzero executable element has nonzero natural encoding. -/
theorem toNat_ne_zero_of_ne_zero {a : ConcreteField params}
    (h : a ≠ zero params) :
    toNat params a ≠ 0 := by
  intro hnat
  exact h (eq_zero_of_toNat_eq_zero params hnat)

/-- Executable zero and one are distinct for positive widths. -/
theorem zero_ne_one (hDegree_pos : 0 < params.degree) :
    zero params ≠ one params := by
  intro h
  have hnat := congrArg (toNat params) h
  simp [toNat, toBitVec, zero, one, ofNat, ofBitVec] at hnat
  omega

/-- The quotient image of a nonzero executable element is nonzero. -/
theorem toSpec_ne_zero
    (hDegree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    {a : ConcreteField params} (h : a ≠ zero params) :
    toSpec params (data := data) a ≠ 0 := by
  intro hz
  have hz' : toSpec params (data := data) a =
      toSpec params (data := data) (zero params) := by
    simpa [toSpec_zero params (data := data)] using hz
  exact h (toSpec_injective params (data := data) hDegree hDegree_pos hz')

/-- Executable inversion maps to the Fermat inverse exponent in the quotient. -/
theorem toSpec_inv_of_ne_zero
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    {a : ConcreteField params} (h : a ≠ zero params) :
    toSpec params (data := data) (inv params a) =
      (toSpec params (data := data) a) ^ (2 ^ params.degree - 2) := by
  unfold inv
  have hnat : toNat params a ≠ 0 := toNat_ne_zero_of_ne_zero params h
  simp [hnat]
  exact toSpec_pow params (data := data) hP hP_degree hDegree_pos a (2 ^ params.degree - 2)

/-- Fast executable power satisfies the monoid successor law. -/
theorem pow_succ_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (n : Nat) (a : ConcreteField params) :
    pow params a (n + 1) = mul params (pow params a n) a := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_pow params (data := data) hP hP_degree hDegree_pos,
    toSpec_mul params (data := data) hP hP_degree,
    toSpec_pow params (data := data) hP hP_degree hDegree_pos]
  exact pow_succ (toSpec params (data := data) a) n

/-- Associativity of executable multiplication, transported through the quotient. -/
theorem mul_assoc_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a b c : ConcreteField params) :
    mul params (mul params a b) c = mul params a (mul params b c) := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  repeat rw [toSpec_mul params (data := data) hP hP_degree]
  exact _root_.mul_assoc (toSpec params (data := data) a)
    (toSpec params (data := data) b) (toSpec params (data := data) c)

/-- Left identity for executable multiplication. -/
theorem one_mul_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a : ConcreteField params) :
    mul params (one params) a = a := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_mul params (data := data) hP hP_degree,
    toSpec_one params (data := data) hDegree_pos]
  exact _root_.one_mul (toSpec params (data := data) a)

/-- Right identity for executable multiplication. -/
theorem mul_one_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a : ConcreteField params) :
    mul params a (one params) = a := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_mul params (data := data) hP hP_degree,
    toSpec_one params (data := data) hDegree_pos]
  exact _root_.mul_one (toSpec params (data := data) a)

/-- Left distributivity for executable multiplication. -/
theorem left_distrib_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a b c : ConcreteField params) :
    mul params a (add params b c) =
      add params (mul params a b) (mul params a c) := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_add params (data := data), toSpec_mul params (data := data) hP hP_degree,
    toSpec_add params (data := data), toSpec_mul params (data := data) hP hP_degree,
    toSpec_mul params (data := data) hP hP_degree]
  exact _root_.mul_add (toSpec params (data := data) a)
    (toSpec params (data := data) b) (toSpec params (data := data) c)

/-- Right distributivity for executable multiplication. -/
theorem right_distrib_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a b c : ConcreteField params) :
    mul params (add params a b) c =
      add params (mul params a c) (mul params b c) := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_add params (data := data), toSpec_mul params (data := data) hP hP_degree,
    toSpec_add params (data := data), toSpec_mul params (data := data) hP hP_degree,
    toSpec_mul params (data := data) hP hP_degree]
  exact _root_.add_mul (toSpec params (data := data) a)
    (toSpec params (data := data) b) (toSpec params (data := data) c)

/-- Left zero for executable multiplication. -/
theorem zero_mul_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a : ConcreteField params) :
    mul params (zero params) a = zero params := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_mul params (data := data) hP hP_degree,
    toSpec_zero params (data := data)]
  exact MulZeroClass.zero_mul (toSpec params (data := data) a)

/-- Right zero for executable multiplication. -/
theorem mul_zero_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a : ConcreteField params) :
    mul params a (zero params) = zero params := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_mul params (data := data) hP hP_degree,
    toSpec_zero params (data := data)]
  exact MulZeroClass.mul_zero (toSpec params (data := data) a)

/-- Commutativity of executable multiplication. -/
theorem mul_comm_of_spec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a b : ConcreteField params) :
    mul params a b = mul params b a := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  repeat rw [toSpec_mul params (data := data) hP hP_degree]
  exact _root_.mul_comm (toSpec params (data := data) a)
    (toSpec params (data := data) b)

/-- Executable inverse of zero is zero. -/
theorem inv_zero :
    inv params (zero params) = zero params := by
  unfold inv
  simp [toNat, toBitVec, zero, ofNat, ofBitVec]

/-- Division is multiplication by inverse. -/
theorem div_eq_mul_inv (a b : ConcreteField params) :
    (instDivConcreteField params).div a b = mul params a (inv params b) :=
  rfl

/-- Nontriviality witness for positive-width executable fields. -/
theorem exists_pair_ne (hDegree_pos : 0 < params.degree) :
    ∃ x y : ConcreteField params, x ≠ y :=
  ⟨zero params, one params, zero_ne_one params hDegree_pos⟩

/-- Ring structure for a certified executable direct binary extension. -/
@[reducible]
def instRingConcreteFieldOfSpec
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree) :
    Ring (ConcreteField params) where
  add := add params
  zero := zero params
  neg := neg params
  sub := sub params
  mul := mul params
  one := one params
  nsmul := fun n x => if n % 2 = 0 then zero params else x
  zsmul := fun n x => if n % 2 = 0 then zero params else x
  npow := fun n x => pow params x n
  add_assoc := add_assoc params
  add_comm := add_comm params
  add_zero := add_zero params
  zero_add := zero_add params
  neg_add_cancel := neg_add_cancel params
  sub_eq_add_neg := by intro _ _; rfl
  nsmul_zero := fun _ => rfl
  nsmul_succ := nsmul_succ params
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := zsmul_succ params
  zsmul_neg' := zsmul_neg params
  mul_assoc := mul_assoc_of_spec params (data := data) hP hP_degree hDegree_pos
  one_mul := one_mul_of_spec params (data := data) hP hP_degree hDegree_pos
  mul_one := mul_one_of_spec params (data := data) hP hP_degree hDegree_pos
  left_distrib := left_distrib_of_spec params (data := data) hP hP_degree hDegree_pos
  right_distrib := right_distrib_of_spec params (data := data) hP hP_degree hDegree_pos
  zero_mul := zero_mul_of_spec params (data := data) hP hP_degree hDegree_pos
  mul_zero := mul_zero_of_spec params (data := data) hP hP_degree hDegree_pos
  natCast := natCast params
  natCast_zero := natCast_zero params
  natCast_succ := natCast_succ params
  intCast := intCast params
  intCast_ofNat := intCast_ofNat params
  intCast_negSucc := intCast_negSucc params
  npow_zero := by
    intro x
    change pow params x 0 = one params
    simp [pow]
  npow_succ := by
    intro n x
    change pow params x (n + 1) = mul params (pow params x n) x
    exact pow_succ_of_spec params (data := data) hP hP_degree hDegree_pos n x

/-- Multiplication by the executable inverse cancels nonzero elements. -/
theorem mul_inv_cancel_of_spec [Fact (Irreducible (polynomial data))]
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree)
    (a : ConcreteField params) (h : a ≠ zero params) :
    mul params a (inv params a) = one params := by
  apply toSpec_injective params (data := data) hP_degree hDegree_pos
  rw [toSpec_mul params (data := data) hP hP_degree,
    toSpec_one params (data := data) hDegree_pos,
    toSpec_inv_of_ne_zero params (data := data) hP hP_degree hDegree_pos h]
  rw [← pow_succ']
  have h_exp : 2 ^ params.degree - 2 + 1 = 2 ^ params.degree - 1 := by
    have htwo : 2 ≤ 2 ^ params.degree := by
      exact Nat.succ_le_of_lt (Nat.one_lt_two_pow hDegree_pos.ne')
    omega
  rw [h_exp]
  have hcard :
      Fintype.card (SpecField data) = 2 ^ params.degree := by
    have hdata : data.degree = params.degree := by
      have hdegNat :
          (polynomial data).natDegree = params.degree :=
        (Polynomial.degree_eq_iff_natDegree_eq (polynomial_ne_zero data)).mp hP_degree
      rw [polynomial_natDegree data] at hdegNat
      exact hdegNat
    rw [Extension.specField_card data, hdata]
  have hq_ne :
      toSpec params (data := data) a ≠ 0 :=
    toSpec_ne_zero params (data := data) hP_degree hDegree_pos h
  have hfinite :=
    FiniteField.pow_card_sub_one_eq_one
      (K := SpecField data) (toSpec params (data := data) a) hq_ne
  rwa [hcard] at hfinite

/-- Division-ring structure for a certified executable direct binary extension. -/
@[reducible]
def instDivisionRingConcreteFieldOfSpec [Fact (Irreducible (polynomial data))]
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree) :
    DivisionRing (ConcreteField params) where
  toRing := instRingConcreteFieldOfSpec params (data := data) hP hP_degree hDegree_pos
  inv := inv params
  div := fun a b => mul params a (inv params b)
  exists_pair_ne := exists_pair_ne params hDegree_pos
  mul_inv_cancel := by
    intro a h
    change mul params a (inv params a) = one params
    exact mul_inv_cancel_of_spec params (data := data) hP hP_degree hDegree_pos
      a (by simpa using h)
  inv_zero := by
    change inv params (zero params) = zero params
    exact inv_zero params
  div_eq_mul_inv := by
    intro a b
    rfl
  qsmul := _
  nnqsmul := _

/-- Field structure for a certified executable direct binary extension. -/
@[reducible]
def instFieldConcreteFieldOfSpec [Fact (Irreducible (polynomial data))]
    (hP : polynomial data = X ^ params.degree + sparsePolynomial params.tailExponents)
    (hP_degree : (polynomial data).degree = params.degree)
    (hDegree_pos : 0 < params.degree) :
    Field (ConcreteField params) where
  toDivisionRing :=
    instDivisionRingConcreteFieldOfSpec params (data := data) hP hP_degree hDegree_pos
  mul_comm := by
    intro a b
    change mul params a b = mul params b a
    exact mul_comm_of_spec params (data := data) hP hP_degree hDegree_pos a b

end QuotientCompatibility

end Concrete

end Extension

end BinaryField
