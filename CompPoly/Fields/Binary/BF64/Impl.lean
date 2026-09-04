/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Schleicher
-/
module

public import CompPoly.Fields.Binary.BF64.Reduce
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The computable `GF(2^64)` carrier

An element is a 64-bit word whose bit `i` is the coefficient of `x^i`. Addition is `xor`,
multiplication is a carry-less product followed by `reduce`, and inversion is the
Itoh-Tsujii addition chain. The carrier maps into `AdjoinRoot basePoly` through
`BF64.toQuot`, so Mathlib's field theory applies while the operations stay executable.

## Main definitions

* `BF64` — the carrier, `BitVec 64`, with `Add`, `Mul`, `Inv`, `CommRing` and `Field`.
* `BF64.toQuot` — the bridge into `BF64Quot`.
* `BF64.powTwoPow` — repeated squaring, `a ^ (2 ^ k)`.
* `BF64.invItohTsujii` — inversion by the Itoh-Tsujii addition chain.

## Main statements

* `BF64.toQuot_add`, `BF64.toQuot_mul` — the bridge is a ring homomorphism.
* `BF64.toQuot_injective`, `BF64.toQuot_surjective` — it is a bijection.
* `BF64.mul_invItohTsujii` — the addition chain really inverts.
* `BF64.card_bf64` — `Fintype.card BF64 = 2 ^ 64`.

## Implementation notes

The algebraic instances are written out field-by-field rather than obtained from
`Function.Injective.commRing`. That transport takes the bridge map as *data*, which makes
the whole structure noncomputable and shadows the computable `Mul` and `Pow`; because
`CompPoly.Extension.Ext.mul` reaches through the base field's `Field` instance, a
noncomputable base field would take the extension in `BF64/Ext3.lean` down with it too.
The `#guard` checks in `tests/CompPolyTests/Fields/Binary/BF64.lean` run the compiled
arithmetic and so fail the build if this ever regresses.

`Pow` is `npowBinRec`, binary exponentiation, matching
`CompPoly.Extension.Ext.instPowNat`. The linear `npowRec` would need `2 ^ 64`
multiplications for a full-order exponent and is unusable in the kernel.
-/

@[expose] public section

open Polynomial BinaryField

/-- `GF(2^64)` in its computable, machine representation: a 64-bit word whose bit `i` is
the coefficient of `x^i`. -/
abbrev BF64 : Type := BitVec 64

namespace BF64

instance : Zero BF64 := ⟨(0 : BitVec 64)⟩
instance : One BF64 := ⟨(1 : BitVec 64)⟩

/-- Addition in characteristic two is `xor`. -/
instance : Add BF64 := ⟨fun a b => a ^^^ b⟩

/-- Negation is the identity in characteristic two. -/
instance : Neg BF64 := ⟨fun a => a⟩

instance : Sub BF64 := ⟨fun a b => a ^^^ b⟩

/-- Multiplication: the carry-less product, reduced modulo the modulus. -/
instance : Mul BF64 :=
  ⟨fun a b => reduce (carryLessMul (w := 128) a b)⟩

/-- The polynomial denoted by a carrier value. -/
noncomputable def toPolyBF64 (a : BF64) : Polynomial (ZMod 2) :=
  toPoly (a : BitVec 64)

/-- The bridge into the quotient. -/
noncomputable def toQuot (a : BF64) : BF64Quot :=
  AdjoinRoot.mk basePoly (toPolyBF64 a)

/-! ## Equation lemmas for the operations -/

theorem add_def (a b : BF64) : a + b = a ^^^ b := rfl

theorem mul_def (a b : BF64) : a * b = reduce (carryLessMul (w := 128) a b) := rfl

/-! ## The bridge is a ring homomorphism -/

@[simp] theorem toPolyBF64_zero : toPolyBF64 0 = 0 := by
  show toPoly (0 : BitVec 64) = 0
  exact toPoly_zero_eq_zero

@[simp] theorem toQuot_zero : toQuot 0 = 0 := by
  rw [toQuot, toPolyBF64_zero, map_zero]

@[simp] theorem toPolyBF64_add (a b : BF64) :
    toPolyBF64 (a + b) = toPolyBF64 a + toPolyBF64 b := by
  rw [toPolyBF64, toPolyBF64, toPolyBF64, add_def]
  exact toPoly_xor _ _

@[simp] theorem toQuot_add (a b : BF64) : toQuot (a + b) = toQuot a + toQuot b := by
  rw [toQuot, toQuot, toQuot, toPolyBF64_add, map_add]

/-- Multiplication agrees with the quotient's, because `reduce` computes the remainder. -/
@[simp] theorem toQuot_mul (a b : BF64) : toQuot (a * b) = toQuot a * toQuot b := by
  rw [toQuot, toQuot, toQuot, ← map_mul, toPolyBF64, mul_def, toPoly_reduce,
    toPoly_carryLessMul _ _ (by omega)]
  rw [AdjoinRoot.mk_eq_mk, toPolyBF64, toPolyBF64]
  exact ⟨-(toPoly a * toPoly b / basePoly), by
    rw [EuclideanDomain.mod_eq_sub_mul_div]; ring⟩

/-- Distinct carrier values denote distinct quotient elements.

A difference of two carrier values has degree below 64, while the modulus has degree
exactly 64, so the modulus can divide it only when it is zero. -/
theorem toQuot_injective : Function.Injective toQuot := by
  intro a b h
  have hsub : toPolyBF64 a - toPolyBF64 b = toPoly (a ^^^ b) := by
    rw [toPoly_xor, toPolyBF64, toPolyBF64]
    exact ZMod2Poly.sub_eq_add _ _
  have hdvd : basePoly ∣ toPolyBF64 a - toPolyBF64 b := AdjoinRoot.mk_eq_mk.mp h
  have hzero : toPoly (a ^^^ b) = 0 := by
    by_contra hnz
    have hne : toPolyBF64 a - toPolyBF64 b ≠ 0 := by rw [hsub]; exact hnz
    have hle := Polynomial.degree_le_of_dvd hdvd hne
    rw [hsub, basePoly_degree] at hle
    exact absurd (toPoly_degree_lt_w (w := 64) (by norm_num) (a ^^^ b)) (not_lt.mpr hle)
  have hxor : (a ^^^ b : BitVec 64) = 0 := by
    by_contra hnz
    exact ((toPoly_ne_zero_iff_ne_zero (a ^^^ b)).mpr hnz) hzero
  have : a = b := by
    have := congrArg (fun v => v ^^^ b) hxor
    simpa [BitVec.xor_assoc] using this
  exact this

/-! ## Algebraic structure

Every law is discharged by pushing through the injective `toQuot` into the quotient,
where it holds because `BF64Quot` is a commutative ring. The instances are
built field-by-field rather than by `Function.Injective.commRing`, because that transport
takes `toQuot` as data and would make the operations noncomputable.
-/

@[simp] theorem toPolyBF64_one : toPolyBF64 1 = 1 :=
  toPoly_one_eq_one (w := 64) (by norm_num)

@[simp] theorem toQuot_one : toQuot 1 = 1 := by
  rw [toQuot, toPolyBF64_one, map_one]

theorem toQuot_inj {a b : BF64} : toQuot a = toQuot b ↔ a = b :=
  ⟨fun h => toQuot_injective h, fun h => h ▸ rfl⟩

/-- Addition is self-cancelling: the field has characteristic two. -/
theorem add_self (a : BF64) : a + a = 0 := BitVec.xor_self

/-! ### Scalar and power operations

In characteristic two an integer scalar multiple collapses to a parity test, and the
natural- and integer-number casts collapse likewise. Defining them in that closed form
keeps them computable and makes the transport conditions immediate.
-/

instance : SMul ℕ BF64 := ⟨nsmulRec⟩
instance : SMul ℤ BF64 := ⟨zsmulRec nsmulRec⟩
instance : NatCast BF64 := ⟨Nat.unaryCast⟩
instance : IntCast BF64 := ⟨Int.castDef⟩
instance : Pow BF64 ℕ := ⟨fun a n => npowBinRec n a⟩

theorem npow_def (a : BF64) (n : ℕ) : a ^ n = npowBinRec n a := rfl

/-! ### The commutative-ring structure

Every law is discharged by pushing through the injective `toQuot` into `BF64Quot`,
where it holds because the quotient is a commutative ring. The instances are written out
field-by-field rather than via `Function.Injective.commRing`: that transport takes `toQuot`
as *data*, which would make the whole structure noncomputable and shadow the computable
operations. This mirrors `CompPoly.Extension.Ext.instCommRing`.
-/

theorem toQuot_neg (a : BF64) : toQuot (-a) = -toQuot a := by
  show toQuot a = -toQuot a
  rw [eq_neg_iff_add_eq_zero, ← toQuot_add, add_self, toQuot_zero]

theorem toQuot_sub (a b : BF64) : toQuot (a - b) = toQuot a - toQuot b := by
  show toQuot (a + b) = toQuot a - toQuot b
  rw [toQuot_add, sub_eq_add_neg]
  congr 1
  rw [← toQuot_neg b]
  rfl

instance : AddCommGroup BF64 where
  add_assoc a b c := toQuot_injective (by simp only [toQuot_add, add_assoc])
  zero_add a := toQuot_injective (by simp only [toQuot_add, toQuot_zero, zero_add])
  add_zero a := toQuot_injective (by simp only [toQuot_add, toQuot_zero, add_zero])
  add_comm a b := toQuot_injective (by simp only [toQuot_add, add_comm])
  neg_add_cancel a :=
    toQuot_injective (by simp only [toQuot_add, toQuot_neg, toQuot_zero, neg_add_cancel])
  sub_eq_add_neg a b :=
    toQuot_injective (by simp only [toQuot_sub, toQuot_add, toQuot_neg, sub_eq_add_neg])
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul := zsmulRec nsmulRec
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl

/-- `npowBinRec` agrees with the linear `npowRec`, so the power can be reasoned about by
ordinary recursion on the exponent while still *evaluating* by binary exponentiation.
Mathlib's `npowBinRec_succ` needs a `Semigroup`, which is not available until `mul_assoc`
below, so associativity is supplied here from the quotient. -/
theorem npow_eq_npowRec (a : BF64) (n : ℕ) : a ^ n = npowRec n a := by
  have hassoc : ∀ x y z : BF64, x * y * z = x * (y * z) := fun x y z =>
    toQuot_injective (by simp only [toQuot_mul, mul_assoc])
  let _ : Semigroup BF64 := { mul := (· * ·), mul_assoc := hassoc }
  rw [npow_def, ← npowBinRecAuto, ← npowRec_eq_npowBinRec]

theorem toQuot_npow (a : BF64) (n : ℕ) : toQuot (a ^ n) = toQuot a ^ n := by
  induction n with
  | zero => rw [npow_eq_npowRec, npowRec, pow_zero, toQuot_one]
  | succ k ih => rw [npow_eq_npowRec, npowRec, ← npow_eq_npowRec, toQuot_mul, ih, pow_succ]

/-- The quotient inherits characteristic two from `GF(2)`. -/
instance : CharP (BF64Quot) 2 := by
  have : CharP (ZMod 2) 2 := inferInstance
  exact charP_of_injective_algebraMap' (ZMod 2) 2

theorem toQuot_natCast (n : ℕ) : toQuot (n : BF64) = (n : BF64Quot) := by
  induction n with
  | zero => show toQuot 0 = _; rw [toQuot_zero, Nat.cast_zero]
  | succ k ih =>
    show toQuot ((k : BF64) + 1) = _
    rw [toQuot_add, ih, toQuot_one, Nat.cast_succ]

instance : CommRing BF64 where
  left_distrib a b c := toQuot_injective (by simp only [toQuot_mul, toQuot_add, mul_add])
  right_distrib a b c := toQuot_injective (by simp only [toQuot_mul, toQuot_add, add_mul])
  zero_mul a := toQuot_injective (by simp only [toQuot_mul, toQuot_zero, zero_mul])
  mul_zero a := toQuot_injective (by simp only [toQuot_mul, toQuot_zero, mul_zero])
  mul_assoc a b c := toQuot_injective (by simp only [toQuot_mul, mul_assoc])
  one_mul a := toQuot_injective (by simp only [toQuot_mul, toQuot_one, one_mul])
  mul_one a := toQuot_injective (by simp only [toQuot_mul, toQuot_one, mul_one])
  mul_comm a b := toQuot_injective (by simp only [toQuot_mul, mul_comm])
  npow n x := x ^ n
  npow_zero x := toQuot_injective (by simp only [toQuot_npow, toQuot_one, pow_zero])
  npow_succ n x := toQuot_injective (by simp only [toQuot_npow, toQuot_mul, pow_succ])
  natCast n := (n : BF64)
  natCast_zero := toQuot_injective (by simp only [toQuot_natCast, toQuot_zero, Nat.cast_zero])
  natCast_succ n :=
    toQuot_injective (by simp only [toQuot_natCast, toQuot_add, toQuot_one, Nat.cast_succ])
  intCast n := (n : BF64)
  intCast_ofNat n := rfl
  intCast_negSucc n := rfl

/-! ### Inversion by Itoh-Tsujii

Inversion uses the Itoh-Tsujii addition chain: `a⁻¹ = a^(2^64 - 2) = (a^(2^63 - 1))^2`,
with `a^(2^k - 1)` built along `1, 2, 3, 6, 7, 14, 15, 30, 31, 62, 63`. This is an
explicit algorithm rather than an existence proof, so the resulting inverse evaluates.
`BF128Ghash.inv_itoh_tsujii` is the analogous chain at degree 128.
-/

/-- Repeated squaring: `a ^ (2 ^ k)`. -/
def powTwoPow (a : BF64) (k : ℕ) : BF64 :=
  match k with
  | 0 => a
  | n + 1 => powTwoPow (a * a) n

theorem toQuot_powTwoPow (a : BF64) (k : ℕ) :
    toQuot (powTwoPow a k) = toQuot a ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp only [powTwoPow, pow_zero, pow_one]
  | succ n ih =>
    simp only [powTwoPow]
    rw [ih, toQuot_mul, ← sq, ← pow_mul, pow_succ, mul_comm]

/-- The multiplicative inverse, by the Itoh-Tsujii addition chain, with `0⁻¹ = 0`. -/
def invItohTsujii (a : BF64) : BF64 :=
  if a = 0 then 0 else
    let u1 := a
    let u2 := powTwoPow u1 1 * u1
    let u3 := powTwoPow u2 1 * u1
    let u6 := powTwoPow u3 3 * u3
    let u7 := powTwoPow u6 1 * u1
    let u14 := powTwoPow u7 7 * u7
    let u15 := powTwoPow u14 1 * u1
    let u30 := powTwoPow u15 15 * u15
    let u31 := powTwoPow u30 1 * u1
    let u62 := powTwoPow u31 31 * u31
    let u63 := powTwoPow u62 1 * u1
    u63 * u63

/-- The exponent identity behind one Itoh-Tsujii step. -/
private theorem chain_exponent (n m : ℕ) :
    (2 ^ n - 1) * 2 ^ m + (2 ^ m - 1) = 2 ^ (n + m) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_add]
  generalize 2 ^ n = A at *
  generalize 2 ^ m = B at *
  cases A with
  | zero => omega
  | succ a =>
    cases B with
    | zero => omega
    | succ b => simp [Nat.succ_mul, Nat.mul_succ]

/-- The target of chain step `k`: `a ^ (2 ^ k - 1)`. -/
private noncomputable def chainTarget (q : BF64Quot) (k : ℕ) :
    BF64Quot := q ^ (2 ^ k - 1)

/-- The Itoh-Tsujii step: combining the `n`- and `m`-targets gives the `n + m`-target. -/
private theorem chainTarget_step {q x y : BF64Quot} {n m : ℕ}
    (hx : x = chainTarget q n) (hy : y = chainTarget q m) :
    x ^ (2 ^ m) * y = chainTarget q (n + m) := by
  rw [hx, hy, chainTarget, chainTarget, chainTarget, ← pow_mul, ← pow_add, chain_exponent]

/-- The Itoh-Tsujii chain computes `a ^ (2 ^ 64 - 2)`. -/
theorem toQuot_invItohTsujii (a : BF64) (h : a ≠ 0) :
    toQuot (invItohTsujii a) = toQuot a ^ (2 ^ 64 - 2) := by
  rw [invItohTsujii, if_neg h]
  set q := toQuot a with hq
  have e1 : toQuot a = chainTarget q 1 := by
    simp only [chainTarget, hq]; norm_num
  have e2 : toQuot (powTwoPow a 1 * a) = chainTarget q 2 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e1 e1
  have e3 : toQuot (powTwoPow (powTwoPow a 1 * a) 1 * a) = chainTarget q 3 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e2 e1
  set u3 := powTwoPow (powTwoPow a 1 * a) 1 * a with hu3
  have e6 : toQuot (powTwoPow u3 3 * u3) = chainTarget q 6 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e3 e3
  set u6 := powTwoPow u3 3 * u3 with hu6
  have e7 : toQuot (powTwoPow u6 1 * a) = chainTarget q 7 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e6 e1
  set u7 := powTwoPow u6 1 * a with hu7
  have e14 : toQuot (powTwoPow u7 7 * u7) = chainTarget q 14 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e7 e7
  set u14 := powTwoPow u7 7 * u7 with hu14
  have e15 : toQuot (powTwoPow u14 1 * a) = chainTarget q 15 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e14 e1
  set u15 := powTwoPow u14 1 * a with hu15
  have e30 : toQuot (powTwoPow u15 15 * u15) = chainTarget q 30 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e15 e15
  set u30 := powTwoPow u15 15 * u15 with hu30
  have e31 : toQuot (powTwoPow u30 1 * a) = chainTarget q 31 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e30 e1
  set u31 := powTwoPow u30 1 * a with hu31
  have e62 : toQuot (powTwoPow u31 31 * u31) = chainTarget q 62 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e31 e31
  set u62 := powTwoPow u31 31 * u31 with hu62
  have e63 : toQuot (powTwoPow u62 1 * a) = chainTarget q 63 := by
    rw [toQuot_mul, toQuot_powTwoPow]
    exact chainTarget_step e62 e1
  set u63 := powTwoPow u62 1 * a with hu63
  rw [toQuot_mul, e63, chainTarget, ← pow_add]
  congr 1

/-! ### The field structure

`BF64Quot` is a field because `basePoly` is irreducible, and `toQuot` is an
injective ring homomorphism onto it, so the carrier is a field too. Following
`CompPoly.Extension.Ext.instField`, the structure is assembled field-by-field so that every
operation stays computable.
-/

theorem toQuot_eq_zero_iff {a : BF64} : toQuot a = 0 ↔ a = 0 := by
  rw [← toQuot_zero]
  exact ⟨fun h => toQuot_injective h, fun h => h ▸ rfl⟩

theorem exists_pair_ne : ∃ x y : BF64, x ≠ y :=
  ⟨0, 1, by decide +kernel⟩

/-- The carrier is in bijection with `Fin (2 ^ 64)`, by its underlying representation. -/
def equivFin : BF64 ≃ Fin (2 ^ 64) where
  toFun a := a.toFin
  invFun i := BitVec.ofFin i
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype BF64 := Fintype.ofEquiv _ equivFin.symm

theorem card_bf64 : Fintype.card BF64 = 2 ^ 64 := by
  rw [Fintype.card_congr equivFin, Fintype.card_fin]

/-- The bridge is surjective: it is injective between finite types of equal cardinality. -/
theorem toQuot_surjective : Function.Surjective toQuot := by
  have hcard : Fintype.card BF64 = Fintype.card (BF64Quot) := by
    rw [card_bf64, card_bf64Quot]
  exact ((Fintype.bijective_iff_injective_and_card toQuot).mpr ⟨toQuot_injective, hcard⟩).2

/-- The Itoh-Tsujii inverse really is a multiplicative inverse. -/
theorem mul_invItohTsujii {a : BF64} (h : a ≠ 0) : a * invItohTsujii a = 1 := by
  have hq : toQuot a ≠ 0 := fun hz => h (toQuot_eq_zero_iff.mp hz)
  refine toQuot_injective ?_
  rw [toQuot_mul, toQuot_invItohTsujii a h, toQuot_one, ← pow_succ']
  have hcard : toQuot a ^ (2 ^ 64 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (toQuot a) hq
    rwa [card_bf64Quot] at this
  rw [show 2 ^ 64 - 2 + 1 = 2 ^ 64 - 1 from by norm_num]
  exact hcard

/-- Every nonzero carrier value has a multiplicative inverse. -/
theorem exists_mul_inv {a : BF64} (h : a ≠ 0) : ∃ b : BF64, a * b = 1 :=
  ⟨invItohTsujii a, mul_invItohTsujii h⟩

/-- Inversion is the Itoh-Tsujii chain, so it evaluates. -/
instance : Inv BF64 := ⟨invItohTsujii⟩

instance : Div BF64 := ⟨fun a b => a * invItohTsujii b⟩

theorem inv_def (a : BF64) : a⁻¹ = invItohTsujii a := rfl

theorem div_def (a b : BF64) : a / b = a * invItohTsujii b := rfl

@[simp] theorem inv_zero_bf64 : (0 : BF64)⁻¹ = 0 := by
  rw [inv_def, invItohTsujii, if_pos rfl]

theorem isField_bf64 : IsField BF64 where
  exists_pair_ne := exists_pair_ne
  mul_comm := mul_comm
  mul_inv_cancel := fun h => exists_mul_inv h

/-- The carrier is a field, `GF(2^64)`.

Assembled field-by-field around the explicit Itoh-Tsujii inverse, so inversion and division
evaluate rather than being extracted from an existence proof. -/
instance : Field BF64 where
  inv := invItohTsujii
  div a b := a * invItohTsujii b
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := exists_pair_ne
  mul_inv_cancel _ h := mul_invItohTsujii h
  inv_zero := inv_zero_bf64
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- The base field has characteristic two, inherited through the bridge. -/
instance : CharP BF64 2 where
  cast_eq_zero_iff n := by
    rw [← toQuot_eq_zero_iff, toQuot_natCast]
    exact (CharP.cast_eq_zero_iff (BF64Quot) 2 n)

end BF64
