/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Goldilocks.Fast.Reduction

/-!
# Fast Goldilocks Arithmetic

This module defines the fast native-word Goldilocks carrier, conversions,
arithmetic operations, and notation instances.

Fast field values are stored as canonical `UInt64` representatives below the
Goldilocks prime `p = 2^64 - 2^32 + 1`. Multiplication uses a 128-bit
intermediate represented as a pair of `UInt64` words `(lo, hi)` and reduces it
with the Goldilocks identity

`2^64 ≡ 2^32 - 1 (mod p)`.
-/

namespace Goldilocks
namespace Fast

/-- The fast native-word Goldilocks field carrier, stored as a canonical residue. -/
abbrev Field : Type := { x : UInt64 // x.toNat < Goldilocks.Basic.fieldSize }

/-- Fast representatives have decidable equality through their `UInt64` value. -/
instance : DecidableEq Field := inferInstance

/-- The raw canonical word backing a fast Goldilocks element. -/
@[inline]
def raw (x : Field) : UInt64 := x.val

/-- Reduce a native `UInt64` modulo Goldilocks. -/
@[inline]
def reduceUInt64 (x : UInt64) : Field :=
  ⟨Reduction.reduceUInt64Raw x, Reduction.reduceUInt64Raw_lt x⟩

/-- One-word reduction preserves the represented canonical field element. -/
@[simp]
theorem reduceUInt64_cast (x : UInt64) :
    ((reduceUInt64 x).val.toNat : Goldilocks.Basic.Field) =
      (x.toNat : Goldilocks.Basic.Field) := by
  exact Reduction.reduceUInt64Raw_cast x

/-- The zero fast Goldilocks element. -/
@[inline]
def zero : Field := ⟨0, by decide⟩

/-- The one fast Goldilocks element. -/
@[inline]
def one : Field := ⟨1, by decide⟩

/-- Build a fast element from a canonical natural representative. -/
@[inline]
def ofCanonicalNat (n : Nat) (h : n < Goldilocks.Basic.fieldSize) : Field :=
  ⟨UInt64.ofNat n, by
    have hn : n < UInt64.size := Nat.lt_trans h fieldSize_lt_uint64Size
    rw [UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt]
    · exact h
    · simpa [UInt64.size] using hn⟩

/-- Convert a natural number into fast canonical representation. -/
@[inline]
def ofNat (n : Nat) : Field :=
  ofCanonicalNat (n % Goldilocks.Basic.fieldSize) (Nat.mod_lt _ fieldSize_pos)

/-- Convert a 64-bit word into fast canonical representation. -/
@[inline]
def ofUInt64 (x : UInt64) : Field :=
  reduceUInt64 x

/-- Convert from the canonical `ZMod` Goldilocks field into fast canonical form. -/
@[inline]
def ofField (x : Goldilocks.Basic.Field) : Field :=
  ofCanonicalNat x.val (ZMod.val_lt x)

/-- Convert an integer into fast canonical representation. -/
@[inline]
def ofInt (z : Int) : Field :=
  ofField (z : Goldilocks.Basic.Field)

/-- Convert a fast Goldilocks element to its canonical natural representative. -/
@[inline]
def toNat (x : Field) : Nat :=
  x.val.toNat

/-- Convert a fast Goldilocks element to the canonical `ZMod` Goldilocks field. -/
@[inline]
def toField (x : Field) : Goldilocks.Basic.Field :=
  (toNat x : Goldilocks.Basic.Field)

/-- Fast modular addition in canonical form. -/
@[inline]
def add (x y : Field) : Field :=
  let lo := x.val + y.val
  let carry := decide (lo < x.val)
  ⟨Reduction.reduceAddWithCarryRaw lo carry,
    Reduction.reduceAddWithCarryRaw_lt lo carry
      (Reduction.addWithCarry_bound x.val y.val x.property y.property)⟩

/-- Fast modular negation in canonical form. -/
@[inline]
def neg (x : Field) : Field :=
  ⟨Reduction.negRaw x.val, Reduction.negRaw_lt x.val x.property⟩

/-- Fast modular subtraction in canonical form. -/
@[inline]
def sub (x y : Field) : Field :=
  ⟨Reduction.subRaw x.val y.val, Reduction.subRaw_lt x.val y.val x.property y.property⟩

/-- Fast modular multiplication in canonical form. -/
@[inline]
def mul (x y : Field) : Field :=
  ⟨Reduction.reduceMulRaw x.val y.val, Reduction.reduceMulRaw_lt x.val y.val⟩

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
def invExponent : Nat := Goldilocks.Basic.fieldSize - 2

/-- Fast modular inversion using an addition chain for `p - 2`.

For Goldilocks, `p - 2 = 0xFFFFFFFEFFFFFFFF`. The chain builds
`x^(2^31 - 1)`, derives `x^(2^32 - 2)` and `x^(2^32 - 1)`, then combines them as

`(2^32 - 2) * 2^32 + (2^32 - 1) = p - 2`.
-/
@[noinline]
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
  nnratCast q := ofField (q : Goldilocks.Basic.Field)

/-- Interpret rational casts through the canonical Goldilocks field. -/
instance instRatCastField : RatCast Field where
  ratCast q := ofField (q : Goldilocks.Basic.Field)

/-- Nonnegative rational scalar multiplication is transported through the canonical field. -/
instance instNNRatSMulField : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

/-- Rational scalar multiplication is transported through the canonical field. -/
instance instRatSMulField : SMul ℚ Field where
  smul q x := ofField (q • toField x)

end Fast
end Goldilocks
