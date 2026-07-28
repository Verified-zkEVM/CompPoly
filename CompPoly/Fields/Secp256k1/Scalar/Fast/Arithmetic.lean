/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Varun Thakore
-/

import CompPoly.Fields.Secp256k1.Scalar.Fast.Reduction

/-!
  # Arithmetic API for fast secp256k1 scalar field elements
-/

namespace Secp256k1.Scalar.Fast

/-- The fast secp256k1 scalar carrier, represented by canonical 4×UInt64 limbs. -/
abbrev Field : Type := { x : Repr // x.toNat < Secp256k1.Scalar.Basic.CARD }

/-- Fast scalar equality is decidable by comparing its four limbs. -/
instance : DecidableEq Field := inferInstance

/-- Raw canonical limbs backing a fast scalar element. -/
@[inline] def raw (x : Field) : Repr := x.val

/-- Zero. -/
@[inline] def zero : Field := ⟨Repr.zero, Repr.zero_lt⟩

/-- One. -/
@[inline] def one : Field := ⟨Repr.one, Repr.one_lt⟩

/-- Construct from a natural number by reducing modulo the scalar order. -/
@[inline] def ofNat (n : Nat) : Field :=
  ⟨Repr.ofNat n, Repr.ofNat_lt n⟩

/-- Convert from canonical `ZMod` scalar field to fast representation. -/
@[inline] def ofField (x : Secp256k1.Scalar.Basic.Field) : Field :=
  ofNat x.val

/-- Convert an integer into fast scalar representation. -/
@[inline] def ofInt (z : Int) : Field :=
  ofField (z : Secp256k1.Scalar.Basic.Field)

/-- Convert a fast scalar to its canonical natural representative. -/
@[inline] def toNat (x : Field) : Nat :=
  x.val.toNat

/-- Convert a fast scalar to the canonical `ZMod` scalar field. -/
@[inline] def toField (x : Field) : Secp256k1.Scalar.Basic.Field :=
  (toNat x : Secp256k1.Scalar.Basic.Field)

/-- Build a fast scalar from four limbs and a proof that they are canonical. -/
@[inline] private def ofCanonicalLimbs (r : Limbs4)
    (h : (Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2).toNat <
      Secp256k1.Scalar.Basic.CARD) : Field :=
  ⟨Repr.ofLimbs r.1 r.2.1 r.2.2.1 r.2.2.2, h⟩

/-- Fast scalar addition. -/
@[inline] def add (x y : Field) : Field :=
  ofCanonicalLimbs
    (Reduction.addModRaw
      x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3)
    (Reduction.addModRaw_lt
      x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3
      x.property y.property)

/-- Fast scalar negation. -/
@[inline] def neg (x : Field) : Field :=
  ofCanonicalLimbs
    (Reduction.negRaw x.val.d0 x.val.d1 x.val.d2 x.val.d3)
    (Reduction.negRaw_lt x.val.d0 x.val.d1 x.val.d2 x.val.d3 x.property)

/-- Fast scalar subtraction. -/
@[inline] def sub (x y : Field) : Field :=
  ofCanonicalLimbs
    (Reduction.subModRaw
      x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3)
    (Reduction.subModRaw_lt
      x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3
      x.property y.property)

/-- Fast scalar multiplication. -/
@[inline] def mul (x y : Field) : Field :=
  ofCanonicalLimbs
    (Reduction.mulRaw
      x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3)
    (Reduction.mulRaw_lt
      x.val.d0 x.val.d1 x.val.d2 x.val.d3 y.val.d0 y.val.d1 y.val.d2 y.val.d3)

/-- Fast scalar squaring. -/
@[inline] def square (x : Field) : Field :=
  ofCanonicalLimbs
    (Reduction.squareRaw x.val.d0 x.val.d1 x.val.d2 x.val.d3)
    (Reduction.squareRaw_lt x.val.d0 x.val.d1 x.val.d2 x.val.d3)

/-- Exponentiation over the fast representation using binary exponentiation. -/
@[inline] def pow (x : Field) (n : Nat) : Field :=
  @npowBinRec Field ⟨one⟩ ⟨mul⟩ n x

/-- Scalar inversion by Fermat exponentiation over the UInt64 limb kernel. -/
@[noinline] def invFermat (x : Field) : Field :=
  pow x (Secp256k1.Scalar.Basic.CARD - 2)

/-- Default scalar inversion uses Fermat exponentiation. -/
@[inline] def inv (x : Field) : Field :=
  invFermat x

/-- Fast scalar division through inversion and multiplication. -/
@[inline] def div (x y : Field) : Field :=
  mul x (inv y)

/-- Fast scalar zero. -/
instance instZeroField : Zero Field := ⟨zero⟩

/-- Fast scalar one. -/
instance instOneField : One Field := ⟨one⟩

/-- Fast scalar addition. -/
instance instAddField : Add Field := ⟨add⟩

/-- Fast scalar negation. -/
instance instNegField : Neg Field := ⟨neg⟩

/-- Fast scalar subtraction. -/
instance instSubField : Sub Field := ⟨sub⟩

/-- Fast scalar multiplication. -/
instance instMulField : Mul Field := ⟨mul⟩

/-- Fast scalar inversion. -/
instance instInvField : Inv Field := ⟨inv⟩

/-- Fast scalar division. -/
instance instDivField : Div Field := ⟨div⟩

/-- Natural-number casts into the fast scalar field. -/
instance instNatCastField : NatCast Field := ⟨ofNat⟩

/-- Integer casts into the fast scalar field. -/
instance instIntCastField : IntCast Field := ⟨ofInt⟩

/-- Natural scalar multiplication is multiplication by the corresponding fast natural cast. -/
instance instNatSMulField : SMul Nat Field where
  smul n x := (n : Field) * x

/-- Integer scalar multiplication is multiplication by the corresponding fast integer cast. -/
instance instIntSMulField : SMul Int Field where
  smul n x := (n : Field) * x

/-- Natural powers use fast binary exponentiation. -/
instance instPowFieldNat : Pow Field Nat := ⟨pow⟩

/-- Integer powers use fast natural powers and inversion. -/
instance instPowFieldInt : Pow Field Int where
  pow x n :=
    match n with
    | Int.ofNat k => pow x k
    | Int.negSucc k => pow (inv x) (k + 1)

/-- Interpret nonnegative rational casts through the canonical scalar field. -/
instance instNNRatCastField : NNRatCast Field where
  nnratCast q := ofField (q : Secp256k1.Scalar.Basic.Field)

/-- Interpret rational casts through the canonical scalar field. -/
instance instRatCastField : RatCast Field where
  ratCast q := ofField (q : Secp256k1.Scalar.Basic.Field)

/-- Transport nonnegative rational scalar multiplication through the canonical scalar field. -/
instance instNNRatSMulField : SMul ℚ≥0 Field where
  smul q x := ofField (q • toField x)

/-- Transport rational scalar multiplication through the canonical scalar field. -/
instance instRatSMulField : SMul ℚ Field where
  smul q x := ofField (q • toField x)

end Secp256k1.Scalar.Fast
