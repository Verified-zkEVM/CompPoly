/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.FieldStorage
import CompPoly.Univariate.NTTFast.Packed.Unrolled

/-! # Field-level models of the packed scalar kernels -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- Read one coordinate in the field-level kernel model. -/
def readField (a : Array KoalaBear.Fast.Field) (i o : USize) : KoalaBear.Fast.Field :=
  a.getD (i.toNat + o.toNat) 0
/-- Addition in the field-level kernel model. -/
def fieldAdd (x y : KoalaBear.Fast.Field) : KoalaBear.Fast.Field := x + y
/-- Subtraction in the field-level kernel model. -/
def fieldSub (x y : KoalaBear.Fast.Field) : KoalaBear.Fast.Field := x - y
/-- Multiplication in the field-level kernel model. -/
def fieldMul (x y : KoalaBear.Fast.Field) : KoalaBear.Fast.Field := x * y

/-- Sixteen independent radix-four butterflies, with four batched array stores. -/
def step16Field (th tl : Array KoalaBear.Fast.Field) (j j1 i0 i1 i2 i3 : USize)
    (b : Array KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  step16_fields%

/-- Field-array expression graph of the fused final four DIF layers. -/
def leaf16Field (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize) (b : Array
    KoalaBear.Fast.Field) : Array KoalaBear.Fast.Field :=
  leaf16_fields%

end CompPoly.CPolynomial.NTTFast.Packed
