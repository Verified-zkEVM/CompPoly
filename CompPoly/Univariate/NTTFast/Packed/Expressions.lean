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
namespace CompPoly.CPolynomial.NTTFast.Packed.Expressions

/-- Read one coordinate in the field-level kernel model. -/
def readField [Zero R] (a : Array R) (i o : USize) : R :=
  a.getD (i.toNat + o.toNat) 0
/-- Addition in the field-level kernel model. -/
def fieldAdd [Add R] (x y : R) : R := x + y
/-- Subtraction in the field-level kernel model. -/
def fieldSub [Sub R] (x y : R) : R := x - y
/-- Multiplication in the field-level kernel model. -/
def fieldMul [Mul R] (x y : R) : R := x * y

/-- Sixteen independent radix-four butterflies, with four batched array stores. -/
def step16Field [Zero R] [Add R] [Sub R] [Mul R] (th tl : Array R) (j j1 i0 i1 i2 i3 : USize)
    (b : Array R) : Array R :=
  step16_fields%

/-- Field-array expression graph of the fused final four DIF layers. -/
def leaf16Field [Zero R] [Add R] [Sub R] [Mul R] (t3 t2 t1 : Array R) (i : USize) (b : Array R) :
    Array R :=
  leaf16_fields%

end CompPoly.CPolynomial.NTTFast.Packed.Expressions
