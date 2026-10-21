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
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

/-- Read one coordinate in the field-level kernel model. -/
def readField (a : Array (FastField p)) (i o : USize) : FastField p :=
  a.getD (i.toNat + o.toNat) 0
/-- Addition in the field-level kernel model. -/
def fieldAdd (x y : FastField p) : FastField p := x + y
/-- Subtraction in the field-level kernel model. -/
def fieldSub (x y : FastField p) : FastField p := x - y
/-- Multiplication in the field-level kernel model. -/
def fieldMul (x y : FastField p) : FastField p := x * y

/-- Sixteen independent radix-four butterflies, with four batched array stores. -/
def step16Field (th tl : Array (FastField p)) (j j1 i0 i1 i2 i3 : USize)
    (b : Array (FastField p)) : Array (FastField p) :=
  step16_fields%

/-- Field-array expression graph of the fused final four DIF layers. -/
def leaf16Field (t3 t2 t1 : Array (FastField p)) (i : USize) (b : Array
    (FastField p)) : Array (FastField p) :=
  leaf16_fields%

end CompPoly.CPolynomial.NTTFast.Packed
