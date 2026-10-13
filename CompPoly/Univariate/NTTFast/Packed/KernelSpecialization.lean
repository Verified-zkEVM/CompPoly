/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.KernelModels
public import CompPoly.Univariate.NTTFast.Packed.Expressions

/-! # Specialization of abstract kernel expression graphs -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- The concrete read has the abstract read's scalar semantics. -/
theorem readField_eq_expression (a : Array KoalaBear.Fast.Field) (i o : USize) :
    readField a i o = Expressions.readField a i o := by rfl
/-- The concrete add specializes abstract addition. -/
theorem fieldAdd_eq_expression (x y : KoalaBear.Fast.Field) :
    fieldAdd x y = Expressions.fieldAdd x y := by rfl
/-- The concrete subtract specializes abstract subtraction. -/
theorem fieldSub_eq_expression (x y : KoalaBear.Fast.Field) :
    fieldSub x y = Expressions.fieldSub x y := by rfl
/-- The concrete multiply specializes abstract multiplication. -/
theorem fieldMul_eq_expression (x y : KoalaBear.Fast.Field) :
    fieldMul x y = Expressions.fieldMul x y := by rfl

/-- The concrete field model specializes the abstract expression graph. -/
theorem step16Field_eq_expression (th tl : Array KoalaBear.Fast.Field) (j j1 i0 i1 i2 i3 : USize)
    (b : Array KoalaBear.Fast.Field)  :
    step16Field th tl j j1 i0 i1 i2 i3 b = Expressions.step16Field th tl j j1 i0 i1 i2 i3 b := by
  unfold Expressions.step16Field
  simp only [← readField_eq_expression, ← fieldAdd_eq_expression, ← fieldSub_eq_expression, ←
    fieldMul_eq_expression]
  rfl

/-- The concrete field model specializes the abstract expression graph. -/
theorem leaf16Field_eq_expression (t3 t2 t1 : Array KoalaBear.Fast.Field) (i : USize) (b : Array
    KoalaBear.Fast.Field)  :
    leaf16Field t3 t2 t1 i b = Expressions.leaf16Field t3 t2 t1 i b := by
  unfold Expressions.leaf16Field
  simp only [← readField_eq_expression, ← fieldAdd_eq_expression, ← fieldSub_eq_expression, ←
    fieldMul_eq_expression]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
