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
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

/-- The concrete read has the abstract read's scalar semantics. -/
theorem readField_eq_expression (a : Array (FastField p)) (i o : USize) :
    readField a i o = Expressions.readField a i o := by rfl
/-- The concrete add specializes abstract addition. -/
theorem fieldAdd_eq_expression (x y : FastField p) :
    fieldAdd x y = Expressions.fieldAdd x y := by rfl
/-- The concrete subtract specializes abstract subtraction. -/
theorem fieldSub_eq_expression (x y : FastField p) :
    fieldSub x y = Expressions.fieldSub x y := by rfl
/-- The concrete multiply specializes abstract multiplication. -/
theorem fieldMul_eq_expression (x y : FastField p) :
    fieldMul x y = Expressions.fieldMul x y := by rfl

/-- The concrete field model specializes the abstract expression graph. -/
theorem step16Field_eq_expression (th tl : Array (FastField p)) (j j1 i0 i1 i2 i3 : USize)
    (b : Array (FastField p))  :
    step16Field th tl j j1 i0 i1 i2 i3 b = Expressions.step16Field th tl j j1 i0 i1 i2 i3 b := by
  unfold Expressions.step16Field
  simp only [← readField_eq_expression, ← fieldAdd_eq_expression, ← fieldSub_eq_expression, ←
    fieldMul_eq_expression]
  rfl

/-- The concrete field model specializes the abstract expression graph. -/
theorem leaf16Field_eq_expression (t3 t2 t1 : Array (FastField p)) (i : USize) (b : Array
    (FastField p))  :
    leaf16Field t3 t2 t1 i b = Expressions.leaf16Field t3 t2 t1 i b := by
  unfold Expressions.leaf16Field
  simp only [← readField_eq_expression, ← fieldAdd_eq_expression, ← fieldSub_eq_expression, ←
    fieldMul_eq_expression]
  rfl

end CompPoly.CPolynomial.NTTFast.Packed
