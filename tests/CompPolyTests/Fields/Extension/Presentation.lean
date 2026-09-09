/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Extension.Field
public import CompPoly.Fields.Extension.Field

/-!
# Extension presentation regressions

The quotients by `X² + 1` and `X² + X + 1` over `GF(2)` have the same coefficient-vector
length but different multiplication. Their elements require an explicit coordinate conversion.
The first quotient is a ring; no irreducibility or field claim is made about that modulus.
-/

public meta section

namespace CompPolyTests.ExtensionPresentation

open CompPoly.Extension

/-- Parameters for the monic modulus `X² + 1` over `GF(2)`. -/
private def first : ExtensionParams (ZMod 2) where
  d := 2
  two_le := le_rfl
  lower := #v[1, 0]
  q := 2
  card_eq := ZMod.card 2

/-- Parameters for the monic modulus `X² + X + 1` over `GF(2)`. -/
private def second : ExtensionParams (ZMod 2) where
  d := 2
  two_le := le_rfl
  lower := #v[1, 1]
  q := 2
  card_eq := ZMod.card 2

example (_x : Ext first) : True := by
  fail_if_success
    let _y : Ext second := _x
  trivial

example (_x : Ext first) (_y : Ext second) : True := by
  fail_if_success
    let _z := Ext.mul (P := first) _x _y
  trivial

example (v : Vector (ZMod 2) first.d) : Ext.coeffs (Ext.ofVector (P := first) v) = v := by
  simp

example (x : Ext first) : Ext.ofVector (Ext.coeffs x) = x := by
  simp

-- Multiplication in each presentation uses its own modulus.
#guard Ext.coeff ((Ext.gen : Ext first) * Ext.gen) ⟨1, by decide⟩ == 0

#guard Ext.coeff ((Ext.gen : Ext second) * Ext.gen) ⟨1, by decide⟩ == 1

-- Boolean equality remains lawful on the wrapped carrier.
example : LawfulBEq (Ext first) := inferInstance

section Operations

variable {F : Type*} [Field F] [Fintype F] {P : ExtensionParams F}
  [Fact (Irreducible P.poly)]

-- Field projections retain the canonical executable operations.
example (x y : Ext P) : (inferInstance : Field (Ext P)).mul x y = Ext.mul x y := rfl
example (x : Ext P) : (inferInstance : Field (Ext P)).inv x = Ext.inv x := rfl
example (x y : Ext P) : (inferInstance : Field (Ext P)).div x y = x * Ext.inv y := rfl
example (x : Ext P) (n : ℕ) :
    (inferInstance : Field (Ext P)).npow n x = npowBinRec n x := rfl

end Operations

end CompPolyTests.ExtensionPresentation
