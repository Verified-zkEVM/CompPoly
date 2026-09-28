/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.Extension.Arithmetic
public import CompPoly.Fields.Extension.Arithmetic

/-!
# Raw extension arithmetic without field certificates

An integer quotient and a coefficient carrier over Bool exercise the raw import boundary.
The inverse candidate with `q = 0` deliberately lacks inverse laws.
-/

public meta section

namespace CompPolyTests.ExtensionRawArithmetic

open CompPoly.Extension

private abbrev params : ExtensionParams Int := ⟨2, by decide, #v[1, 0], 0⟩

#guard Ext.coeffs ((Ext.gen : Ext params) * Ext.gen) == #v[-1, 0]
#guard Ext.coeffs ((Ext.gen : Ext params) ^ 2) == #v[-1, 0]
#guard Ext.coeffs ((0 : Ext params)⁻¹) == #v[1, 0]

example : (inferInstance : Mul (Ext params)).mul = Ext.mul := rfl
example : (inferInstance : Inv (Ext params)).inv = Ext.inv := rfl

private abbrev bare : ExtensionParams Bool := ⟨2, by decide, #v[true, false], 0⟩

example (v : Vector Bool 2) : Ext.coeffs (Ext.ofVector (P := bare) v) = v := rfl

private abbrev binomial : BinomialParams Int := ⟨2, -1, by decide, 0⟩

#guard Ext.coeffs ((Ext.gen : Ext binomial.toExtensionParams) ^ 2) == #v[-1, 0]

end CompPolyTests.ExtensionRawArithmetic
