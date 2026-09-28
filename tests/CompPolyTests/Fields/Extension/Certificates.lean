/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public meta import CompPoly.Fields.KoalaBear.Ext4
public meta import Mathlib.Algebra.Polynomial.SpecificDegree
public import CompPoly.Fields.KoalaBear.Ext4
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Cardinality certificates for extension field laws

An incorrect finite cardinality and the true cardinality zero of an infinite field each
fail field admission despite irreducibility. Valid finite certificates support iterated
extensions without supplying enumeration dictionaries.
-/

public meta section

namespace CompPolyTests.ExtensionCertificates

open CompPoly.Extension Polynomial

private abbrev wrongCardinality : ExtensionParams KoalaBear.Field :=
  { KoalaBear.ext4Params.toExtensionParams with q := 0 }

private instance : Fact (Irreducible wrongCardinality.poly) := ⟨by
  change Irreducible KoalaBear.ext4Params.toExtensionParams.poly
  exact Fact.out⟩

example : Nat.card KoalaBear.Field ≠ wrongCardinality.q := by
  rw [Nat.card_eq_fintype_card, ZMod.card]
  decide

example : True := by
  fail_if_success
    let _ : Fact (Nat.card KoalaBear.Field = wrongCardinality.q) := inferInstance
  fail_if_success
    let _ : Field (Ext wrongCardinality) := inferInstance
  trivial

#guard Ext.inv (0 : Ext wrongCardinality) == 1

private abbrev infiniteBase : ExtensionParams Rat := ⟨2, by decide, #v[1, 0], 0⟩

private theorem infiniteBase_poly : infiniteBase.poly = X ^ 2 + 1 := by
  simp [ExtensionParams.poly, infiniteBase, ExtensionParams.lowerCoeff, Fin.sum_univ_two]

private instance : Fact (Nat.card Rat = infiniteBase.q) := ⟨Nat.card_eq_zero_of_infinite⟩

private instance : Fact (Irreducible infiniteBase.poly) := ⟨by
  rw [infiniteBase_poly]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X ^ 2 + 1 : Rat[X]).natDegree = 2 := by compute_degree!
    rw [hd]
    decide
  · intro a ha
    simp only [Polynomial.IsRoot, eval_add, eval_pow, eval_X, eval_one] at ha
    nlinarith [sq_nonneg a]⟩

example : True := by
  fail_if_success
    let _ : Finite Rat := inferInstance
  fail_if_success
    let _ : Field (Ext infiniteBase) := inferInstance
  trivial

#guard Ext.inv (0 : Ext infiniteBase) == 1

section Iterated

variable {F : Type*} [Field F] [Finite F] {P : ExtensionParams F}
  [Fact (Nat.card F = P.q)] [Fact (Irreducible P.poly)]

example : Finite (Ext P) := inferInstance
example : Nat.card (Ext P) = P.q ^ P.d := Ext.nat_card_ext

variable {Q : ExtensionParams (Ext P)} [Fact (Nat.card (Ext P) = Q.q)]
  [Fact (Irreducible Q.poly)]

example : Field (Ext Q) := inferInstance
example : Finite (Ext Q) := inferInstance
example (x : Ext Q) : (inferInstance : Field (Ext Q)).inv x = Ext.inv x := rfl

end Iterated

end CompPolyTests.ExtensionCertificates
