/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Arithmetic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finiteness and cardinality of monic quotient presentations

The coordinate equivalence gives `Finite (Ext P)` from `Finite F`, and gives an optional
`Fintype (Ext P)` when an enumeration of the base is available. A separate certificate
`Fact (Nat.card F = P.q)` identifies the stored exponent parameter with the base cardinality.
The resulting extension cardinality is `P.q ^ P.d`.

These facts require neither a polynomial quotient bridge nor irreducibility. All finiteness
and cardinality assumptions used by field laws are propositions, so executable arithmetic
never receives an enumeration dictionary merely to use those laws.
-/

@[expose] public section

namespace CompPoly.Extension

/-- The certified cardinality agrees with any enumeration of the base type. -/
theorem ExtensionParams.card_eq {F : Type*} [Fintype F] (P : ExtensionParams F)
    [Fact (Nat.card F = P.q)] : Fintype.card F = P.q := by
  rw [← Nat.card_eq_fintype_card]
  exact Fact.out

/-- The certified binomial base cardinality agrees with any enumeration. -/
theorem BinomialParams.card_eq {F : Type*} [Fintype F] (P : BinomialParams F)
    [Fact (Nat.card F = P.q)] : Fintype.card F = P.q := by
  rw [← Nat.card_eq_fintype_card]
  exact Fact.out

instance {F : Type*} [Ring F] (P : BinomialParams F) [Fact (Nat.card F = P.q)] :
    Fact (Nat.card F = P.toExtensionParams.q) := ⟨(show Nat.card F = P.q from Fact.out)⟩

end CompPoly.Extension

namespace CompPoly.Extension.Ext

variable {F : Type*} {P : ExtensionParams F}

instance instFinite [Finite F] : Finite (Ext P) :=
  Finite.of_equiv (Fin P.d → F) (equivFn P).symm

instance instFintype [Fintype F] : Fintype (Ext P) := Fintype.ofEquiv _ (equivFn P).symm

/-- The enumerated extension cardinality is the certified base cardinality to the degree. -/
theorem card_ext [Fintype F] [Fact (Nat.card F = P.q)] : Fintype.card (Ext P) = P.q ^ P.d := by
  rw [Fintype.card_congr (equivFn P), Fintype.card_fun, P.card_eq, Fintype.card_fin]

/-- The extension has `q^d` elements, independently of any chosen enumeration. -/
theorem nat_card_ext [Finite F] [Fact (Nat.card F = P.q)] :
    Nat.card (Ext P) = P.q ^ P.d := by
  let := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, card_ext]

end CompPoly.Extension.Ext
