/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Binomial
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.ReduceModChar

/-!
# Binomial irreducibility criterion tests

Cross-checks of `Polynomial.irreducible_X_pow_four_sub_C_iff_of_card` on `ZMod 5`, small enough
that the answers can be confirmed independently by `decide`.

Both directions are exercised: `X^4 - 2` is irreducible (`2` is a non-square mod `5`), while
`X^4 - 1` is not. The second case is what makes the `iff` worth having — a failed check
*proves* reducibility rather than merely failing to prove irreducibility.
-/

@[expose] public section

namespace CompPolyTests.Fields.Extension.Binomial

open Polynomial

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem card_zmod5 : Fintype.card (ZMod 5) = 5 := ZMod.card _

/-- `X^4 - 2` is irreducible over `ZMod 5`. -/
theorem irreducible_X_pow_four_sub_two : Irreducible ((X : (ZMod 5)[X]) ^ 4 - C 2) :=
  irreducible_X_pow_four_sub_C_of_card card_zmod5 (by decide) (by norm_num) (by norm_num)
    (by reduce_mod_char) (by reduce_mod_char; decide)

/-- Independent necessary-condition check: an irreducible quartic has no root in the base
field. Confirms the criterion's verdict above is consistent with brute force. -/
example : ∀ a : ZMod 5, a ^ 4 - 2 ≠ 0 := by decide

/-- Conversely `X^4 - 1` is *reducible* over `ZMod 5`: the second Rabin condition fails,
because `1` is a fourth power. -/
theorem not_irreducible_X_pow_four_sub_one : ¬ Irreducible ((X : (ZMod 5)[X]) ^ 4 - C 1) := by
  rw [irreducible_X_pow_four_sub_C_iff_of_card card_zmod5 (by decide) (by norm_num) (by norm_num)]
  rintro ⟨-, hmid⟩
  exact hmid (one_pow _)

/-- And indeed `X^4 - 1` visibly has roots in `ZMod 5`, independently of the criterion. -/
example : ((1 : ZMod 5) ^ 4 - 1 = 0) ∧ ((2 : ZMod 5) ^ 4 - 1 = 0) := by decide

end CompPolyTests.Fields.Extension.Binomial
