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

Cross-checks of `Polynomial.irreducible_X_pow_four_sub_C_iff` and its general-degree
counterpart `Polynomial.irreducible_X_pow_sub_C` on `ZMod 5`, small enough that the
answers can be confirmed independently by `decide`. Both take the field size as a numeral with
`hcard : Fintype.card F = q`, here `card_zmod5`.

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
  irreducible_X_pow_four_sub_C card_zmod5 (by decide) (by norm_num) (by norm_num)
    (by reduce_mod_char) (by reduce_mod_char; decide)

/-- Independent necessary-condition check: an irreducible quartic has no root in the base
field. Confirms the criterion's verdict above is consistent with brute force. -/
example : ∀ a : ZMod 5, a ^ 4 - 2 ≠ 0 := by decide

/-- Conversely `X^4 - 1` is *reducible* over `ZMod 5`: the second Rabin condition fails,
because `1` is a fourth power. -/
theorem not_irreducible_X_pow_four_sub_one : ¬ Irreducible ((X : (ZMod 5)[X]) ^ 4 - C 1) := by
  rw [irreducible_X_pow_four_sub_C_iff card_zmod5 (by decide) (by norm_num) (by norm_num)]
  rintro ⟨-, hmid⟩
  exact hmid (one_pow _)

/-- And indeed `X^4 - 1` visibly has roots in `ZMod 5`, independently of the criterion. -/
example : ((1 : ZMod 5) ^ 4 - 1 = 0) ∧ ((2 : ZMod 5) ^ 4 - 1 = 0) := by decide

/-! ### The general-degree form

`irreducible_X_pow_sub_C` is the same criterion at arbitrary `d`, for a future extension
of a degree other than `4`. At `d = 2` over `ZMod 5` it says `X^2 - 2` is irreducible, which is
just "2 is not a square mod 5" — checkable by `decide` alongside it.
-/

/-- `X^2 - 2` is irreducible over `ZMod 5`, via the general-degree criterion. -/
theorem irreducible_X_sq_sub_two : Irreducible ((X : (ZMod 5)[X]) ^ 2 - C 2) := by
  refine irreducible_X_pow_sub_C card_zmod5 (by norm_num) (by decide)
    (by norm_num) ?_ (by reduce_mod_char) ?_
  · intro ℓ hℓ
    rw [Nat.Prime.primeFactors Nat.prime_two, Finset.mem_singleton] at hℓ
    subst hℓ
    norm_num
  · intro ℓ hℓ
    rw [Nat.Prime.primeFactors Nat.prime_two, Finset.mem_singleton] at hℓ
    subst hℓ
    reduce_mod_char
    decide

/-- Independent check: `2` is a non-square mod `5`, so the quadratic above has no root. -/
example : ∀ a : ZMod 5, a ^ 2 - 2 ≠ 0 := by decide

/-- At `hcard := rfl`, the general-degree criterion reads at `Fintype.card F`. -/
theorem card_rfl_instance {F : Type*} [Field F] [Fintype F] {d : ℕ} {W : F}
    (hd : 0 < d) (hW0 : W ≠ 0)
    (h_top : d ∣ Fintype.card F ^ d - 1)
    (h_mid : ∀ ℓ ∈ d.primeFactors, d ∣ Fintype.card F ^ (d / ℓ) - 1) :
    Irreducible ((X : F[X]) ^ d - C W) ↔
      (W ^ ((Fintype.card F ^ d - 1) / d) = 1 ∧
        ∀ ℓ ∈ d.primeFactors, W ^ ((Fintype.card F ^ (d / ℓ) - 1) / d) ≠ 1) :=
  irreducible_X_pow_sub_C_iff rfl hd hW0 h_top h_mid

end CompPolyTests.Fields.Extension.Binomial
