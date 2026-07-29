/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.Extension
import CompPoly.Fields.KoalaBear.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# The degree-4 extension of KoalaBear

`KoalaBear[X] / (X^4 - 3)`, the challenge field used alongside the KoalaBear base field in
Plonky3-style STARKs.

Irreducibility of `X^4 - 3` is discharged by `Polynomial.irreducible_X_pow_four_sub_C_of_card`,
whose two hypotheses are single exponentiations in the base field:
`3^((p^4-1)/4) = 1` and `3^((p^2-1)/4) ≠ 1`. Both are closed by `reduce_mod_char`, which does
modular repeated squaring at elaboration time — no `native_decide`, and no generated
certificate file.

## Main definitions

* `KoalaBear.ext4Params`: the `BinomialParams` for `X^4 - 3`.
* `KoalaBear.Ext4`: the extension field itself.
-/

namespace KoalaBear

open CompPoly.Extension Polynomial

/-- The parameters of the quartic extension `KoalaBear[X] / (X^4 - 3)`. -/
def ext4Params : BinomialParams Field where
  d := 4
  W := 3
  two_le := by norm_num
  q := fieldSize
  card_eq := ZMod.card _

@[simp] theorem ext4Params_d : ext4Params.d = 4 := rfl
@[simp] theorem ext4Params_W : ext4Params.W = 3 := rfl
@[simp] theorem ext4Params_q : ext4Params.q = fieldSize := rfl

/-- `X^4 - 3` is irreducible over KoalaBear, by the collapsed Rabin criterion. -/
theorem ext4Params_poly_irreducible : Irreducible ext4Params.poly := by
  rw [BinomialParams.poly]
  refine irreducible_X_pow_four_sub_C_of_card (q := 2130706433) (ZMod.card _) (by decide)
    (by norm_num) (by norm_num) ?_ ?_
  · show (3 : ZMod 2130706433) ^ ((2130706433 ^ 4 - 1) / 4) = 1
    reduce_mod_char
  · show (3 : ZMod 2130706433) ^ ((2130706433 ^ 2 - 1) / 4) ≠ 1
    reduce_mod_char
    decide

instance : Fact (Irreducible ext4Params.poly) := ⟨ext4Params_poly_irreducible⟩

/-- The degree-4 extension field of KoalaBear. -/
abbrev Ext4 : Type := CompPoly.Extension.Ext ext4Params

/-- The adjoined fourth root of `3`, as an element of `Ext4`. -/
def ext4Gen : Ext4 := Ext.ofFn fun i => if (i : ℕ) = 1 then 1 else 0

@[simp] theorem card_ext4 : Fintype.card Ext4 = fieldSize ^ 4 := Ext.card_ext

end KoalaBear
