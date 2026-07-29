/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.Extension
import CompPoly.Fields.BabyBear.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# The degree-4 extension of BabyBear

`BabyBear[X] / (X^4 - 11)`, the challenge field used alongside the BabyBear base field in
RISC Zero and Plonky3.

Irreducibility of `X^4 - 11` is discharged by
`Polynomial.irreducible_X_pow_four_sub_C_of_card`, whose two hypotheses are single
exponentiations in the base field: `11^((p^4-1)/4) = 1` and `11^((p^2-1)/4) ≠ 1`.

## Main definitions

* `BabyBear.ext4Params`: the `BinomialParams` for `X^4 - 11`.
* `BabyBear.Ext4`: the extension field itself.
-/

namespace BabyBear

open CompPoly.Extension Polynomial

/-- The parameters of the quartic extension `BabyBear[X] / (X^4 - 11)`. -/
def ext4Params : BinomialParams Field where
  d := 4
  W := 11
  two_le := by norm_num
  q := fieldSize
  card_eq := ZMod.card _

@[simp] theorem ext4Params_d : ext4Params.d = 4 := rfl
@[simp] theorem ext4Params_W : ext4Params.W = 11 := rfl
@[simp] theorem ext4Params_q : ext4Params.q = fieldSize := rfl

/-- `X^4 - 11` is irreducible over BabyBear, by the collapsed Rabin criterion. -/
theorem ext4Params_poly_irreducible : Irreducible ext4Params.poly := by
  rw [BinomialParams.poly]
  refine irreducible_X_pow_four_sub_C_of_card (q := 2013265921) (ZMod.card _) (by decide)
    (by norm_num) (by norm_num) ?_ ?_
  · show (11 : ZMod 2013265921) ^ ((2013265921 ^ 4 - 1) / 4) = 1
    reduce_mod_char
  · show (11 : ZMod 2013265921) ^ ((2013265921 ^ 2 - 1) / 4) ≠ 1
    reduce_mod_char
    decide

instance : Fact (Irreducible ext4Params.poly) := ⟨ext4Params_poly_irreducible⟩

/-- The degree-4 extension field of BabyBear. -/
abbrev Ext4 : Type := CompPoly.Extension.Ext ext4Params

/-- The adjoined fourth root of `11`, as an element of `Ext4`. -/
def ext4Gen : Ext4 := Ext.ofFn fun i => if (i : ℕ) = 1 then 1 else 0

@[simp] theorem card_ext4 : Fintype.card Ext4 = fieldSize ^ 4 := Ext.card_ext

end BabyBear
