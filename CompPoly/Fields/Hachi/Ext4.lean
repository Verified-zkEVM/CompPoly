/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import CompPoly.Fields.Extension
import CompPoly.Fields.Hachi
import Mathlib.Tactic.ReduceModChar

/-!
# The degree-4 extension of Hachi

`Hachi[X] / (X^4 - 2)`, the degree-4 extension of the 32-bit prime field `2^32 - 99`.

`W = 2` is the smallest non-square modulo `p`, which also makes multiplication by `W` a
doubling. Because `p ≡ 1 mod 4`, `X^4 - W` is irreducible for any non-square `W`; concretely
this is discharged by `Polynomial.irreducible_X_pow_four_sub_C_of_card` from
`2^((p^4-1)/4) = 1` and `2^((p^2-1)/4) ≠ 1`.

## Main definitions

* `Hachi.ext4Params`: the `BinomialParams` for `X^4 - 2`.
* `Hachi.Ext4`: the extension field itself.
-/

namespace Hachi

open CompPoly.Extension Polynomial

/-- The parameters of the quartic extension `Hachi[X] / (X^4 - 2)`. -/
def ext4Params : BinomialParams Field where
  d := 4
  W := 2
  two_le := by norm_num
  q := fieldSize
  card_eq := ZMod.card _

@[simp] theorem ext4Params_d : ext4Params.d = 4 := rfl
@[simp] theorem ext4Params_W : ext4Params.W = 2 := rfl
@[simp] theorem ext4Params_q : ext4Params.q = fieldSize := rfl

/-- `X^4 - 2` is irreducible over Hachi, by the collapsed Rabin criterion. -/
theorem ext4Params_poly_irreducible : Irreducible ext4Params.poly := by
  rw [BinomialParams.poly]
  refine irreducible_X_pow_four_sub_C_of_card (q := 4294967197) (ZMod.card _) (by decide)
    (by norm_num) (by norm_num) ?_ ?_
  · show (2 : ZMod 4294967197) ^ ((4294967197 ^ 4 - 1) / 4) = 1
    reduce_mod_char
  · show (2 : ZMod 4294967197) ^ ((4294967197 ^ 2 - 1) / 4) ≠ 1
    reduce_mod_char
    decide

instance : Fact (Irreducible ext4Params.poly) := ⟨ext4Params_poly_irreducible⟩

/-- The degree-4 extension field of Hachi. -/
abbrev Ext4 : Type := CompPoly.Extension.Ext ext4Params

/-- The adjoined fourth root of `2`, as an element of `Ext4`. -/
def ext4Gen : Ext4 := Ext.ofFn fun i => if (i : ℕ) = 1 then 1 else 0

@[simp] theorem card_ext4 : Fintype.card Ext4 = fieldSize ^ 4 := Ext.card_ext

end Hachi
