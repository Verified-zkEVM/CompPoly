/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension
public import CompPoly.Fields.KoalaBear.Ext5.QuinticIrreducible

/-!
# The degree-5 extension of KoalaBear

`KoalaBear[X] / (X^5 + X^2 - 1)`. The modulus is necessarily *not* a binomial: since
`gcd(5, p - 1) = 1`, the map `x ↦ x^5` is a bijection on KoalaBear, so every `X^5 - W` has a
root and no degree-5 binomial extension exists. This is the first consumer of the general
monic-modulus side of the extension framework (`CompPoly.Extension.ExtensionParams`).

Irreducibility of `X^5 + X^2 - 1` is `KoalaBear.quinticPoly_irreducible`
(`CompPoly/Fields/KoalaBear/Ext5/QuinticIrreducible.lean`), proved by Rabin's test at prime
degree with kernel-checked certificates. Supporting files live under `KoalaBear/Ext5/`.

## Main definitions

* `KoalaBear.ext5Params`: the `ExtensionParams` for `X^5 + X^2 - 1`.
* `KoalaBear.Ext5`: the extension field itself.
-/

@[expose] public section

namespace KoalaBear

open CompPoly.Extension Polynomial

/-- The parameters of the quintic extension `KoalaBear[X] / (X^5 + X^2 - 1)`: the lower
coefficients of the monic modulus are `(-1, 0, 1, 0, 0)`. -/
def ext5Params : ExtensionParams Field where
  d := 5
  two_le := by norm_num
  lower := #v[-1, 0, 1, 0, 0]
  q := fieldSize
  card_eq := ZMod.card _

@[simp] theorem ext5Params_d : ext5Params.d = 5 := rfl
@[simp] theorem ext5Params_q : ext5Params.q = fieldSize := rfl

/-- The defining polynomial of the parameters is the quintic `X^5 + X^2 - 1`. -/
theorem ext5Params_poly : ext5Params.poly = quinticPoly := by
  have h0 : ext5Params.lowerCoeff ⟨0, by norm_num⟩ = -1 := rfl
  have h1 : ext5Params.lowerCoeff ⟨1, by norm_num⟩ = 0 := rfl
  have h2 : ext5Params.lowerCoeff ⟨2, by norm_num⟩ = 1 := rfl
  have h3 : ext5Params.lowerCoeff ⟨3, by norm_num⟩ = 0 := rfl
  have h4 : ext5Params.lowerCoeff ⟨4, by norm_num⟩ = 0 := rfl
  rw [ExtensionParams.poly, quinticPoly]
  show X ^ 5 + (∑ i : Fin 5, C (ext5Params.lowerCoeff i) * X ^ (i : ℕ)) = X ^ 5 + X ^ 2 - C 1
  rw [Fin.sum_univ_five]
  rw [show ext5Params.lowerCoeff (0 : Fin 5) = -1 from h0,
    show ext5Params.lowerCoeff (1 : Fin 5) = 0 from h1,
    show ext5Params.lowerCoeff (2 : Fin 5) = 1 from h2,
    show ext5Params.lowerCoeff (3 : Fin 5) = 0 from h3,
    show ext5Params.lowerCoeff (4 : Fin 5) = 0 from h4]
  simp only [map_neg, map_zero, map_one]
  rw [show ((0 : Fin 5) : ℕ) = 0 from rfl, show ((2 : Fin 5) : ℕ) = 2 from rfl]
  ring

/-- The irreducibility fact in the form the framework's `Field` instance consumes. -/
instance : Fact (Irreducible ext5Params.poly) :=
  ⟨ext5Params_poly ▸ quinticPoly_irreducible⟩

/-- The degree-5 extension field of KoalaBear. -/
abbrev Ext5 : Type := CompPoly.Extension.Ext ext5Params

/-- The adjoined root of `X^5 + X^2 - 1`, as an element of `Ext5`. -/
def ext5Gen : Ext5 := Ext.gen

/--
`ext5Gen` is the framework's `Ext.gen`.

Deliberately **not** `@[simp]`: as a rewrite it fires before `ext5Gen_pow_five` can match, which
would knock that lemma out of the simp set.
-/
theorem ext5Gen_eq_gen : ext5Gen = Ext.gen := rfl

/-- `ext5Gen` maps to the adjoined root of the specification. -/
@[simp] theorem toQuot_ext5Gen : Ext.toQuot ext5Gen = Ext.rt ext5Params := Ext.toQuot_gen

/-- `ext5Gen` is a root of `X^5 + X^2 - 1`, in the form `aeval` expects. -/
theorem aeval_ext5Gen : aeval ext5Gen ext5Params.poly = 0 := Ext.aeval_gen_poly

/-- **The defining relation**: the adjoined root satisfies `g^5 = 1 - g^2`. -/
@[simp] theorem ext5Gen_pow_five : ext5Gen ^ 5 = Ext.ofBase (1 : Field) - ext5Gen ^ 2 := by
  have h := aeval_ext5Gen
  rw [ext5Params_poly, quinticPoly] at h
  simp only [map_add, map_sub, map_pow, aeval_X, aeval_C, Ext.algebraMap_eq_ofBase] at h
  linear_combination h

@[simp] theorem card_ext5 : Fintype.card Ext5 = fieldSize ^ 5 := Ext.card_ext

end KoalaBear
