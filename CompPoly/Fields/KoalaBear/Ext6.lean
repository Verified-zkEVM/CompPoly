/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension
public import CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible

/-!
# The degree-6 extension of KoalaBear

`KoalaBear[X] / (X^6 + X^3 + 1)`, a field of `p^6 ≈ 2^186` elements. The modulus is `Φ₉`, the
ninth cyclotomic polynomial, so the adjoined root `θ` is a primitive 9th root of unity.

As at degree 5, the modulus is necessarily *not* a binomial, and for a stronger reason: since
`p - 1 = 2^24 · 127` we have `3 ∤ p - 1`, so `x ↦ x^3` is a bijection on KoalaBear and every `W`
is a cube `V^3`, whence `X^6 - W = (X^2 - V)(X^4 + V X^2 + V^2)` factors for *every* `W`. So no
degree-6 binomial extension of KoalaBear exists at all.

`Φ₉` is chosen among the irreducible sextics because every entry of its reduction table
`X^6 … X^10 mod f` is `±1` — reduction costs no base-field multiplications — and the same holds
for its Frobenius matrix, since `p ≡ 2 mod 9` makes Frobenius `θ ↦ θ^2`. It also carries the
`2`-then-`3` tower implicitly: `θ^3` is a primitive cube root of unity generating the `F_p²`
subfield, because `Y^2 + Y + 1` is irreducible over KoalaBear.

Irreducibility of `X^6 + X^3 + 1` is `KoalaBear.sexticPoly_irreducible`
(`CompPoly/Fields/KoalaBear/Ext6/SexticIrreducible.lean`), proved by Rabin's test at a degree with
two prime factors, with kernel-checked certificates for all three conditions. Supporting files
live under `KoalaBear/Ext6/`.

This sits alongside `KoalaBear.Ext5` rather than replacing it; the two are independent instances
of the same framework.

## Main definitions

* `KoalaBear.ext6Params`: the `ExtensionParams` for `X^6 + X^3 + 1`.
* `KoalaBear.Ext6`: the extension field itself.
-/

@[expose] public section

namespace KoalaBear

open CompPoly.Extension Polynomial

/-- The parameters of the sextic extension `KoalaBear[X] / (X^6 + X^3 + 1)`: the lower
coefficients of the monic modulus are `(1, 0, 0, 1, 0, 0)`. -/
def ext6Params : ExtensionParams Field where
  d := 6
  two_le := by norm_num
  lower := #v[1, 0, 0, 1, 0, 0]
  q := fieldSize
  card_eq := ZMod.card _

@[simp] theorem ext6Params_d : ext6Params.d = 6 := rfl
@[simp] theorem ext6Params_q : ext6Params.q = fieldSize := rfl

/-- The defining polynomial of the parameters is the sextic `X^6 + X^3 + 1`. -/
theorem ext6Params_poly : ext6Params.poly = sexticPoly := by
  have h0 : ext6Params.lowerCoeff ⟨0, by norm_num⟩ = 1 := rfl
  have h1 : ext6Params.lowerCoeff ⟨1, by norm_num⟩ = 0 := rfl
  have h2 : ext6Params.lowerCoeff ⟨2, by norm_num⟩ = 0 := rfl
  have h3 : ext6Params.lowerCoeff ⟨3, by norm_num⟩ = 1 := rfl
  have h4 : ext6Params.lowerCoeff ⟨4, by norm_num⟩ = 0 := rfl
  have h5 : ext6Params.lowerCoeff ⟨5, by norm_num⟩ = 0 := rfl
  rw [ExtensionParams.poly, sexticPoly]
  show X ^ 6 + (∑ i : Fin 6, C (ext6Params.lowerCoeff i) * X ^ (i : ℕ)) = X ^ 6 + X ^ 3 + C 1
  rw [Fin.sum_univ_six]
  rw [show ext6Params.lowerCoeff (0 : Fin 6) = 1 from h0,
    show ext6Params.lowerCoeff (1 : Fin 6) = 0 from h1,
    show ext6Params.lowerCoeff (2 : Fin 6) = 0 from h2,
    show ext6Params.lowerCoeff (3 : Fin 6) = 1 from h3,
    show ext6Params.lowerCoeff (4 : Fin 6) = 0 from h4,
    show ext6Params.lowerCoeff (5 : Fin 6) = 0 from h5]
  simp only [map_zero, map_one]
  rw [show ((0 : Fin 6) : ℕ) = 0 from rfl, show ((3 : Fin 6) : ℕ) = 3 from rfl]
  ring

/-- The irreducibility fact in the form the framework's `Field` instance consumes. -/
instance : Fact (Irreducible ext6Params.poly) :=
  ⟨ext6Params_poly ▸ sexticPoly_irreducible⟩

/-- The degree-6 extension field of KoalaBear. -/
abbrev Ext6 : Type := CompPoly.Extension.Ext ext6Params

/-- The adjoined root of `X^6 + X^3 + 1`, a primitive 9th root of unity, as an element of
`Ext6`. -/
def ext6Gen : Ext6 := Ext.gen

/--
`ext6Gen` is the framework's `Ext.gen`.

Deliberately **not** `@[simp]`: as a rewrite it fires before `ext6Gen_pow_six` can match, which
would knock that lemma out of the simp set.
-/
theorem ext6Gen_eq_gen : ext6Gen = Ext.gen := rfl

/-- `ext6Gen` maps to the adjoined root of the specification. -/
@[simp] theorem toQuot_ext6Gen : Ext.toQuot ext6Gen = Ext.rt ext6Params := Ext.toQuot_gen

/-- `ext6Gen` is a root of `X^6 + X^3 + 1`, in the form `aeval` expects. -/
theorem aeval_ext6Gen : aeval ext6Gen ext6Params.poly = 0 := Ext.aeval_gen_poly

/-- **The defining relation**: the adjoined root satisfies `θ^6 = -θ^3 - 1`. Every coefficient is
`±1`, which is what makes reduction multiplication-free. -/
@[simp] theorem ext6Gen_pow_six :
    ext6Gen ^ 6 = -(ext6Gen ^ 3) - Ext.ofBase (1 : Field) := by
  have h := aeval_ext6Gen
  rw [ext6Params_poly, sexticPoly] at h
  simp only [map_add, map_pow, aeval_X, aeval_C, Ext.algebraMap_eq_ofBase] at h
  linear_combination h

/-- `θ^3` is a primitive cube root of unity: it satisfies `Y^2 + Y + 1 = 0`, which is irreducible
over KoalaBear because `3 ∤ p - 1`. So `F_p(θ^3)` is the `F_p²` subfield, and this is the
`2`-then-`3` tower `F_p ⊂ F_p² ⊂ F_p⁶` presented inside a single sextic. -/
theorem ext6Gen_cubed_is_primitive_cube_root :
    (ext6Gen ^ 3) ^ 2 + ext6Gen ^ 3 + Ext.ofBase (1 : Field) = 0 := by
  have h := ext6Gen_pow_six
  linear_combination h

/-- **`θ` is a primitive 9th root of unity**: `θ^9 = 1`. -/
@[simp] theorem ext6Gen_pow_nine : ext6Gen ^ 9 = 1 := by
  have h := ext6Gen_cubed_is_primitive_cube_root
  have hone : Ext.ofBase (1 : Field) = (1 : Ext6) := Ext.ofBase_one
  rw [hone] at h
  linear_combination (ext6Gen ^ 3 - 1) * h

@[simp] theorem card_ext6 : Fintype.card Ext6 = fieldSize ^ 6 := Ext.card_ext

end KoalaBear
