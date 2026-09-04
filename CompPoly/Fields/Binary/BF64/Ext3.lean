/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.BF64.Impl
public import CompPoly.Fields.Extension
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The degree-3 extension of `GF(2^64)`

```text
GF(2^64)[y] / (y^3 + y + 1),   giving GF(2^192)
```

An element is `c0 + c1 * y + c2 * y^2` with each coefficient in `BF64`. The carrier comes
from the computable extension framework in `CompPoly/Fields/Extension/`, so `Ext ext3Params`
is definitionally `Vector BF64 3` — the three-limb layout, with no translation needed.

Irreducibility needs no certificate here, unlike the degree-64 base modulus: a cubic is
irreducible exactly when it has no root, and a short characteristic-two argument rules one
out. See `CompPoly/Fields/KoalaBear/Ext5.lean` for the general monic-modulus pattern this
follows.

## Main definitions

* `ext3Poly` — the modulus `y^3 + y + 1` over `BF64`.
* `ext3Params` — its `CompPoly.Extension.ExtensionParams`.
* `Ext3` — the extension field itself.

## Main statements

* `ext3Poly_irreducible` — the cubic is irreducible over `BF64`.
* `ext3Params_poly` — the coefficient vector `#v[1, 1, 0]` denotes that cubic.
* `card_ext3` — `Fintype.card Ext3 = 2 ^ 192`.

## Implementation notes

`ext3Params_poly` is load-bearing: it ties the coefficient vector `#v[1, 1, 0]` to
`y ^ 3 + y + 1`. A wrong vector there would still compile and would silently give a
different field, so it is checked against reference vectors in
`tests/CompPolyTests/Fields/Binary/BF64.lean` rather than only re-derived.
-/

@[expose] public section

namespace BF64

open Polynomial CompPoly.Extension

set_option maxRecDepth 4000

/-! ## The defining cubic -/

/-- The extension modulus `y^3 + y + 1` over `GF(2^64)`. -/
noncomputable def ext3Poly : Polynomial BF64 := X ^ 3 + X + 1

theorem ext3Poly_natDegree : ext3Poly.natDegree = 3 := by
  rw [ext3Poly]; compute_degree!

theorem ext3Poly_degree : ext3Poly.degree = (3 : ℕ) := by
  rw [ext3Poly]; compute_degree!

theorem ext3Poly_monic : ext3Poly.Monic := by
  rw [ext3Poly]; monicity!

/-! ## Irreducibility

A cubic is irreducible exactly when it has no root. A root `a` of `y^3 + y + 1` satisfies
`a^3 = a + 1`, from which `a^7 = 1`. The multiplicative group of `GF(2^64)` has order
`2^64 - 1`, which is coprime to `7`, so `a = 1` — and `1` is not a root.
-/

/-- A root of the cubic would have multiplicative order dividing `7`. -/
private theorem pow_seven_of_isRoot {a : BF64} (h : ext3Poly.IsRoot a) : a ^ 7 = 1 := by
  have h3 : a ^ 3 = a + 1 := by
    have := h
    rw [ext3Poly, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at this
    rw [← sub_eq_zero, CharTwo.sub_eq_add,
      show a ^ 3 + (a + 1) = a ^ 3 + a + 1 from by ring]
    exact this
  calc a ^ 7 = (a ^ 3) ^ 2 * a := by ring
    _ = (a + 1) ^ 2 * a := by rw [h3]
    _ = (a ^ 2 + 1) * a := by rw [CharTwo.add_sq, one_pow]
    _ = a ^ 3 + a := by ring
    _ = (a + 1) + a := by rw [h3]
    _ = 1 := by rw [add_comm a 1, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The cubic has no root in `GF(2^64)`.

A root has `a ^ 7 = 1`, so its multiplicative order divides `7`. It also divides
`Fintype.card BF64 - 1 = 2 ^ 64 - 1`, which is coprime to `7`, so the order is `1` and
`a = 1`. But `1` is not a root.
-/
theorem ext3Poly_no_root (a : BF64) : ¬ext3Poly.IsRoot a := by
  intro h
  have h7 := pow_seven_of_isRoot h
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at h7
    exact zero_ne_one h7
  -- the order divides 7 and divides the group order
  have hdvd7 : orderOf a ∣ 7 := orderOf_dvd_of_pow_eq_one h7
  have hdvdcard : orderOf a ∣ 2 ^ 64 - 1 := by
    have hc : a ^ (Fintype.card BF64 - 1) = 1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [card_bf64] at hc
    exact orderOf_dvd_of_pow_eq_one hc
  have hcop : Nat.Coprime 7 (2 ^ 64 - 1) := by decide +kernel
  have h1 : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd7 hdvdcard
  have : a = 1 := orderOf_eq_one_iff.mp h1
  -- but 1 is not a root
  rw [this] at h
  rw [ext3Poly, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, one_pow] at h
  rw [show (1 : BF64) + 1 + 1 = 1 from by
    rw [CharTwo.add_self_eq_zero, zero_add]] at h
  exact one_ne_zero h

/-- The cubic `y^3 + y + 1` is irreducible over `GF(2^64)`. -/
theorem ext3Poly_irreducible : Irreducible ext3Poly :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [ext3Poly_natDegree]; decide) ext3Poly_no_root

instance : Fact (Irreducible ext3Poly) := ⟨ext3Poly_irreducible⟩

/-! ## The extension field -/

/-- Parameters of `GF(2^64)[y] / (y^3 + y + 1)`: degree three, with lower coefficients
`(1, 1, 0)` encoding `1 + y` below the leading `y^3`. -/
def ext3Params : ExtensionParams BF64 where
  d := 3
  two_le := by norm_num
  lower := #v[1, 1, 0]
  q := 2 ^ 64
  card_eq := card_bf64

@[simp] theorem ext3Params_d : ext3Params.d = 3 := rfl
@[simp] theorem ext3Params_q : ext3Params.q = 2 ^ 64 := rfl

/-- The parameters' defining polynomial is the cubic. -/
theorem ext3Params_poly : ext3Params.poly = ext3Poly := by
  have h0 : ext3Params.lowerCoeff ⟨0, by norm_num⟩ = 1 := rfl
  have h1 : ext3Params.lowerCoeff ⟨1, by norm_num⟩ = 1 := rfl
  have h2 : ext3Params.lowerCoeff ⟨2, by norm_num⟩ = 0 := rfl
  rw [ExtensionParams.poly, ext3Poly]
  show X ^ 3 + (∑ i : Fin 3, C (ext3Params.lowerCoeff i) * X ^ (i : ℕ)) = X ^ 3 + X + 1
  rw [Fin.sum_univ_three]
  rw [show ext3Params.lowerCoeff (0 : Fin 3) = 1 from h0,
    show ext3Params.lowerCoeff (1 : Fin 3) = 1 from h1,
    show ext3Params.lowerCoeff (2 : Fin 3) = 0 from h2]
  simp only [map_zero, map_one]
  rw [show ((0 : Fin 3) : ℕ) = 0 from rfl, show ((1 : Fin 3) : ℕ) = 1 from rfl]
  ring

instance : Fact (Irreducible ext3Params.poly) :=
  ⟨ext3Params_poly ▸ ext3Poly_irreducible⟩

/-- `GF(2^192)`, the degree-three extension `GF(2^64)[y] / (y^3 + y + 1)`.

Definitionally `Vector BF64 3`, the three-limb layout `c0 + c1 * y + c2 * y^2`. -/
abbrev Ext3 : Type := Ext ext3Params

/-- `Ext3` has `2 ^ 192` elements. -/
theorem card_ext3 : Fintype.card Ext3 = 2 ^ 192 := by
  rw [Ext.card_ext, ext3Params_q, ext3Params_d, ← pow_mul]

end BF64
