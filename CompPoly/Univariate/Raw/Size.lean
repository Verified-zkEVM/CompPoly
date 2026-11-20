/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

import all CompPoly.Univariate.Raw.Ops
public import CompPoly.Univariate.Raw.Ops

/-!
# Sizes of raw polynomial operations

These bounds concern stored coefficient arrays, including trailing zero coefficients.
Raw multiplication retains the padding of its shifted rows even when the right input is empty.
`CompPoly.Univariate.Raw.Ops` states the size equations of `smul`, `mulPowX`, `addRaw` and
`mulRaw`, next to the operations. This module imports it publicly. The product bound
`size_mulRaw_le` was ported from ArkLib's raw-size adapter under Apache 2.0. The file header keeps
its original copyright attribution.
-/

public section

namespace CompPoly.CPolynomial.Raw

/-- A raw constant stores one coefficient, including when that coefficient is zero. -/
@[simp]
theorem size_C {R : Type*} (x : R) : (C x).size = 1 := by
  rfl

/-- Compatibility name for the public theorem previously provided by `Raw.Proofs`. -/
@[deprecated (since := "2026-11-03")]
alias add_size := size_addRaw

/-- The raw product's stored size is at most the sum of the input sizes minus one. -/
theorem size_mulRaw_le {R : Type*} [Semiring R] (p q : Raw R) :
    (mulRaw p q).size ≤ p.size + q.size - 1 := by
  rw [size_mulRaw]
  split_ifs <;> omega

end CompPoly.CPolynomial.Raw
