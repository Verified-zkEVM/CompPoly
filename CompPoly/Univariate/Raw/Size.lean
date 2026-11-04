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
The scalar, shift and product facts were ported from ArkLib's raw-size adapter under Apache 2.0;
its original copyright attribution is retained.
-/

public section

namespace CompPoly.CPolynomial.Raw

/-- A raw constant stores one coefficient, including when that coefficient is zero. -/
@[simp]
theorem size_C {R : Type*} (x : R) : (C x).size = 1 := by
  rfl

/-- Scalar multiplication preserves the stored coefficient count. -/
@[simp]
theorem size_smul {R : Type*} [Mul R] (x : R) (p : Raw R) :
    (smul x p).size = p.size := by
  simp only [smul, Array.size_map]

/-- Multiplication by `X^i` retains all of the prepended zero coefficients. -/
@[simp]
theorem size_mulPowX {R : Type*} [Zero R] (i : Nat) (p : Raw R) :
    (mulPowX i p).size = i + p.size := by
  simp only [mulPowX, Array.size_append, Array.size_replicate]

/-- Padded raw addition stores the larger input size. -/
@[simp]
theorem size_addRaw {Q : Type*} [Zero Q] [Add Q] {p q : Raw Q} :
    (addRaw p q).size = max p.size q.size := by
  simp only [addRaw, Array.size_zipWith, Array.size_rightpad]
  omega

/-- Compatibility name for the public theorem previously provided by `Raw.Proofs`. -/
@[deprecated (since := "2026-11-03")]
alias add_size := size_addRaw

/-- Raw multiplication retains every shifted row, including padding from an empty right array. -/
theorem size_mulRaw {R : Type*} [Semiring R] (p q : Raw R) :
    (mulRaw p q).size = if p.size = 0 then 0 else q.size + p.size - 1 := by
  unfold mulRaw
  have h := Array.foldl_induction (as := p.zipIdx)
    (motive := fun i (acc : Raw R) ↦ acc.size = if i = 0 then 0 else q.size + i - 1)
    (init := mk #[]) (by rfl)
    (f := fun acc ai ↦ acc.addRaw ((smul ai.1 q).mulPowX ai.2)) ?_
  · simpa only [Array.size_zipIdx] using h
  · intro i acc ih
    have hz : (p.zipIdx)[i].2 = i.val := by
      change ((p.zipIdx)[i.val]'i.isLt).2 = i.val
      rw [Array.getElem_zipIdx]
      exact Nat.zero_add _
    simp only [size_addRaw, size_mulPowX, size_smul]
    rw [hz, ih]
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
      omega

/-- The raw product's stored size is at most the sum of the input sizes minus one. -/
theorem size_mulRaw_le {R : Type*} [Semiring R] (p q : Raw R) :
    (mulRaw p q).size ≤ p.size + q.size - 1 := by
  rw [size_mulRaw]
  split_ifs <;> omega

end CompPoly.CPolynomial.Raw
