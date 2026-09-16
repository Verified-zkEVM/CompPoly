/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Fields.Binary.Tower.Concrete.Coordinates

/-!
# Quadratic arithmetic in concrete successor coordinates

At level `k + 1`, write an element as `lo + hi * Z (k + 1)` using the chosen embedding
from level `k`. The relation
`Z (k + 1) ^ 2 = 1 + canonicalAlgMap k (Z k) * Z (k + 1)` gives multiplication,
conjugation and norm formulas over the predecessor field. The inverse formula is total,
including zero, and describes the canonical concrete inverse with its existing fast paths.

These are concrete coordinate contracts for the tower described in [DP23], §2.3.
They use the existing predecessor-field proofs without importing the abstract tower bridge.

## References

* [Diamond, B. E. and Posen, J., *Succinct arguments over towers of binary fields*][DP23]
-/

public section

namespace ConcreteBinaryTower.Coordinates

/-- Multiplication in constant-first successor coordinates follows the quadratic relation
with linear coefficient `Z k` and constant coefficient one. -/
theorem joinSucc_mul_joinSucc (k : ℕ) (a₀ a₁ b₀ b₁ : ConcreteBTField k) :
    joinSucc k a₀ a₁ * joinSucc k b₀ b₁ =
      joinSucc k (a₀ * b₀ + a₁ * b₁)
        (a₀ * b₁ + b₀ * a₁ + (a₁ * b₁) * Z k) := by
  exact concrete_mul_eq (k := k + 1) (h_k := by omega)
    (getBTFResult k).toConcreteBTFieldProps _ _
    (split_join_eq_split (k := k + 1) (h_pos := by omega) a₁ a₀).symm
    (split_join_eq_split (k := k + 1) (h_pos := by omega) b₁ b₀).symm

/-- The constant coefficient of a product is the sum of the two diagonal products. -/
theorem low_mul (k : ℕ) (x y : ConcreteBTField (k + 1)) :
    low k (x * y) = low k x * low k y + high k x * high k y := by
  simpa only [joinSucc_low_high, low_joinSucc] using
    congrArg (low k) (joinSucc_mul_joinSucc k (low k x) (high k x) (low k y) (high k y))

/-- The generator coefficient of a product includes the quadratic linear-coefficient term. -/
theorem high_mul (k : ℕ) (x y : ConcreteBTField (k + 1)) :
    high k (x * y) = low k x * high k y + low k y * high k x +
      (high k x * high k y) * Z k := by
  simpa only [joinSucc_low_high, high_joinSucc] using
    congrArg (high k) (joinSucc_mul_joinSucc k (low k x) (high k x) (low k y) (high k y))

/-- Quadratic conjugation replaces the generator by itself plus the embedded `Z k`. -/
def conjugate (k : ℕ) (x : ConcreteBTField (k + 1)) : ConcreteBTField (k + 1) :=
  joinSucc k (low k x + high k x * Z k) (high k x)

/-- The predecessor-field norm in low/high coordinates. -/
def norm (k : ℕ) (x : ConcreteBTField (k + 1)) : ConcreteBTField k :=
  low k x * (low k x + high k x * Z k) + high k x * high k x

/-- The conjugate keeps the high coefficient and adds `high * Z k` to the low coefficient. -/
theorem conjugate_eq_joinSucc (k : ℕ) (x : ConcreteBTField (k + 1)) :
    conjugate k x = joinSucc k (low k x + high k x * Z k) (high k x) := by rfl

/-- The norm is `lo * (lo + hi * Z k) + hi * hi` in the predecessor field. -/
theorem norm_eq (k : ℕ) (x : ConcreteBTField (k + 1)) :
    norm k x = low k x * (low k x + high k x * Z k) + high k x * high k x := by rfl

/-- Multiplication by the quadratic conjugate is the embedded predecessor-field norm. -/
theorem mul_conjugate (k : ℕ) (x : ConcreteBTField (k + 1)) :
    x * conjugate k x = canonicalAlgMap k (norm k x) := by
  conv_lhs => lhs; rw [← joinSucc_low_high k x]
  rw [conjugate, joinSucc_mul_joinSucc]
  have hhi : low k x * high k x + (low k x + high k x * Z k) * high k x +
      (high k x * high k x) * Z k = 0 := by
    calc
      _ = (low k x * high k x + low k x * high k x) +
          ((high k x * high k x) * Z k + (high k x * high k x) * Z k) := by ring
      _ = 0 := by rw [add_self_cancel, add_self_cancel, add_zero]
  rw [hhi]
  rfl

/-- Conjugating twice recovers the original successor-field element. -/
@[simp] theorem conjugate_conjugate (k : ℕ) (x : ConcreteBTField (k + 1)) :
    conjugate k (conjugate k x) = x := by
  simp only [conjugate, low_joinSucc, high_joinSucc]
  rw [add_assoc, add_self_cancel, add_zero, joinSucc_low_high]

/-- A nonzero successor-field element has nonzero predecessor-field norm. -/
theorem norm_ne_zero (k : ℕ) (x : ConcreteBTField (k + 1)) (hx : x ≠ 0) :
    norm k x ≠ 0 :=
  norm_of_ne_zero_is_ne_zero (k := k + 1) (h_k_gt_0 := by omega) (getBTFResult k) x hx

/-- The canonical inverse has conjugate coordinates divided by the norm, including at zero. -/
theorem inv_eq_joinSucc (k : ℕ) (x : ConcreteBTField (k + 1)) :
    x⁻¹ = joinSucc k ((norm k x)⁻¹ * (low k x + high k x * Z k))
      ((norm k x)⁻¹ * high k x) := by
  by_cases hz : x = 0
  · subst x
    have hs : split (k := k + 1) (by omega) (0 : ConcreteBTField (k + 1)) = (0, 0) :=
      split_zero (by omega)
    simp only [norm, low, high, hs, zero_mul, mul_zero, add_zero, inv_zero]
    exact (join_zero_zero (k := k + 1) (by omega)).symm
  have hscale :
      joinSucc k ((norm k x)⁻¹ * (low k x + high k x * Z k))
        ((norm k x)⁻¹ * high k x) =
        canonicalAlgMap k ((norm k x)⁻¹) * conjugate k x := by
    have h := smul_joinSucc k (norm k x)⁻¹ (low k x + high k x * Z k) (high k x)
    change concreteTowerAlgebraMap k (k + 1) (Nat.le_succ k) (norm k x)⁻¹ *
      joinSucc k (low k x + high k x * Z k) (high k x) = _ at h
    rw [concreteTowerAlgebraMap_succ_1] at h
    exact h.symm
  rw [hscale]
  apply (mul_eq_one_iff_inv_eq₀ hz).mp
  calc
    x * (canonicalAlgMap k ((norm k x)⁻¹) * conjugate k x) =
        canonicalAlgMap k ((norm k x)⁻¹) * (x * conjugate k x) := by ring
    _ = canonicalAlgMap k ((norm k x)⁻¹) * canonicalAlgMap k (norm k x) := by
      rw [mul_conjugate]
    _ = canonicalAlgMap k ((norm k x)⁻¹ * norm k x) := (map_mul _ _ _).symm
    _ = 1 := by rw [inv_mul_cancel₀ (norm_ne_zero k x hz), map_one]

end ConcreteBinaryTower.Coordinates
