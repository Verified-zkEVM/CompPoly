/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.OddBucket
import CompPoly.Univariate.Roots.LasVegas.Probability.Uniform

/-!
# Euler Bucket Counting for Odd Cantor-Zassenhaus Splitting

Finite-field counting facts about the deterministic Euler bucket classifier
`oddCZBucket`: the Euler criterion bridge, the bucket cardinalities
`1`, `(q - 1) / 2`, and `(q - 1) / 2`, and the resulting probability that two
independent uniform field values land in different buckets.

These theorems are field-theoretic, not algorithmic: they do not mention
`CPolynomial`, gcds, or the Las Vegas loop.
-/

open scoped Classical ENNReal NNReal BigOperators

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Euler criterion bridge: the square bucket consists of the nonzero squares. -/
theorem oddCZBucket_eq_square_iff_isSquare {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) (x : F) :
    oddCZBucket q x = OddCZBucket.square ↔ x ≠ 0 ∧ IsSquare x := by
  sorry

/--
Euler criterion bridge: over an odd field of cardinality `q`, the residual
nonsquare bucket is exactly the locus `x ^ ((q - 1) / 2) = -1`.
-/
theorem oddCZBucket_eq_nonsquare_iff_pow_eq_neg_one {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) (x : F) :
    oddCZBucket q x = OddCZBucket.nonsquare ↔ x ^ ((q - 1) / 2) = -1 := by
  sorry

/-- The zero Euler bucket has exactly one element. -/
theorem card_oddCZBucket_zero {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F] (q : Nat) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.zero).card = 1 := by
  sorry

/-- The square Euler bucket of an odd field of cardinality `q` has `(q - 1) / 2` elements. -/
theorem card_oddCZBucket_square {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.square).card =
      (q - 1) / 2 := by
  sorry

/-- The nonsquare Euler bucket of an odd field of cardinality `q` has `(q - 1) / 2` elements. -/
theorem card_oddCZBucket_nonsquare {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (Finset.univ.filter fun x : F ↦ oddCZBucket q x = OddCZBucket.nonsquare).card =
      (q - 1) / 2 := by
  sorry

/--
Two independent uniform field values land in different Euler buckets with
probability at least `1 / 2`.

With bucket masses `1 / q`, `m / q`, and `m / q` for `m = (q - 1) / 2`, the
collision probability is `(1 + 2 * m ^ 2) / q ^ 2`, so the separation
probability is `(q - 1) * (q + 3) / (2 * q ^ 2) ≥ 1 / 2` for every odd `q ≥ 3`.
-/
theorem oddCZBucket_pair_separated_probability_ge_half {F : Type*}
    [Field F] [Fintype F] [BEq F] [LawfulBEq F]
    {q : Nat} (enumeration : UniformFieldEnumeration F q)
    (hodd : q % 2 = 1) (hcard : Fintype.card F = q) :
    (2 : ℝ≥0∞)⁻¹ ≤
      eventProbability
        ((uniformFieldElementPMF enumeration.toFieldEnumeration).bind
          fun x ↦ (uniformFieldElementPMF enumeration.toFieldEnumeration).map
            fun y ↦ (x, y))
        {xy | oddCZBucket q xy.1 ≠ oddCZBucket q xy.2} := by
  sorry

end FiniteField

end Roots

end CPolynomial

end CompPoly
