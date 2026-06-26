/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Euler Buckets for Odd Cantor-Zassenhaus Splitting

Deterministic three-way classifier for field values seen by one odd-field
Cantor-Zassenhaus probe: zero values, nonzero values whose Euler power
`x ^ ((q - 1) / 2)` equals one, and the remaining nonzero values.

This module is shared by the deterministic correctness surface and the
probability surface, so it must stay free of `PMF` and measure-theory imports.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Euler bucket of a field value under one odd Cantor-Zassenhaus probe. -/
inductive OddCZBucket where
  | zero
  | square
  | nonsquare
  deriving DecidableEq, Repr

/--
Classify a value by its Euler power `x ^ ((q - 1) / 2)`.

The `nonsquare` bucket is the residual branch `x ≠ 0 ∧ x ^ ((q - 1) / 2) ≠ 1`;
identifying it with `x ^ ((q - 1) / 2) = -1` additionally needs `q` to be the
odd cardinality of the field, which is a probability-side bridge lemma.
-/
def oddCZBucket {F : Type*} [MonoidWithZero F] [BEq F] [LawfulBEq F]
    (q : Nat) (x : F) : OddCZBucket :=
  if x == 0 then
    OddCZBucket.zero
  else if x ^ ((q - 1) / 2) == 1 then
    OddCZBucket.square
  else
    OddCZBucket.nonsquare

/-- The zero bucket contains exactly the zero value. -/
theorem oddCZBucket_eq_zero_iff {F : Type*} [MonoidWithZero F] [BEq F] [LawfulBEq F]
    (q : Nat) (x : F) :
    oddCZBucket q x = OddCZBucket.zero ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [oddCZBucket, hx]
  · by_cases hpow : x ^ ((q - 1) / 2) = 1 <;> simp [oddCZBucket, hx, hpow]

/-- The square bucket contains exactly the nonzero values with Euler power one. -/
theorem oddCZBucket_eq_square_iff {F : Type*} [MonoidWithZero F] [BEq F] [LawfulBEq F]
    (q : Nat) (x : F) :
    oddCZBucket q x = OddCZBucket.square ↔ x ≠ 0 ∧ x ^ ((q - 1) / 2) = 1 := by
  by_cases hx : x = 0
  · simp [oddCZBucket, hx]
  · by_cases hpow : x ^ ((q - 1) / 2) = 1 <;> simp [oddCZBucket, hx, hpow]

/-- The nonsquare bucket is the residual branch of the classifier. -/
theorem oddCZBucket_eq_nonsquare_iff {F : Type*} [MonoidWithZero F] [BEq F] [LawfulBEq F]
    (q : Nat) (x : F) :
    oddCZBucket q x = OddCZBucket.nonsquare ↔ x ≠ 0 ∧ x ^ ((q - 1) / 2) ≠ 1 := by
  by_cases hx : x = 0
  · simp [oddCZBucket, hx]
  · by_cases hpow : x ^ ((q - 1) / 2) = 1 <;> simp [oddCZBucket, hx, hpow]

end FiniteField

end Roots

end CPolynomial

end CompPoly
