/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Data.Polynomial.Frobenius

/-!
# Frobenius divisibility: the numeral-parameterized forms

`Polynomial.irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd` states
`q ∣ X^(c^n) - X ↔ deg q ∣ n` at a caller-supplied numeral `c` with `Fintype.card R = c`, so a
concrete field applies it without a `rw [ZMod.card]` cast around a large-exponent divisibility.
`irreducible_dvd_X_pow_add_X_iff_natDegree_dvd` is its characteristic-two form, stated with `+ X`
so a binary field does not rewrite under the exponent either.

Passing `rfl` for `hcard` has to give back the `Fintype.card R` statement verbatim; that is the
first theorem below.
-/

@[expose] public section

namespace CompPolyTests.Frobenius

open Polynomial

/-- At `hcard := rfl`, the criterion reads at `Fintype.card R`. -/
theorem dvd_iff_recovered {R : Type*} [Field R] [Fact (Nat.Prime (ringChar R))] [Fintype R]
    (n : ℕ) (q : Polynomial R) (hq_irr : Irreducible q) :
    q ∣ (X ^ ((Fintype.card R) ^ n) - X) ↔ q.natDegree ∣ n :=
  irreducible_dvd_X_pow_sub_X_iff_natDegree_dvd rfl n q hq_irr

/-- The characteristic-two `+ X` form does the same at `c := Fintype.card R`. -/
theorem dvd_add_iff_recovered {R : Type*} [Field R] [Fact (Nat.Prime (ringChar R))] [Fintype R]
    [CharP R 2] (n : ℕ) (q : Polynomial R) (hq_irr : Irreducible q) :
    q ∣ (X ^ ((Fintype.card R) ^ n) + X) ↔ q.natDegree ∣ n :=
  irreducible_dvd_X_pow_add_X_iff_natDegree_dvd rfl n q hq_irr

/-- The two spellings coincide in characteristic two, which is what the `+ X` form absorbs. -/
theorem add_iff_sub {R : Type*} [Field R] [Fintype R] [CharP R 2] (n : ℕ) (q : Polynomial R) :
    q ∣ (X ^ ((Fintype.card R) ^ n) + X) ↔ q ∣ (X ^ ((Fintype.card R) ^ n) - X) := by
  rw [CharTwo.sub_eq_add]

end CompPolyTests.Frobenius
