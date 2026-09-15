/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension.Arithmetic
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Polynomial specifications for monic quotient presentations

`ExtensionParams.poly` interprets the lower coefficient vector as the monic polynomial
`X^d + ∑ i, C lower[i] * X^i`. The binomial specification is `X^d - W`; its conversion to
an arbitrary monic presentation preserves that polynomial.

The carrier and executable operations are defined in `Extension/Arithmetic.lean`. These
specifications do not certify the cardinality parameter or irreducibility. The quotient bridge
and field laws are supplied separately in `Extension/Bridge.lean` and `Extension/Field.lean`.
-/

@[expose] public section

namespace CompPoly.Extension

open Polynomial

variable {F : Type*} [Field F]

namespace ExtensionParams

variable (P : ExtensionParams F)

/-- The monic defining polynomial `X^d + ∑_{i < d} lower[i] · X^i`. Part of the specification
only; the computable arithmetic on `Ext P` never evaluates it. -/
noncomputable def poly : F[X] := X ^ P.d + ∑ i : Fin P.d, C (P.lowerCoeff i) * X ^ (i : ℕ)

/-- The lower part of the modulus has degree strictly less than `d`. -/
theorem degree_lower_lt :
    (∑ i : Fin P.d, C (P.lowerCoeff i) * X ^ (i : ℕ)).degree < (P.d : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe P.d)]
  intro i _
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast i.isLt)

theorem degree_poly : P.poly.degree = (P.d : WithBot ℕ) := by
  rw [poly, degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact P.degree_lower_lt),
    degree_X_pow]

theorem monic_poly : P.poly.Monic := by
  rw [poly]
  exact (monic_X_pow P.d).add_of_left (by rw [degree_X_pow]; exact P.degree_lower_lt)

@[simp] theorem natDegree_poly : P.poly.natDegree = P.d :=
  natDegree_eq_of_degree_eq_some P.degree_poly

end ExtensionParams

namespace BinomialParams

variable (P : BinomialParams F)

/-- The defining polynomial `X^d - W`. Part of the specification only. -/
noncomputable def poly : F[X] := X ^ P.d - C P.W

@[simp] theorem natDegree_poly : P.poly.natDegree = P.d := natDegree_X_pow_sub_C

theorem monic_poly : P.poly.Monic := monic_X_pow_sub_C _ (by have := P.two_le; omega)

/-- The general-framework polynomial of a binomial agrees with `X^d - W`. -/
theorem toExtensionParams_poly : P.toExtensionParams.poly = P.poly := by
  have hsum : (∑ i : Fin P.toExtensionParams.d,
      C (P.toExtensionParams.lowerCoeff i) * X ^ (i : ℕ)) = -C P.W := by
    rw [Finset.sum_eq_single_of_mem (⟨0, P.d_pos⟩ : Fin P.toExtensionParams.d) (Finset.mem_univ _)]
    · rw [toExtensionParams_lowerCoeff]; simp
    · intro i _ hi
      have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
      rw [toExtensionParams_lowerCoeff, if_neg hi0, map_zero, zero_mul]
  rw [ExtensionParams.poly, hsum, poly, ← sub_eq_add_neg, toExtensionParams_d]

end BinomialParams

end CompPoly.Extension
