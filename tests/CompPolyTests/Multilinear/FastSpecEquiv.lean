/-
Copyright (c) 2026 CompPoly, Elias Judin, Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic)
-/
import CompPoly.Multilinear.Equiv
import CompPoly.Multilinear.FastSpecEquiv

/-!
# Multilinear Fast/Spec Equivalence Tests

Regression tests for the fast butterfly Möbius
transform (`lagrangeToMono`) agreeing with the
closed-form specification (`lagrangeToMonoSpec`).

Covers:
- Explicit fast/spec equality (via `decide`)
- The main theorem instantiation
- Both round-trip directions
-/

namespace CompPoly
open CMlPolynomial

/-! ### Explicit fast/spec equality (small n) -/

-- n = 0: single element
example : lagrangeToMono 0 #v[(42 : ℤ)] =
    lagrangeToMonoSpec #v[(42 : ℤ)] := by
  decide

-- n = 1: two elements
example :
    lagrangeToMono 1 #v[(10 : ℤ), 20] =
    lagrangeToMonoSpec
      #v[(10 : ℤ), 20] := by decide

-- n = 2: four elements
set_option maxHeartbeats 800000 in
example :
    lagrangeToMono 2
      #v[(1 : ℤ), 2, 3, 4] =
    lagrangeToMonoSpec
      #v[(1 : ℤ), 2, 3, 4] := by decide

/-! ### Main theorem instantiation -/

-- The theorem works for any AddCommGroup
example {R : Type*} [AddCommGroup R]
    (v : Vector R (2 ^ 3)) :
    lagrangeToMono 3 v =
      lagrangeToMonoSpec v :=
  lagrangeToMono_eq_lagrangeToMonoSpec v

example {R : Type*} [AddCommGroup R]
    (v : Vector R (2 ^ 5)) :
    lagrangeToMono 5 v =
      lagrangeToMonoSpec v :=
  lagrangeToMono_eq_lagrangeToMonoSpec v

-- Specific types
example (v : Vector ℤ (2 ^ 4)) :
    lagrangeToMono 4 v =
      lagrangeToMonoSpec v :=
  lagrangeToMono_eq_lagrangeToMonoSpec v

example (v : Vector ℚ (2 ^ 4)) :
    lagrangeToMono 4 v =
      lagrangeToMonoSpec v :=
  lagrangeToMono_eq_lagrangeToMonoSpec v

/-! ### Round-trip (via equivMonomialLagrangeRepr)

These are existing results, just checked here
for regression coverage. -/

-- mono → lagrange → mono
example {R : Type*} [AddCommGroup R]
    (v : CMlPolynomial R 3) :
    lagrangeToMono 3 (monoToLagrange 3 v) =
      v :=
  equivMonomialLagrangeRepr.left_inv v

-- lagrange → mono → lagrange
example {R : Type*} [AddCommGroup R]
    (v : CMlPolynomialEval R 3) :
    monoToLagrange 3 (lagrangeToMono 3 v) =
      v :=
  equivMonomialLagrangeRepr.right_inv v

end CompPoly
