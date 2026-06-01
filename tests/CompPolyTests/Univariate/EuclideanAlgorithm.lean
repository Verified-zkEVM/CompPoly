/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import CompPoly.Univariate.EuclideanAlgorithm
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Tests: `xgcd` gcd and partial (threshold) behavior

`#guard` checks over `ZMod 7`. Mathlib's `Polynomial` arithmetic is
`noncomputable`, so we can't evaluate `EuclideanDomain.gcd` at runtime; the
expected gcds are hardcoded as `CPolynomial` values and compared with `==`.
-/

open CompPoly

namespace CompPolyTests
namespace EuclideanAlgorithmTest

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev F : Type := ZMod 7

/-! ### Test 1: `gcd(X² - 1, X - 1) = X - 1` -/

private def p₁ : CPolynomial F := CPolynomial.X ^ 2 - 1
private def q₁ : CPolynomial F := CPolynomial.X - 1

-- `X - 1`, stored as `[6, 1]` since `-1 = 6` in `ZMod 7`.
private def gcd₁ : CPolynomial F := CPolynomial.X - 1

#guard (CPolynomial.xgcd p₁ q₁ 0).1 == gcd₁

/-! ### Test 2: `gcd((X-1)(X-2), (X-1)(X-3))`, associate of `X - 1`. -/

private def p₂ : CPolynomial F :=
  (CPolynomial.X - 1) * (CPolynomial.X - CPolynomial.C 2)
private def q₂ : CPolynomial F :=
  (CPolynomial.X - 1) * (CPolynomial.X - CPolynomial.C 3)

-- xgcd gives `1 - X`, an associate of `X - 1` (`-1 = 6` is a unit in
-- `ZMod 7`); stored as `[1, 6]`.
private def gcd₂ : CPolynomial F := 1 - CPolynomial.X

#guard (CPolynomial.xgcd p₂ q₂ 0).1 == gcd₂

/-! ### Test 3: coprime inputs `X + 1`, `X + 2`. xgcd returns the unit `1`. -/

private def p₃ : CPolynomial F := CPolynomial.X + 1
private def q₃ : CPolynomial F := CPolynomial.X + CPolynomial.C 2

private def gcd₃ : CPolynomial F := 1

#guard (CPolynomial.xgcd p₃ q₃ 0).1 == gcd₃

/-! ### Bezout-identity sanity checks (`threshold = 0`) -/

#guard
  let t := CPolynomial.xgcd p₁ q₁ 0
  t.2.1 * p₁ + t.2.2 * q₁ == t.1

#guard
  let t := CPolynomial.xgcd p₂ q₂ 0
  t.2.1 * p₂ + t.2.2 * q₂ == t.1

#guard
  let t := CPolynomial.xgcd p₃ q₃ 0
  t.2.1 * p₃ + t.2.2 * q₃ == t.1

/-! ### Threshold behavior (`threshold > 0`) -/

/-! #### Test 4: overshoot to `r = 0` returns the gcd, not `(0, s, t)`.

`gcd(X², X) = X` has degree `1`, not `< threshold = 1`, so the run reaches
`r = 0` and the `r == 0` branch returns the previous triple, the gcd `X`.
Regression guard: the old `r.natDegree < threshold`-first ordering returned
`(0, …)` here, since `natDegree 0 = 0 < 1`. -/

private def p₄ : CPolynomial F := CPolynomial.X ^ 2
private def q₄ : CPolynomial F := CPolynomial.X

#guard (CPolynomial.xgcd p₄ q₄ 1).1 == CPolynomial.X
-- Overshoot at `threshold = 1` agrees with the full `threshold = 0` gcd.
#guard (CPolynomial.xgcd p₄ q₄ 1).1 == (CPolynomial.xgcd p₄ q₄ 0).1
#guard
  let t := CPolynomial.xgcd p₄ q₄ 1
  t.2.1 * p₄ + t.2.2 * q₄ == t.1

/-! #### Test 5: coprime, stops one iteration early via the threshold branch.

At `threshold = 1` the final loop has `r = 1 ≠ 0` with `natDegree 0 < 1`, so
the threshold branch fires and returns `(1, …)`, one step before the
`threshold = 0` run reaches `r = 0`. Same triple either way. -/

#guard (CPolynomial.xgcd p₃ q₃ 1).1 == gcd₃
-- Same triple as the full run.
#guard CPolynomial.xgcd p₃ q₃ 1 == CPolynomial.xgcd p₃ q₃ 0
#guard
  let t := CPolynomial.xgcd p₃ q₃ 1
  t.2.1 * p₃ + t.2.2 * q₃ == t.1

/-! #### Test 6: genuine truncation, threshold returns a non-gcd remainder.

`X³` and `X² + 1` are coprime (gcd `1`), but `threshold = 2` stops at the
first remainder of degree `< 2`, the degree-`1` one, not the gcd. The result
depends on the threshold, and Bezout still holds for the truncated triple. -/

private def p₆ : CPolynomial F := CPolynomial.X ^ 3
private def q₆ : CPolynomial F := CPolynomial.X ^ 2 + 1

-- Full gcd is the unit.
#guard (CPolynomial.xgcd p₆ q₆ 0).1 == gcd₃
-- Partial run stops at a degree-1 remainder (≠ the degree-0 gcd).
#guard (CPolynomial.xgcd p₆ q₆ 2).1.natDegree == 1
#guard
  let t := CPolynomial.xgcd p₆ q₆ 2
  t.2.1 * p₆ + t.2.2 * q₆ == t.1

end EuclideanAlgorithmTest
end CompPolyTests
