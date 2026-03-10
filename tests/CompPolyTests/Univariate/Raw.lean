/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen, Elias Judin
-/
import CompPoly.Univariate.Raw

/-!
  # Univariate Raw Regression Tests

  Lightweight regression checks for `CompPoly.Univariate.Raw`.

  Note: These tests previously used `native_decide` which is banned from the
  project TCB (see AGENTS.md). The `divByMonic`/`modByMonic` operations over `ℚ`
  do not reduce by `decide` or `rfl` because `ℚ` normalization is not
  definitionally computable. Tests are verified at meta-level via `#guard`.
-/

open CompPoly CPolynomial.Raw in
-- Regression test for issue #115: (X^2 - 1) / (X + 1) = X - 1
#guard
  divByMonic ((X : CPolynomial.Raw ℚ) ^ 2 - C 1) ((X : CPolynomial.Raw ℚ) + C 1)
    == #[-(1 : ℚ), 1]

open CompPoly CPolynomial.Raw in
#guard
  modByMonic ((X : CPolynomial.Raw ℚ) ^ 2 - C 1) ((X : CPolynomial.Raw ℚ) + C 1)
    == #[]

open CompPoly CPolynomial.Raw in
-- Regression test for review-thread case: X^3 = (X^2 + 1) * X + (-X)
#guard
  divByMonic ((X : CPolynomial.Raw ℚ) ^ 3) ((X : CPolynomial.Raw ℚ) ^ 2 + C 1)
    == #[(0 : ℚ), 1]

open CompPoly CPolynomial.Raw in
#guard
  modByMonic ((X : CPolynomial.Raw ℚ) ^ 3) ((X : CPolynomial.Raw ℚ) ^ 2 + C 1)
    == #[(0 : ℚ), -(1 : ℚ)]
