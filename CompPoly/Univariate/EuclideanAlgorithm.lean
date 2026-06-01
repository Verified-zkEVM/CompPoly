/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.DivisionCorrectness

/-!
# Extended Euclidean Algorithm for `CPolynomial`

`xgcd p q` returns a triple `(r, s, t)` with `r = s * p + t * q`.
Early stop when `r.natDegree < threshold`.
The default `threshold = 0` makes `r` the Greatest Common Divisior of `p` and `q`.
-/

namespace CompPoly

namespace CPolynomial

variable {R : Type*}

/-- Extended euclidean algorithm on `p, q`.

Stops when `r = 0`, `r.natDegree < threshold`, or fuel `n` exhausted.

Potential optimization: the raw long division behind `r' / r` already computes
`r' - (r' / r) * r` but it's not exposed through `CPolynomial R`.
-/
def xgcdAux [Field R] [BEq R] [LawfulBEq R]
  (threshold n : ℕ) (r s t r' s' t' : CPolynomial R) :
  CPolynomial R × CPolynomial R × CPolynomial R :=
  match n with
  | 0 => (r', s', t')
  | k + 1 =>
    if r == 0 then
      (r', s', t')
    else if r.natDegree < threshold then
      (r, s, t)
    else
      let q := r' / r
      xgcdAux threshold k
        (r' - q * r) (s' - q * s) (t' - q * t) r s t

/-- Extended euclidean algorithm for `(p, q)`.

Returns `(r, s, t)` with `r = s * p + t * q`.

With the default `threshold = 0` returns the gcd of `p` and `q`.
With `threshold > 0` stops when `r.natDegree < threshold`. -/
def xgcd [Field R] [BEq R] [LawfulBEq R]
  (p q : CPolynomial R) (threshold : ℕ := 0) :
  CPolynomial R × CPolynomial R × CPolynomial R :=
  xgcdAux threshold p.val.size p 1 0 q 0 1
