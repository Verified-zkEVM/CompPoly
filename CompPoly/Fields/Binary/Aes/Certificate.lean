/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module

public import CompPoly.Data.Polynomial.RabinCertificate

/-!
# Rabin certificate data for `p = 2`

The modulus `f` has little-endian coefficients `[1, 1, 0, 1, 1, 0, 0, 0, 1]`.

`d = 8` is composite, so Rabin's coprimality condition needs one certificate per
prime factor of `d` (2), at exponents p^4 respectively. Checking only the
linear-factor case would admit a product of equal-degree factors.

GENERATED. Do not edit by hand; regenerate with:

```sh
python3 scripts/gen_rabin_certificate.py --p 2 \
  --f='1,1,0,1,1,0,0,0,1' \
  --lean <this file> --namespace AesField.Certificate \
  --authors 'CompPoly Contributors'
```

These lists are untrusted data. Consumers validate them with kernel-checked
`CompPoly.RabinCert.runChain` equations and certificate-soundness theorems for
their specified polynomial. Defining the lists alone establishes no such theorem.
-/

@[expose] public section

namespace AesField.Certificate

open CompPoly.RabinCert

/-- Square-and-multiply chain for `X^(p^8) mod f` (8 steps). -/
def traceSteps : List Step := [
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨false, [0], [0, 0, 0, 0, 1]⟩,
  ⟨false, [1], [1, 1, 0, 1, 1]⟩,
  ⟨false, [1], [0, 1, 1, 1, 1, 0, 1]⟩,
  ⟨false, [0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 1, 1, 1]⟩,
  ⟨false, [1, 1, 0, 0, 1, 0, 1], [1, 0, 1, 1, 0, 0, 1]⟩,
  ⟨false, [1, 0, 0, 0, 1], [0, 1, 0, 1, 1, 1, 1, 1]⟩,
  ⟨false, [0, 1, 0, 0, 1, 0, 1], [0, 1]⟩]

/-! ### Coprimality with `X^(p^4) - X`, for the prime factor `2` of `d = 8`. -/

/-- Square-and-multiply chain for `X^(p^4) mod f` (4 steps). -/
def cop4Steps : List Step := [
  ⟨false, [0], [0, 0, 1]⟩,
  ⟨false, [0], [0, 0, 0, 0, 1]⟩,
  ⟨false, [1], [1, 1, 0, 1, 1]⟩,
  ⟨false, [1], [0, 1, 1, 1, 1, 0, 1]⟩]

/-- The residue `X^(p^4) mod f`. -/
def cop4Rp : List ℕ := [0, 1, 1, 1, 1, 0, 1]

/-- `cop4W = (X^(p^4) mod f) - X`, the reduced form of `X^(p^4) - X`. -/
def cop4W : List ℕ := [0, 0, 1, 1, 1, 0, 1]

/-- Bézout coefficient: `cop4U·f + cop4V·cop4W = 1`. -/
def cop4U : List ℕ := [1, 1, 0, 0, 1]

/-- Bézout coefficient: `cop4U·f + cop4V·cop4W = 1`. -/
def cop4V : List ℕ := [1, 0, 0, 0, 1, 0, 1]

end AesField.Certificate
