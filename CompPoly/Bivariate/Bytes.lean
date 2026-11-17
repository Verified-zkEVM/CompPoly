/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Bivariate.Basic
public import CompPoly.Univariate.Bytes

/-!
# Serialization of bivariate polynomials

`CBivariate R` is `CPolynomial (CPolynomial R)`, so its self-delimiting encoding is the
univariate one nested: a `u64` count of `Y`-coefficients, each a `u64` count of
`X`-coefficients followed by those coefficients. Nothing new is defined; the instance is the
univariate codec at coefficient type `CPolynomial R`, which is what the delimited-codec design
exists for.
-/

@[expose] public section

namespace CompPoly.CBivariate

variable {R : Type*} [Zero R] [BEq R] [LawfulBEq R]

instance [DelimitedCodec R] : DelimitedCodec (CBivariate R) :=
  inferInstanceAs (DelimitedCodec (CPolynomial (CPolynomial R)))

theorem encode_eq [DelimitedCodec R] (p : CBivariate R) :
    DelimitedCodec.encode p = DelimitedCodec.encode (p : CPolynomial (CPolynomial R)) := rfl

end CompPoly.CBivariate
