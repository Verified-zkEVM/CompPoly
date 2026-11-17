/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Multilinear.Basic
public import CompPoly.Data.Bytes.Vector

/-!
# Serialization of multilinear polynomials

`CMlPolynomial R n` and `CMlPolynomialEval R n` are `Vector R (2 ^ n)`, so they serialize
through the vector codec with no further definitions: `2 ^ n` coefficients, or `2 ^ n`
hypercube evaluations, in little-endian index order, `2 ^ n * width R` bytes. The two
representations have the same bytes for different meanings; the type says which.
-/

@[expose] public section

namespace CompPoly

variable {R : Type*} {n : ℕ}

theorem CMlPolynomial.width [ByteCodec R] :
    ByteCodec.width (CMlPolynomial R n) = 2 ^ n * ByteCodec.width R := rfl

theorem CMlPolynomialEval.width [ByteCodec R] :
    ByteCodec.width (CMlPolynomialEval R n) = 2 ^ n * ByteCodec.width R := rfl

theorem CMlPolynomial.toBytes_eq [ByteCodec R] (p : CMlPolynomial R n) :
    ByteCodec.toBytes p = ByteCodec.toBytes (p : Vector R (2 ^ n)) := rfl

end CompPoly
