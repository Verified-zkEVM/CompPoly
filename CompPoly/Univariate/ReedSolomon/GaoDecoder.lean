/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import CompPoly.Univariate.ReedSolomon
import CompPoly.Univariate.EuclideanAlgorithm
import CompPoly.Univariate.Lagrange

/-!
# Gao Decoder for Reed-Solomon Codes

Gao's decoding algorithm [Gao02] for the Reed-Solomon code of `ReedSolomon.lean`;
correctness is proved in `GaoCorrectness.lean`.

## Main definitions

* `nodalPoly`, `receivedInterpolant`: the decoder's inputs to the partial EEA, the nodal
  polynomial `g₀ = ∏ (x − aᵢ)` and the interpolant `g₁` of the received word.
* `partialGcd`: the partial extended Euclidean algorithm on `(g₀, g₁)` with stopping
  threshold `⌈(n+k)/2⌉`.
* `decode`: the decoder; returns the recovered message polynomial, or `none`.

## References

* [Gao, S., *A New Algorithm for Decoding Reed-Solomon Codes*][Gao02]
-/

namespace CompPoly.ReedSolomon.Gao

variable {F : Type*}

/-- Nodal polynomial of the evaluation domain: `g₀(x) = ∏ a ∈ D, (x − a)`. -/
def nodalPoly [Ring F] [BEq F] [LawfulBEq F] [Nontrivial F] (D : Domain F) : CPolynomial F :=
  D.val.foldl (fun acc a => acc * (CPolynomial.X - CPolynomial.C a)) 1

/-- Unique polynomial `g₁ ∈ 𝔽[X]` of degree < `D.n` such that
`g₁(aᵢ) = r[i]` for `aᵢ ∈ D`. -/
def receivedInterpolant [Field F] [BEq F] [LawfulBEq F]
    (D : Domain F) (r : Vector F D.n) : CPolynomial F :=
  CPolynomial.CLagrange.interpolate Finset.univ (D.val[·]) r.get

/-- Partial extended Euclidean algorithm stopping when the remainder
has degree less than `(n + k + 1)/2 = ⌈(n+k)/2⌉`. -/
def partialGcd [Field F] [BEq F] [LawfulBEq F]
    (k : ℕ) (D : Domain F) (r : Vector F D.n) :
    CPolynomial F × CPolynomial F × CPolynomial F :=
  CPolynomial.xgcd (nodalPoly D) (receivedInterpolant D r) ((D.n + k + 1)/2)

/-- Gao's algorithm.

Apply the partial EEA to the nodal polynomial `g₀` and the interpolant `g₁` of
the received word, stopping at threshold `(n + k + 1)/2`, where `n = D.n` is the
block length and `k` the message length. This yields a triple `(g, u, v)`
satisfying the Bézout identity `g = u * g₀ + v * g₁`, where:
- `g` is the first residue with degree below the threshold
- `v` is the error-locator polynomial (`u` is discarded)

Decoding succeeds when `v` divides `g` and `g / v` has degree below `k`, in
which case the recovered message polynomial is `g / v`.
-/
def decode [Field F] [BEq F] [LawfulBEq F]
    (k : ℕ) (D : Domain F) (r : Vector F D.n) :
    Option (CPolynomial F) :=
  let (g, _, v) := partialGcd k D r
  if g.mod v == 0 then
    let f := g / v
    if f.degree < k then some f else none
  else none

end CompPoly.ReedSolomon.Gao
