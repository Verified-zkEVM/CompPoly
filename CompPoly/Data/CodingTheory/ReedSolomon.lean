/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import CompPoly.Univariate.ToPoly.Impl

/-!
# Reed-Solomon Codes

The Reed-Solomon code over a finite field: evaluation domain, message polynomial, and
encoder. Decoders live in their own files.

A Reed-Solomon code is fixed by an evaluation domain `(a₀, ..., aₙ₋₁) ∈ Fⁿ` of distinct
points and a message length `k`. The codeword for a message `(m₀, ..., mₖ₋₁) ∈ Fᵏ` is
`cᵢ = f(aᵢ)` with `f(x) = m₀ + m₁ x + ... + mₖ₋₁ xᵏ⁻¹`. For `1 ≤ k < n ≤ #F` this is an
`(n, k, d)` code of minimum distance `d = n − k + 1`.

## Main definitions

* `Domain`: evaluation domain, an array of distinct points of `F`.
* `messagePoly`, `encode`: the message polynomial of a coefficient vector and the encoder
  evaluating it on the domain.
-/

namespace CompPoly

namespace ReedSolomon

variable {F : Type*}

/-- Evaluation domain: an array of distinct points in `F`. -/
def Domain (F : Type*) := {a : Array F // a.toList.Nodup}

namespace Domain

/-- Block length. -/
abbrev n (D : Domain F) : ℕ := D.val.size

/-- Indexing into the (nodup) domain array is injective on `Fin D.n`. -/
lemma node_injective (D : Domain F) :
    Function.Injective (fun i : Fin D.n => D.val[i]) :=
  fun _ _ hxy => Fin.ext ((List.getElem_inj D.property).mp hxy)

end Domain

/-- Message polynomial `m₀ + m₁ x + ... + mₖ₋₁ xᵏ⁻¹` from a length-`k`
coefficient vector `msg`. -/
def messagePoly [Zero F] [BEq F] [LawfulBEq F]
    {k : ℕ} (msg : Vector F k) : CPolynomial F :=
  ⟨(CPolynomial.Raw.mk msg.toArray).trim,
   CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- `(messagePoly msg).degree < k`. -/
lemma messagePoly_degree_lt [Zero F] [BEq F] [LawfulBEq F] {k : ℕ} (msg : Vector F k) :
    (messagePoly msg).degree < k :=
  CPolynomial.mem_degreeLT_iff_size_le.mpr
    ((CPolynomial.Raw.Trim.size_le_size msg.toArray).trans_eq msg.size_toArray)

/-- `messagePoly` recovers a `CPolynomial` of degree `< k` from its bounded coefficient vector. -/
lemma messagePoly_ofFn_coeff [Semiring F] [BEq F] [LawfulBEq F] (k : ℕ) (f : CPolynomial F)
    (hf : f.degree < k) : messagePoly (Vector.ofFn fun i : Fin k => f.coeff i) = f := by
  rw [CPolynomial.eq_iff_coeff]; intro j
  rw [messagePoly, CPolynomial.coeff, CPolynomial.Raw.Trim.coeff_eq_coeff, CPolynomial.Raw.coeff,
    CPolynomial.Raw.mk, Vector.toArray_ofFn, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split; rfl
  rename_i hjk
  rw [Option.getD_none, CPolynomial.coeff_toPoly, Polynomial.coeff_eq_zero_of_degree_lt
    ((CPolynomial.degree_toPoly f ▸ hf).trans_le (Nat.cast_le.mpr (not_lt.mp hjk)))]

/-- Encode: the message polynomial `messagePoly msg` evaluated at the domain `D`. -/
def encode [Semiring F] [BEq F] [LawfulBEq F]
    (D : Domain F) {k : ℕ} (msg : Vector F k) : Vector F D.n :=
  ⟨D.val.map (messagePoly msg).eval, by simp [Domain.n]⟩

/-- The codeword entry at node `i` is `messagePoly msg` evaluated at `D.val[i]`. -/
lemma encode_get [Semiring F] [BEq F] [LawfulBEq F] (D : Domain F) {k : ℕ}
    (msg : Vector F k) (i : Fin D.n) :
    (encode D msg).get i = (messagePoly msg).eval (D.val[i]) := Array.getElem_map ..

end ReedSolomon

end CompPoly
