/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abraxas1010 (IAOM / Apoth3osis)
-/
module

public import CompPoly.Univariate.ReedSolomon
public import CompPoly.Univariate.NTT.Evaluation

/-!
# NTT Encoding of Reed-Solomon Codewords

Over the evaluation domain induced by a radix-2 NTT domain (the node array
`#[ω⁰, ω¹, …, ω^(n-1)]`, nodup because powers of a primitive `n`-th root below `n` are
pairwise distinct), the forward NTT of a message polynomial's coefficients **is** the
Reed-Solomon encoding: `forwardImpl_eq_encode` ties the `O(n log n)` evaluation path
(`NTT.Forward.forwardImpl`, in natural order) to the definitional encoder
(`ReedSolomon.encode`) exactly, for every message of length at most the domain size.
No padding is required: `messagePoly` trims, so the degree bound `k ≤ D.n` suffices.

`nttCodeword` packages the forward-NTT output as a length-indexed vector over the induced
domain, with `nttCodeword_eq_encode` the packaged form of the equality.

Note the natural-order caveat: `NTTFast.forwardImpl` returns evaluations in bit-reversed
order (`forwardImpl_eq_bitRevPermute_evalOnDomain`), so the fast variant relates to
`encode` only after composing with `bitRevPermute`; this file deliberately uses the
natural-order `NTT.Forward.forwardImpl`.

## Main definitions

* `ReedSolomon.nttDomainToRS`: the Reed-Solomon evaluation domain induced by an NTT domain.
* `ReedSolomon.nttCodeword`: the forward-NTT output as a `Vector F (nttDomainToRS D).n`.

## Main results

* `ReedSolomon.forwardImpl_eq_encode`: the forward NTT of `messagePoly msg` equals
  `encode (nttDomainToRS D) msg`, as arrays.
* `ReedSolomon.nttCodeword_eq_encode`: the packaged (vector-level) form.
-/

@[expose] public section

namespace CompPoly

namespace ReedSolomon

open CPolynomial.NTT

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The Reed-Solomon evaluation domain induced by a radix-2 NTT domain: the node array
`#[ω⁰, ω¹, …, ω^(n-1)]`, nodup because powers of a primitive `n`-th root below `n` are
pairwise distinct. -/
def nttDomainToRS (D : CPolynomial.NTT.Domain F) : ReedSolomon.Domain F :=
  ⟨Array.ofFn (fun i : D.Idx => D.node i), by
    rw [Array.toList_ofFn]
    refine (List.nodup_ofFn).mpr ?_
    intro i j hij
    exact Fin.ext (D.primitive.pow_inj i.isLt j.isLt hij)⟩

omit [BEq F] [LawfulBEq F] in
@[simp] lemma nttDomainToRS_n (D : CPolynomial.NTT.Domain F) :
    (nttDomainToRS D).n = D.n := by
  simp [nttDomainToRS, ReedSolomon.Domain.n]

/-- **The certified NTT encoder**: over the induced evaluation domain, the forward NTT of
the message polynomial's coefficients is exactly the Reed-Solomon encoding — the
`O(n log n)` evaluation path and the definitional encoder agree, with no padding needed. -/
theorem forwardImpl_eq_encode (D : CPolynomial.NTT.Domain F) {k : ℕ} (msg : Vector F k)
    (hk : k ≤ D.n) :
    Forward.forwardImpl D (messagePoly msg).val
      = (encode (nttDomainToRS D) msg).toArray := by
  have hdeg : (messagePoly msg).toPoly.natDegree < D.n := by
    by_cases h0 : (messagePoly msg).toPoly = 0
    · simp [h0, Nat.two_pow_pos D.logN]
    · have h1 : (messagePoly msg).toPoly.degree < (k : WithBot ℕ) := by
        rw [← CPolynomial.degree_toPoly]
        exact_mod_cast messagePoly_degree_lt msg
      exact lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr h1) hk
  rw [Forward.forwardImpl_eq_evalOnDomain D _ hdeg]
  simp only [evalOnDomain, encode, nttDomainToRS, Array.map_ofFn]
  rfl

/-- The forward-NTT output packaged as a length-indexed vector over the induced domain. -/
def nttCodeword (D : CPolynomial.NTT.Domain F) {k : ℕ} (msg : Vector F k) (hk : k ≤ D.n) :
    Vector F (nttDomainToRS D).n :=
  ⟨Forward.forwardImpl D (messagePoly msg).val, by
    rw [forwardImpl_eq_encode D msg hk]; simp⟩

/-- Vector-level form of `forwardImpl_eq_encode`. -/
theorem nttCodeword_eq_encode (D : CPolynomial.NTT.Domain F) {k : ℕ} (msg : Vector F k)
    (hk : k ≤ D.n) : nttCodeword D msg hk = encode (nttDomainToRS D) msg := by
  apply Vector.toArray_inj.mp
  simpa [nttCodeword] using forwardImpl_eq_encode D msg hk

end ReedSolomon

end CompPoly
