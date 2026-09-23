/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.ToPoly.Core
public import CompPoly.Univariate.NTT.Barycentric
public import CompPoly.Univariate.NTTFast.Interpolation
public import CompPoly.Univariate.ReedSolomon.GaoCorrectness
public import CompPoly.Univariate.ReedSolomon.NTTEncode
public import CompPoly.Univariate.ToPoly.RingHom

/-!
# Gao Decoding on an NTT Domain

`Gao.decode` builds its two Euclidean inputs by definition: the nodal polynomial as a fold of
`n` linear factors, and the received interpolant by Lagrange's formula, `O(n²)` per basis
polynomial. On the evaluation domain of a radix-2 NTT domain both have fast forms. The nodal
polynomial is `Xⁿ - 1` (`NTT.Domain.nodal_eq_X_pow_sub_one`), and the interpolant is the
inverse NTT (`NTT.interpolate`). `decodeNTT` uses both, and `decodeNTT_eq_decode` proves it
equal to `decode`, so every correctness theorem of `GaoCorrectness.lean` transfers unchanged.

## Main definitions

* `Gao.decodeFrom`: the Euclidean stage of `decode` on given inputs `(g₀, g₁)`.
* `Gao.vanishingNTT`: the polynomial `Xⁿ - 1` of an NTT domain.
* `Gao.decodeNTT`, `Gao.decodePlan`: `decode` with the fast inputs, unplanned and planned.

## Main results

* `Gao.nodalPoly_nttDomainToRS`: the nodal polynomial of the induced domain is `Xⁿ - 1`.
* `Gao.receivedInterpolant_nttDomainToRS`: the received interpolant is the inverse NTT.
* `Gao.decodeNTT_eq_decode`, `Gao.decodePlan_eq_decode`: the fast decoders are `decode`.
-/

@[expose] public section

namespace CompPoly.ReedSolomon.Gao

open CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The Euclidean stage of Gao's decoder on the inputs `(g₀, g₁)`, for block length `n`. -/
def decodeFrom (k n : ℕ) (g₀ g₁ : CPolynomial F) : Option (CPolynomial F) :=
  let (g, _, v) := CPolynomial.xgcd g₀ g₁ ((n + k + 1) / 2)
  if g.mod v == 0 then
    let f := g / v
    if f.degree < k then some f else none
  else none

/-- `decode` is its Euclidean stage applied to the nodal polynomial and the interpolant. -/
theorem decode_eq_decodeFrom (k : ℕ) (D : Domain F) (r : Vector F D.n) :
    decode k D r = decodeFrom k D.n (nodalPoly D) (receivedInterpolant D r) :=
  rfl

/-- The coefficient array `#[-1, 0, …, 0, 1]` of `Xⁿ - 1`, for `n ≥ 1`. -/
def vanishingRaw (n : ℕ) : CPolynomial.Raw F :=
  Array.ofFn fun i : Fin (n + 1) => if (i : ℕ) = n then 1 else if (i : ℕ) = 0 then -1 else 0

/-- The vanishing polynomial `Xⁿ - 1` of an NTT domain, written down coefficient by
coefficient rather than multiplied out of `n` linear factors. -/
def vanishingNTT (D : NTT.Domain F) : CPolynomial F :=
  let raw := vanishingRaw (F := F) D.n
  ⟨raw.trim, CPolynomial.Raw.Trim.isCanonical_trim raw⟩

theorem toPoly_vanishingNTT (D : NTT.Domain F) :
    (vanishingNTT D).toPoly = Polynomial.X ^ D.n - 1 := by
  change (CPolynomial.Raw.trim (vanishingRaw (F := F) D.n)).toPoly = _
  rw [CPolynomial.Raw.toPoly_trim]
  ext i
  rw [CPolynomial.Raw.coeff_toPoly, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_one]
  have hn := D.n_pos
  simp only [CPolynomial.Raw.coeff, vanishingRaw]
  rw [Array.getD_eq_getD_getElem?]
  by_cases hi : i < D.n + 1
  · rw [Array.getElem?_ofFn, dite_eq_left hi]
    simp only [Option.getD_some]
    split_ifs <;> first | omega | simp_all
  · rw [Array.getElem?_ofFn, dite_eq_right hi]
    simp only [Option.getD_none]
    split_ifs <;> first | omega | simp_all

/-- Transport a received word over the NTT domain to the induced Reed-Solomon domain. -/
def castToRS (D : NTT.Domain F) (r : Vector F D.n) : Vector F (nttDomainToRS D).n :=
  r.cast (nttDomainToRS_n D).symm

omit [BEq F] [LawfulBEq F] in
private theorem nttDomainToRS_getElem (D : NTT.Domain F) (i : Fin (nttDomainToRS D).n) :
    (nttDomainToRS D).val[i] = D.node (Fin.cast (nttDomainToRS_n D) i) := by
  show (nttDomainToRS D).val[i.1] = _
  simp [nttDomainToRS]
  rfl

/-- The nodal polynomial of the Reed-Solomon domain induced by an NTT domain is `Xⁿ - 1`. -/
theorem nodalPoly_nttDomainToRS (D : NTT.Domain F) :
    nodalPoly (nttDomainToRS D) = vanishingNTT D := by
  apply CPolynomial.toPoly_injective
  rw [toPoly_vanishingNTT, ← NTT.Domain.nodal_eq_X_pow_sub_one, Lagrange.nodal, toPoly_nodalPoly,
    ← Fin.prod_congr' (fun i : Fin D.n => Polynomial.X - Polynomial.C (D.node i))
      (nttDomainToRS_n D)]
  exact Finset.prod_congr rfl fun i _ => by rw [nttDomainToRS_getElem]

/-- The received interpolant on the induced domain is the inverse NTT of the word. -/
theorem receivedInterpolant_nttDomainToRS (D : NTT.Domain F) (r : Vector F D.n) :
    receivedInterpolant (nttDomainToRS D) (castToRS D r) = NTT.interpolate D r := by
  apply CPolynomial.toPoly_injective
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := Finset.univ) (v := D.node)
    D.node_injective.injOn ?_ ?_ ?_
  · have h := receivedInterpolant_degree_lt (nttDomainToRS D) (castToRS D r)
    simpa using h
  · rw [NTT.interpolate_eq_interpolatePow, CLagrange.interpolatePow,
      CLagrange.cinterpolate_eq_interpolate]
    exact Lagrange.degree_interpolate_lt _ D.node_injective.injOn
  · intro k _
    have h := receivedInterpolant_eval_node (nttDomainToRS D) (castToRS D r)
      (Fin.cast (nttDomainToRS_n D).symm k)
    rw [nttDomainToRS_getElem] at h
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h
    rw [h, ← CPolynomial.eval_toPoly, NTT.eval_interpolate_node]
    simp [castToRS, Vector.get]
    rfl

/-- Gao's decoder on an NTT domain, with `Xⁿ - 1` as the nodal polynomial and the inverse
NTT as the interpolant. -/
def decodeNTT (k : ℕ) (D : NTT.Domain F) (r : Vector F D.n) :
    Option (CPolynomial F) :=
  decodeFrom k D.n (vanishingNTT D) (NTT.interpolate D r)

/-- The NTT decoder is Gao's decoder on the induced Reed-Solomon domain. -/
theorem decodeNTT_eq_decode (k : ℕ) (D : NTT.Domain F) (r : Vector F D.n) :
    decodeNTT k D r = decode k (nttDomainToRS D) (castToRS D r) := by
  rw [decode_eq_decodeFrom, nodalPoly_nttDomainToRS, receivedInterpolant_nttDomainToRS,
    nttDomainToRS_n]
  rfl

/-- Gao's decoder through a reusable NTT plan. -/
def decodePlan (k : ℕ) (P : NTTFast.Plan F) (r : Vector F P.domain.n) :
    Option (CPolynomial F) :=
  decodeFrom k P.domain.n (vanishingNTT P.domain) (NTTFast.Plan.interpolate P r)

/-- A well-formed plan decodes as Gao's decoder on the induced Reed-Solomon domain. -/
theorem decodePlan_eq_decode (k : ℕ) (P : NTTFast.Plan F)
    (hP : NTTFast.Plan.WellFormed P) (r : Vector F P.domain.n) :
    decodePlan k P r = decode k (nttDomainToRS P.domain) (castToRS P.domain r) := by
  rw [← decodeNTT_eq_decode, decodePlan, NTTFast.Plan.interpolate_eq_ntt_interpolate P hP]
  rfl

end CompPoly.ReedSolomon.Gao
