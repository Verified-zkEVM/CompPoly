/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Conejero
-/
import Mathlib.InformationTheory.Hamming
import CompPoly.Univariate.ReedSolomon.GaoDecoder
import CompPoly.ToMathlib.Polynomial.Roots

/-!
# Gao Decoder Correctness

Correctness of the computable `Gao.decode` decoder from `GaoDecoder.lean`, formalizing
[Gao02, Theorem 3.3]: `decode` succeeds exactly on received words within the decoding
radius `⌊(n − k) / 2⌋` (soundness, failure, completeness, and uniqueness).

## Main results

* `decode_sound`: every success of `Gao.decode` is the message polynomial of a codeword
  within the decoding radius of the received word.
* `decode_eq_none`: if no codeword lies within the decoding radius, `Gao.decode` fails.
* `decode_eq_some`: within the decoding radius, `Gao.decode` recovers the sent message.
* `decode_unique`: the decoded message polynomial is unique within the decoding radius.

## References

* [Gao, S., *A New Algorithm for Decoding Reed-Solomon Codes*][Gao02]
-/

open Polynomial
open CompPoly.CPolynomial hiding X C add_comm zero_add mul_comm mul_zero mul_one one_mul mul_assoc

namespace CompPoly.ReedSolomon.Gao

variable {F : Type*}

/-! ## Uniqueness of degree-bounded Bézout solutions

Two degree-bounded solutions of the Bézout identity cross-multiply
(`bezout_solutions_cross_mul`), so the quotient `G / V` is unique. -/

/-- `deg A + d₀ ≤ deg g₀` and `deg B < d₀` imply `deg (A * B) < deg g₀`. -/
private lemma degree_mul_lt_of_bounds [Semiring F] [NoZeroDivisors F]
    {A B g₀ : F[X]} (hg₀ : g₀ ≠ 0) (d₀ : ℕ)
    (hA : A.degree + d₀ ≤ g₀.degree) (hB : B.degree < d₀) :
    (A * B).degree < g₀.degree := by
  rw [degree_mul]
  obtain rfl | hA0 := eq_or_ne A 0
  · simp only [Polynomial.degree_zero, WithBot.bot_add, bot_lt_iff_ne_bot, ne_eq, degree_eq_bot,
      hg₀, not_false_eq_true]
  · exact (WithBot.add_lt_add_left
      (by simp only [ne_eq, degree_eq_bot, hA0, not_false_eq_true]) hB).trans_le hA

/-- Two degree-bounded Bézout solutions `(U,V,G)`, `(U',V',G')` of `U g₀ + V g₁ = ·`
(with `deg G, deg G' < d₀` and `deg V + d₀, deg V' + d₀ ≤ deg g₀`) cross-multiply:
`V * G' = V' * G`. -/
theorem bezout_solutions_cross_mul [CommRing F] [NoZeroDivisors F]
    (g₀ g₁ G U V G' U' V' : F[X]) (d₀ : ℕ) (hg₀ : g₀ ≠ 0)
    (hBez : U * g₀ + V * g₁ = G) (hBez' : U' * g₀ + V' * g₁ = G')
    (hG : G.degree < d₀) (hG' : G'.degree < d₀)
    (hV : V.degree + d₀ ≤ g₀.degree) (hV' : V'.degree + d₀ ≤ g₀.degree) :
    V * G' = V' * G := by
  have hcross : V' * G - V * G' = (V' * U - V * U') * g₀ := by rw [← hBez, ← hBez']; ring
  have hlt : (V' * G - V * G').degree < g₀.degree :=
    (Polynomial.degree_sub_le _ _).trans_lt (max_lt (degree_mul_lt_of_bounds hg₀ _ hV' hG)
      (degree_mul_lt_of_bounds hg₀ _ hV hG'))
  exact (sub_eq_zero.mp (eq_zero_of_dvd_of_degree_lt ⟨_, hcross.trans (mul_comm _ _)⟩ hlt)).symm

/-! ## Error locators and Hamming distance

A nonzero error locator vanishes on every disagreement node, so its degree bounds the
Hamming distance between the received word and a candidate codeword. -/

/-- If `V * (f₁ - g₁) = U * g₀` and `g₀` vanishes on aᵢ, then `V` vanishes at every
aᵢ where `f₁` and `g₁` disagree. -/
lemma disagreement_subset_error_locator_zeros [CommRing F] [NoZeroDivisors F]
    {ι : Type*} [DecidableEq F] (s : Finset ι) (a : ι → F) (g₀ g₁ U V f₁ : F[X])
    (hroot : ∀ i ∈ s, g₀.eval (a i) = 0) (hlocator : V * (f₁ - g₁) = U * g₀) :
    {i ∈ s | f₁.eval (a i) ≠ g₁.eval (a i)} ⊆ {i ∈ s | V.eval (a i) = 0} :=
  Finset.monotone_filter_right _ fun i hi hne => by
    have hev := congrArg (Polynomial.eval (a i)) hlocator
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, hroot i hi, mul_zero, mul_eq_zero,
      sub_eq_zero] at hev
    exact hev.resolve_right hne

/-- From the Bézout identity `G = U g₀ + V g₁` and `G = f₁ V` (with `V ≠ 0`,
`g₀` rooted on the aᵢ), `f₁` disagrees with `g₁` at at most `V.natDegree` nodes. -/
lemma disagreement_card_le_error_locator_natDegree [CommRing F] [IsDomain F]
    {ι : Type*} [DecidableEq F] (s : Finset ι) (a : ι → F) (hinj : Set.InjOn a s)
    (g₀ g₁ G U V f₁ : F[X]) (hroot : ∀ i ∈ s, g₀.eval (a i) = 0)
    (hbez : G = U * g₀ + V * g₁) (hsucc : G = f₁ * V) (hV : V ≠ 0) :
    {i ∈ s | f₁.eval (a i) ≠ g₁.eval (a i)}.card ≤ V.natDegree :=
  (Finset.card_le_card (disagreement_subset_error_locator_zeros s a _ _ U _ _ hroot
    (by rw [mul_sub, mul_comm V f₁, ← hsucc, hbez]; ring))).trans
    (card_eval_zero_le_natDegree s a hinj _ hV)

/-- From the Bézout identity `G = U g₀ + V g₁` and `G = f₁ V`
(with `V ≠ 0`, `g₀` rooted on the aᵢ), a word `b` with `g₁(aᵢ) = b i` satisfies
`hammingDist b (f₁ ∘ a) ≤ V.natDegree`. -/
lemma hammingDist_le_error_locator_natDegree [CommRing F] [IsDomain F]
    {ι : Type*} [Fintype ι] [DecidableEq F] (a : ι → F)
    (hinj : Function.Injective a)
    (g₀ g₁ G U V f₁ : F[X]) (b : ι → F)
    (hroot : ∀ i, g₀.eval (a i) = 0) (hb : ∀ i, g₁.eval (a i) = b i)
    (hbez : G = U * g₀ + V * g₁) (hsucc : G = f₁ * V) (hV : V ≠ 0) :
    hammingDist b (fun i => f₁.eval (a i)) ≤ V.natDegree := by
  obtain rfl : b = fun i => g₁.eval (a i) := funext fun i => (hb i).symm; rw [hammingDist_comm]
  exact disagreement_card_le_error_locator_natDegree Finset.univ a hinj.injOn _ _ _ _ _ _
    (fun i _ => hroot i) hbez hsucc hV

/-! ## Decoder components meet their specifications

Transports the abstract `Polynomial` results to the implementation along the decoder
pipeline:
the received interpolant interpolates `r`, `nodalPoly = ∏ (X - aᵢ)` is monic of degree
`D.n`, and `partialGcd` meets the Bézout stop spec. -/

section Decoder
variable [BEq F] [LawfulBEq F]

/-- The received interpolant evaluates to `r i` at each domain node. -/
lemma receivedInterpolant_eval_node [Field F] (D : Domain F) (r : Vector F D.n) (i : Fin D.n) :
    (receivedInterpolant D r).toPoly.eval (D.val[i]) = r.get i := by
  rw [receivedInterpolant, CLagrange.cinterpolate_eq_interpolate]
  exact Lagrange.eval_interpolate_at_node _ D.node_injective.injOn (Finset.mem_univ i)

/-- The received interpolant has degree `< D.n`. -/
lemma receivedInterpolant_degree_lt [Field F] (D : Domain F) (r : Vector F D.n) :
    (receivedInterpolant D r).toPoly.degree < D.n := by
  rw [receivedInterpolant, CLagrange.cinterpolate_eq_interpolate]
  simpa using Lagrange.degree_interpolate_lt (s := .univ) r.get D.node_injective.injOn

/-- `(nodalPoly D).toPoly = ∏ i, (X - C D.val[i])`. -/
lemma toPoly_nodalPoly [CommRing F] [Nontrivial F] (D : Domain F) :
    (nodalPoly D).toPoly = ∏ i : Fin D.n, (X - C (D.val[i])) := by
  rw [nodalPoly, ← Array.foldl_toList,
    ← List.foldl_map (f := fun a => CPolynomial.X - CPolynomial.C a) (g := (· * ·)),
    ← List.prod_eq_foldl, ← List.ofFn_getElem (xs := D.val.toList), List.map_ofFn,
    List.prod_ofFn, toPoly_prod]
  simp only [Function.comp_apply, toPoly_sub, X_toPoly, C_toPoly]; rfl

/-- `(nodalPoly D).toPoly.natDegree = D.n`. -/
lemma natDegree_nodalPoly [CommRing F] [NoZeroDivisors F] [Nontrivial F] (D : Domain F) :
    (nodalPoly D).toPoly.natDegree = D.n := by
  rw [toPoly_nodalPoly, Polynomial.natDegree_prod _ _ (fun i _ => X_sub_C_ne_zero _)]
  simp only [Fin.getElem_fin, natDegree_sub_C, natDegree_X, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

/-- `(nodalPoly D).toPoly ≠ 0` (it is monic, a product of distinct linear factors). -/
lemma toPoly_nodalPoly_ne_zero [CommRing F] [Nontrivial F] (D : Domain F) :
    (nodalPoly D).toPoly ≠ 0 := by
  rw [toPoly_nodalPoly]; exact (monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)).ne_zero

/-- `(nodalPoly D).toPoly.degree = D.n`. -/
lemma degree_nodalPoly [CommRing F] [NoZeroDivisors F] [Nontrivial F] (D : Domain F) :
    (nodalPoly D).toPoly.degree = D.n := by
  rw [Polynomial.degree_eq_natDegree (toPoly_nodalPoly_ne_zero D), natDegree_nodalPoly]

/-- `nodalPoly D` vanishes at every domain node. -/
lemma nodalPoly_eval_node_eq_zero [CommRing F] [Nontrivial F] (D : Domain F) (i : Fin D.n) :
    (nodalPoly D).toPoly.eval (D.val[i]) = 0 := by
  rw [toPoly_nodalPoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (by simp only [Fin.getElem_fin, Polynomial.eval_sub, eval_X, Polynomial.eval_C, sub_self])

/-- `partialGcd`'s output satisfies the stop spec for `(nodalPoly D, receivedInterpolant D r)` at
threshold `(D.n + k + 1) / 2`. -/
lemma partialGcd_stopSpec [Field F] (k : ℕ) (D : Domain F) (r : Vector F D.n) (hkn : k < D.n) :
    BezoutStopSpecOf (nodalPoly D) (receivedInterpolant D r) ((D.n + k + 1) / 2)
      (partialGcd k D r) :=
  xgcd_stopSpec _ _ _
    (by simpa only [degree_toPoly, degree_nodalPoly] using receivedInterpolant_degree_lt D r)
    (by omega) (by rw [degree_toPoly, degree_nodalPoly, Nat.cast_le]; omega)

/-! ## Soundness

A decoder success comes from a codeword within the decoding radius `⌊(D.n - k) / 2⌋` of the
received word; `decode_eq_none` is the contrapositive. -/

variable [DecidableEq F]

/-- Soundness over abstract components `G, V, f₁`: given the Bézout identity, `V ≠ 0` with the
error-locator degree bound (`deg V + ⌈(D.n+k)/2⌉ ≤ D.n`), and exact division `G / V = f₁` with
`deg f₁ < k`, then `f₁.toPoly` has degree `< k` and its word of node evaluations `(f₁(aᵢ))ᵢ`
lies within Hamming distance `⌊(D.n-k)/2⌋` of the received word `r`.
(Free variables keep elaboration from unfolding the `xgcd` fold; `decode_sound` supplies the
concrete projections.) -/
private lemma decode_sound_aux [Field F]
    (k : ℕ) (D : Domain F) (r : Vector F D.n)
    (U G V f₁ : CPolynomial F)
    (hbez : G = U * nodalPoly D + V * receivedInterpolant D r)
    (hVne0 : V ≠ 0)
    (hVdeg : V.degree + (↑((D.n + k + 1) / 2) : WithBot ℕ) ≤ D.n)
    (hmod0 : G.mod V = 0) (hdiv : G / V = f₁)
    (hfdeg : f₁.degree < k) :
    f₁.toPoly.degree < k ∧
      hammingDist r.get (fun i => f₁.toPoly.eval (D.val[i])) ≤ (D.n - k) / 2 := by
  have hVtp : V.toPoly ≠ 0 := (toPoly_eq_zero_iff _).not.mpr hVne0
  refine ⟨by rwa [← degree_toPoly], ?_⟩
  have hGV : G.toPoly = f₁.toPoly * V.toPoly :=
    (exactDiv_toPoly_iff _ _ _ hVtp).mpr ⟨hmod0, hdiv ▸ rfl⟩
  have hVnd : V.toPoly.natDegree ≤ (D.n - k) / 2 := by
    rw [degree_toPoly, Polynomial.degree_eq_natDegree hVtp, ← Nat.cast_add,
      Nat.cast_le] at hVdeg; omega
  have hbezP : G.toPoly
      = U.toPoly * (nodalPoly D).toPoly + V.toPoly * (receivedInterpolant D r).toPoly := by
    simp only [hbez, toPoly_add, toPoly_mul]
  exact (hammingDist_le_error_locator_natDegree _ D.node_injective _ _ _ _ _ _ _
    (nodalPoly_eval_node_eq_zero D) (receivedInterpolant_eval_node D r) hbezP hGV hVtp).trans hVnd

/-- Soundness: any success of `Gao.decode` returns `messagePoly msg` for
some `msg` whose codeword is within the decoding radius `⌊(D.n-k)/2⌋ = (d-1)/2` of `r`. -/
theorem decode_sound [Field F]
    (k : ℕ) (D : Domain F) (r : Vector F D.n) (hkn : k < D.n)
    (f₁ : CPolynomial F) (h : Gao.decode k D r = some f₁) :
    ∃ msg : Vector F k, messagePoly msg = f₁ ∧
      hammingDist r.get (encode D msg).get ≤ (D.n - k) / 2 := by
  obtain ⟨hbez, -, hVdeg, hVne0⟩ := partialGcd_stopSpec _ _ r hkn
  simp only [Gao.decode] at h
  set p := partialGcd k D r; set G := p.1; set U := p.2.1; set V := p.2.2
  replace hVne0 := (toPoly_eq_zero_iff _).not.mp hVne0
  rw [degree_nodalPoly, ← degree_toPoly] at hVdeg
  have hbezC : G = U * nodalPoly D + V * receivedInterpolant D r := by
    rw [← sub_eq_zero, ← toPoly_eq_zero_iff, toPoly_sub, toPoly_add, toPoly_mul, toPoly_mul,
      hbez, sub_self]
  split_ifs at h with hmod hfdeg
  have hdiv : G / V = f₁ := Option.some.inj h; have hfdeg' : f₁.degree < k := hdiv ▸ hfdeg
  have hdist := (decode_sound_aux _ _ _ _ _ _ _ hbezC hVne0 hVdeg (eq_of_beq hmod) hdiv hfdeg').2
  refine ⟨_, messagePoly_ofFn_coeff _ _ hfdeg', ?_⟩
  have hcw : (encode D (Vector.ofFn fun i : Fin k => f₁.coeff i)).get
      = fun i => f₁.toPoly.eval (D.val[i]) := by
    funext i; rw [encode_get, messagePoly_ofFn_coeff _ _ hfdeg', eval_toPoly]
  rwa [hcw]

/-- Failure: if `r` is beyond the decoding radius `⌊(D.n-k)/2⌋` of every message,
`Gao.decode` returns `none` (contrapositive of soundness). -/
theorem decode_eq_none [Field F]
    (k : ℕ) (D : Domain F) (r : Vector F D.n) (hkn : k < D.n)
    (h : ∀ msg : Vector F k,
      (D.n - k) / 2 < hammingDist r.get (encode D msg).get) :
    Gao.decode k D r = none := by
  rcases hgao : Gao.decode k D r with _ | f₁; rfl
  obtain ⟨msg, -, hle⟩ := decode_sound _ _ _ hkn _ hgao; exact absurd hle (h msg).not_ge

/-! ## Completeness and uniqueness

Within the guaranteed-decoding radius `⌊(D.n-k)/2⌋` the decoder returns exactly
`messagePoly msg`, and that decoded word is unique (`decode_unique`). -/

/-- Completeness: if `r` is within the guaranteed-decoding radius `⌊(D.n-k)/2⌋`
(`2 * (error count) ≤ D.n - k`) of `encode D msg`, then `Gao.decode` returns `messagePoly msg`. -/
theorem decode_eq_some [Field F]
    (k : ℕ) (D : Domain F) (r : Vector F D.n) (hkn : k < D.n)
    (msg : Vector F k)
    (herr : 2 * hammingDist r.get (encode D msg).get ≤ D.n - k) :
    Gao.decode k D r = some (messagePoly msg) := by
  -- Define the set of error positions.
  simp only [hammingDist] at herr
  set E := Finset.univ.filter (fun i : Fin D.n => r.get i ≠ (encode D msg).get i) with hEdef
  -- The error locator polynomial forms a Bézout solution.
  have hagree : ∀ i ∈ Finset.univ \ E,
      (messagePoly msg).toPoly.eval (D.val[i])
        = (receivedInterpolant D r).toPoly.eval (D.val[i]) := by
    intro i hi; have hi' : r.get i = (encode D msg).get i := by simpa [hEdef] using hi
    rw [← eval_toPoly, ← encode_get, ← hi', ← receivedInterpolant_eval_node]
  have hdvd :=
    prod_X_sub_C_dvd_prod_mul_sub _ _ (Finset.subset_univ E) _ D.node_injective.injOn _ _ hagree
  have hwne : (∏ i ∈ E, (X - C (D.val[i]))) ≠ 0 :=
    (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _).ne_zero
  have hwdeg : (∏ i ∈ E, (X - C (D.val[i]))).degree = (E.card : WithBot ℕ) :=
    natDegree_finsetProd_X_sub_C_eq_card E (fun i => D.val[i]) ▸ Polynomial.degree_eq_natDegree hwne
  set w := ∏ i ∈ E, (X - C (D.val[i]))
  obtain ⟨U', hU'⟩ :
      (nodalPoly D).toPoly ∣ w * ((messagePoly msg).toPoly - (receivedInterpolant D r).toPoly) :=
    toPoly_nodalPoly D ▸ hdvd
  have hBez' : U' * (nodalPoly D).toPoly + w * (receivedInterpolant D r).toPoly
      = w * (messagePoly msg).toPoly := by rw [mul_comm U', ← hU']; ring
  -- The relation between two Bézout solutions pins the original message.
  obtain ⟨hbez, hstop, hVdeg, hVne0⟩ := partialGcd_stopSpec _ _ r hkn
  set p := partialGcd k D r; set G := p.1; set U := p.2.1; set V := p.2.2
  have hGdeg : G.toPoly.degree < ((D.n + k + 1) / 2 : ℕ) :=
    Polynomial.degree_le_natDegree.trans_lt (mod_cast hstop)
  have hG'deg : (w * (messagePoly msg).toPoly).degree < ((D.n + k + 1) / 2 : ℕ) := by
    rw [degree_mul, hwdeg]
    exact (WithBot.add_lt_add_left (by simp only [ne_eq, WithBot.natCast_ne_bot, not_false_eq_true])
      (degree_toPoly (messagePoly msg) ▸ messagePoly_degree_lt msg)).trans_le (mod_cast by omega)
  have hV'deg : w.degree + ((D.n + k + 1) / 2 : ℕ) ≤ (nodalPoly D).toPoly.degree := by
    rw [hwdeg, degree_nodalPoly]; exact mod_cast by omega
  have hcross := bezout_solutions_cross_mul _ _ _ _ _ _ _ _ _ (toPoly_nodalPoly_ne_zero D)
    hbez.symm hBez' hGdeg hG'deg hVdeg hV'deg
  have hGVf : G.toPoly = V.toPoly * (messagePoly msg).toPoly :=
    mul_left_cancel₀ hwne (by rw [← hcross]; ring)
  -- Extract the message from the exact-division equation `hGVf`.
  obtain ⟨hmod0, hdivtp⟩ :=
    (exactDiv_toPoly_iff _ _ _ hVne0).mp (hGVf.trans (mul_comm _ _))
  have hdiveq : G / V = messagePoly msg := toPolyLinearEquiv.injective hdivtp
  show (if G.mod V == 0 then if (G / V).degree < k then some (G / V) else none else none) = _
  rw [if_pos (beq_iff_eq.mpr hmod0), if_pos (hdiveq ▸ messagePoly_degree_lt msg), hdiveq]

/-- Uniqueness: within the guaranteed-decoding radius `⌊(D.n-k)/2⌋`, two messages
whose codewords lie within that radius of `r` decode to the same polynomial. -/
theorem decode_unique [Field F] (k : ℕ) (D : Domain F) (r : Vector F D.n)
    (hkn : k < D.n) (msg₁ msg₂ : Vector F k)
    (h₁ : 2 * hammingDist r.get (encode D msg₁).get ≤ D.n - k)
    (h₂ : 2 * hammingDist r.get (encode D msg₂).get ≤ D.n - k) :
    messagePoly msg₁ = messagePoly msg₂ :=
  Option.some.inj <|
    (decode_eq_some k D r hkn msg₁ h₁).symm.trans (decode_eq_some k D r hkn msg₂ h₂)

end Decoder

end CompPoly.ReedSolomon.Gao
