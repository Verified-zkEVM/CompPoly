/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitrios Mitsios
-/

import CompPoly.Univariate.Roots.Splitter
import CompPoly.Univariate.Roots.Correctness

/-!
# Cantor–Zassenhaus Linear-Factor Splitting

Executable equal-degree (degree-one) splitter for field-root products over a
finite field of odd cardinality `q`, following the Cantor–Zassenhaus
root-finding method [CZ81]. It plugs into the shared
`LinearFactorProductSplitter` interface alongside the smooth-subgroup splitter.

The generic root pipeline first reduces to a squarefree product of linear
factors `p = ∏ (X - rᵢ)` via `gcd(f, X^q - X)` (see `Roots.RootProduct`); this
module only performs the *separation* of those linear factors.

## Method

For a shift `s : F`, with `w = (X + s)^((q-1)/2) mod p`:

* `gcd(p, X + s)` isolates the root `r = -s` (if present);
* `gcd(p, w - 1)` collects roots `r` with `r + s` a nonzero square;
* `gcd(p, w + 1)` collects roots `r` with `r + s` a non-square.

Iterating over a sequence of shifts separates all roots: for any two distinct
roots, some shift sends them to different quadratic-residue classes. The split
is correct for *every* shift; the shift sequence only governs termination, so no
probabilistic reasoning enters correctness. See `czSound` (proved here) and the
`complete` obligation, supplied to `czLinearFactorProductSplitterOf`.

## References

* [Cantor, D. G., and Zassenhaus, H., *A new algorithm for factoring
    polynomials over finite fields*][CZ81]
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- `(X + s)^exponent mod modulus`, lifted back to canonical polynomials.
The Cantor–Zassenhaus discriminating power, generalising `xPowModWith` to the
shifted base `X + s`. -/
def shiftedPowModWith (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (modulus : CPolynomial F) (s : F) (exponent : Nat) : CPolynomial F :=
  CPolynomial.ofArray
    (CPolynomial.Raw.powModWith M D modulus.val
      (CPolynomial.X + CPolynomial.C s).val exponent)

/-- One Cantor–Zassenhaus refinement against shift `s`: returns the three
sub-factors `(gcd(p, X+s), gcd(p, w-1), gcd(p, w+1))` where `w` is the shifted
discriminating power. Their product is `p` (for squarefree `p` of odd `q`). -/
def czRefine (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (s : F) (p : CPolynomial F) :
    CPolynomial F × CPolynomial F × CPolynomial F :=
  let w := shiftedPowModWith M D p s ((q - 1) / 2)
  let gZero := CPolynomial.monicNormalize (CPolynomial.gcdMonic p (CPolynomial.X + CPolynomial.C s))
  let gRes := CPolynomial.monicNormalize (CPolynomial.gcdMonic p (w - 1))
  let gNon := CPolynomial.monicNormalize (CPolynomial.gcdMonic p (w + 1))
  (gZero, gRes, gNon)

/-- The shift bucket `X + s` is exactly the monic linear factor with root `-s`.
First step of the completeness argument: at shift `s = -a` the `gcd(p, X + s)`
bucket isolates the root `a` directly, with no quadratic-residue reasoning. The
residue buckets `w ± 1` are needed only for fields whose elements are not all
reached by the prime-subfield shift schedule (extension fields). -/
theorem czShift_eq_linearFactor (s : F) :
    (CPolynomial.X + CPolynomial.C s : CPolynomial F) = CPolynomial.linearFactor (-s) := by
  rw [CPolynomial.linearFactor, neg_neg, add_comm]

/-- Evaluating the shift base `X + s` at `a` gives `a + s`. -/
theorem eval_X_add_C (a s : F) :
    CPolynomial.eval a (CPolynomial.X + CPolynomial.C s) = a + s := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- At a root `a` of `p`, the shifted discriminating power evaluates as
`(a + s)^k`. This is the analytic core of the quadratic-residue routing:
`w(a) = (a + s)^((q-1)/2)`. Wraps `raw_eval_powModWith_eq_pow`. -/
theorem eval_shiftedPowModWith (M : CPolynomial.Raw.MulContext F)
    (D : CPolynomial.Raw.ModContext F) (p : CPolynomial F) (s a : F) (k : Nat)
    (hp : CPolynomial.eval a p = 0) :
    CPolynomial.eval a (shiftedPowModWith M D p s k) = (a + s) ^ k := by
  have hmod : (p.val : CPolynomial.Raw F).eval a = 0 := hp
  unfold shiftedPowModWith
  show CPolynomial.Raw.eval a
      (CPolynomial.Raw.powModWith M D p.val (CPolynomial.X + CPolynomial.C s).val k).trim =
      (a + s) ^ k
  rw [CPolynomial.Raw.eval_trim_eq_eval, raw_eval_powModWith_eq_pow M D hmod k]
  change CPolynomial.eval a (CPolynomial.X + CPolynomial.C s) ^ k = (a + s) ^ k
  rw [eval_X_add_C]

/-- Evaluation is additive (the library provides `eval_sub` but not `eval_add`). -/
theorem eval_add (a : F) (p₁ p₂ : CPolynomial F) :
    CPolynomial.eval a (p₁ + p₂) = CPolynomial.eval a p₁ + CPolynomial.eval a p₂ := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

/-- The quotient bucket of `czRefine` is `gcd(p, X + s)`, normalized. -/
theorem czRefine_fst (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (s : F) (p : CPolynomial F) :
    (czRefine M D q s p).1 =
      CPolynomial.monicNormalize (CPolynomial.gcdMonic p (CPolynomial.X + CPolynomial.C s)) :=
  rfl

/-- The quadratic-residue bucket of `czRefine` is `gcd(p, w - 1)`, normalized. -/
theorem czRefine_snd_fst (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (s : F) (p : CPolynomial F) :
    (czRefine M D q s p).2.1 =
      CPolynomial.monicNormalize
        (CPolynomial.gcdMonic p (shiftedPowModWith M D p s ((q - 1) / 2) - 1)) :=
  rfl

/-- The non-residue bucket of `czRefine` is `gcd(p, w + 1)`, normalized. -/
theorem czRefine_snd_snd (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (s : F) (p : CPolynomial F) :
    (czRefine M D q s p).2.2 =
      CPolynomial.monicNormalize
        (CPolynomial.gcdMonic p (shiftedPowModWith M D p s ((q - 1) / 2) + 1)) :=
  rfl

/-- Quadratic-residue routing: for `q` odd and `a + s ≠ 0`, a root `a` of `p` is a
root of one of the two residue buckets `gRes`/`gNon`. Uses Fermat (`a^q = a`) so
that `((a+s)^((q-1)/2))² = 1`, hence the discriminating power is `±1` at `a`. -/
theorem czRefine_root_in_residue_bucket
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (hodd : Odd q) (hfrob : ∀ x : F, x ^ q = x)
    (s a : F) (p : CPolynomial F)
    (hp : CPolynomial.eval a p = 0) (hsa : a + s ≠ 0) :
    CPolynomial.eval a (czRefine M D q s p).2.1 = 0 ∨
      CPolynomial.eval a (czRefine M D q s p).2.2 = 0 := by
  obtain ⟨m, hm⟩ := hodd
  have hwa : CPolynomial.eval a (shiftedPowModWith M D p s ((q - 1) / 2))
      = (a + s) ^ ((q - 1) / 2) :=
    eval_shiftedPowModWith M D p s a ((q - 1) / 2) hp
  have hpow : (a + s) ^ (q - 1) = 1 := by
    have h := hfrob (a + s)
    have hq : q = (q - 1) + 1 := by omega
    rw [hq, pow_succ] at h
    have hcancel : (a + s) ^ (q - 1) * (a + s) = 1 * (a + s) := by simpa using h
    exact mul_right_cancel₀ hsa hcancel
  have ht2 : CPolynomial.eval a (shiftedPowModWith M D p s ((q - 1) / 2))
      * CPolynomial.eval a (shiftedPowModWith M D p s ((q - 1) / 2)) = 1 := by
    rw [hwa, ← pow_add]
    have hsum : (q - 1) / 2 + (q - 1) / 2 = q - 1 := by omega
    rw [hsum, hpow]
  rcases mul_self_eq_one_iff.mp ht2 with ht | ht
  · left
    rw [czRefine_snd_fst]
    refine monicNormalize_root_of_root (gcdMonic_root_of_left_right hp ?_)
    rw [eval_sub, eval_one, ht]; ring
  · right
    rw [czRefine_snd_snd]
    refine monicNormalize_root_of_root (gcdMonic_root_of_left_right hp ?_)
    rw [eval_add, eval_one, ht]; ring

/-- `linearFactor a` maps to the Mathlib monic linear polynomial `X - C a`. -/
theorem linearFactor_toPoly (a : F) :
    (CPolynomial.linearFactor a).toPoly = (Polynomial.X - Polynomial.C a) := by
  rw [CPolynomial.linearFactor, CPolynomial.toPoly_add, CPolynomial.C_toPoly,
    CPolynomial.X_toPoly, Polynomial.C_neg]
  ring

/-- Isolation: at a root `a` of `p`, the monic gcd of `p` with the linear factor
`X - a` is exactly that linear factor. This makes the `s = -a` quotient bucket of
`czRefine` equal to `linearFactor a`, isolating the root. -/
theorem gcdMonic_linearFactor_of_root {p : CPolynomial F} {a : F}
    (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.gcdMonic p (CPolynomial.linearFactor a) = CPolynomial.linearFactor a := by
  classical
  have hisroot : p.toPoly.IsRoot a := by
    rw [Polynomial.IsRoot.def, ← CPolynomial.eval_toPoly]; exact hroot
  have hdvd : (Polynomial.X - Polynomial.C a) ∣ p.toPoly :=
    Polynomial.dvd_iff_isRoot.mpr hisroot
  have hg1 : EuclideanDomain.gcd p.toPoly (Polynomial.X - Polynomial.C a) ∣
      (Polynomial.X - Polynomial.C a) := EuclideanDomain.gcd_dvd_right _ _
  have hg2 : (Polynomial.X - Polynomial.C a) ∣
      EuclideanDomain.gcd p.toPoly (Polynomial.X - Polynomial.C a) :=
    EuclideanDomain.dvd_gcd hdvd dvd_rfl
  have htoPoly : (CPolynomial.gcdMonic p (CPolynomial.linearFactor a)).toPoly =
      (CPolynomial.linearFactor a).toPoly := by
    rw [CPolynomial.gcdMonic_toPoly_eq_normalize_gcd, linearFactor_toPoly,
      normalize_eq_normalize hg1 hg2, (Polynomial.monic_X_sub_C a).normalize_eq_self]
  apply CPolynomial.eq_iff_coeff.mpr
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, htoPoly]

/-- `monicNormalize` fixes the already-monic linear factor `X - a`. -/
theorem monicNormalize_linearFactor (a : F) :
    CPolynomial.monicNormalize (CPolynomial.linearFactor a) = CPolynomial.linearFactor a := by
  classical
  have htoPoly : (CPolynomial.monicNormalize (CPolynomial.linearFactor a)).toPoly =
      (CPolynomial.linearFactor a).toPoly := by
    rw [CPolynomial.monicNormalize_toPoly_eq_normalize, linearFactor_toPoly,
      (Polynomial.monic_X_sub_C a).normalize_eq_self]
  apply CPolynomial.eq_iff_coeff.mpr
  intro i
  rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, htoPoly]

/-- Cantor–Zassenhaus separation driven by an explicit shift schedule
(structural recursion on the schedule).

Emits a factor only when it is recognised as a represented linear factor, so the
output is linear by construction (`czSound`). When the schedule is exhausted on a
still-composite factor, that factor is dropped (defensive): completeness is
therefore conditional on the schedule separating all roots, which is the content
of the `complete` obligation. -/
def czSplitWithShifts (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) : List F → CPolynomial F → Array (CPolynomial F)
  | [], p =>
      let p := CPolynomial.monicNormalize p
      if isRepresentedLinearFactor p then #[p] else #[]
  | s :: rest, p =>
      let p := CPolynomial.monicNormalize p
      if p == 0 || p == 1 then
        #[]
      else if isRepresentedLinearFactor p then
        #[p]
      else
        let (gZero, gRes, gNon) := czRefine M D q s p
        czSplitWithShifts M D q rest gZero ++
          czSplitWithShifts M D q rest gRes ++
            czSplitWithShifts M D q rest gNon

/-- Default shift schedule: `0, 1, …, (count - 1)` cast into `F`. -/
def czDefaultShifts (count : Nat) : List F :=
  (List.range count).map (fun i => (Nat.cast i : F))

/-- Cantor–Zassenhaus linear-factor splitting with naive polynomial arithmetic
contexts and the default shift schedule of length `q`. -/
def czSplitLinearFactors (q : Nat) (p : CPolynomial F) : Array (CPolynomial F) :=
  czSplitWithShifts CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive
    q (czDefaultShifts q) p

/-- Soundness: every factor emitted by the CZ schedule is a linear factor. -/
theorem czSound (q : Nat) (shifts : List F) (p factor : CPolynomial F)
    (h : factor ∈ (czSplitWithShifts CPolynomial.Raw.MulContext.naive
      CPolynomial.Raw.ModContext.naive q shifts p).toList) :
    IsLinearFactor factor := by
  induction shifts generalizing p with
  | nil =>
      rw [czSplitWithShifts] at h
      split at h
      · rename_i hlin
        have hfp : factor = CPolynomial.monicNormalize p := by simpa using h
        subst hfp
        exact isRepresentedLinearFactor_sound hlin
      · simp at h
  | cons s rest ih =>
      rw [czSplitWithShifts] at h
      split at h
      · simp at h
      · split at h
        · rename_i hlin
          have hfp : factor = CPolynomial.monicNormalize p := by simpa using h
          subst hfp
          exact isRepresentedLinearFactor_sound hlin
        · simp only [czRefine, Array.toList_append, List.mem_append] at h
          rcases h with (h | h) | h
          · exact ih _ h
          · exact ih _ h
          · exact ih _ h

/-- A represented linear factor has nonzero degree-one coefficient. -/
theorem represented_coeff_one_ne_zero {q : CPolynomial F}
    (hq : isRepresentedLinearFactor q = true) : CPolynomial.coeff q 1 ≠ 0 := by
  intro h
  rw [isRepresentedLinearFactor, h] at hq
  simp at hq

/-- A represented linear factor is neither `0` nor `1`. -/
theorem represented_zero_one_eq_false {q : CPolynomial F}
    (hq : isRepresentedLinearFactor q = true) : (q == 0 || q == 1) = false := by
  have hc := represented_coeff_one_ne_zero hq
  have h0 : q ≠ 0 := by intro h; exact hc (by rw [h]; exact CPolynomial.coeff_zero 1)
  have h1 : q ≠ 1 := by intro h; apply hc; rw [h]; rfl
  simp [h0, h1]

/-- Base case of completeness: if the (normalized) input is already a represented
linear factor with root `a`, the schedule emits it as a root factor candidate. -/
theorem czSplit_emits (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (q : Nat) (a : F) (shifts : List F) (p : CPolynomial F)
    (hlin : isRepresentedLinearFactor (CPolynomial.monicNormalize p) = true)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor, factor ∈ (czSplitWithShifts M D q shifts p).toList ∧
      IsLinearRootFactorCandidate factor a := by
  refine ⟨CPolynomial.monicNormalize p, ?_, ?_⟩
  · cases shifts with
    | nil => rw [czSplitWithShifts, if_pos hlin]; simp
    | cons s rest =>
        rw [czSplitWithShifts,
          if_neg (by rw [represented_zero_one_eq_false hlin]; simp), if_pos hlin]
        simp
  · exact representedLinearFactor_candidate_of_root hlin (monicNormalize_root_of_root hroot)

/-- Build a `LinearFactorProductSplitter` from the Cantor–Zassenhaus algorithm.

`sound` is discharged by `czSound`. `complete` is left as a parameter: it is the
statement that, under `validInput`, the supplied shift schedule (here the default
of length `q`) separates every root into its own linear factor. The proof rests
on the quadratic-residue separation lemma (for distinct roots some shift splits
them) and termination of the schedule — no probabilistic argument. -/
def czLinearFactorProductSplitterOf
    (validInput : Nat → CPolynomial F → Prop)
    (complete :
      ∀ q p a,
        validInput q p →
          p ≠ 0 →
            CPolynomial.eval a p = 0 →
              ∃ factor,
                factor ∈ (czSplitLinearFactors q p).toList ∧
                  IsLinearRootFactorCandidate factor a) :
    LinearFactorProductSplitter F where
  splitLinearFactors := czSplitLinearFactors
  validInput := validInput
  sound := by
    intro q p factor h
    exact czSound q (czDefaultShifts q) p factor h
  complete := complete

end FiniteField

end Roots

end CPolynomial

end CompPoly
