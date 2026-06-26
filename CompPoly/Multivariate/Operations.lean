/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen, Dimitris Mitsios
-/
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Multivariate.MvPolyEquiv.Instances

/-!
# Computable multivariate polynomials (extended operations)

Operations on `CMvPolynomial` that depend on ring instances from `MvPolyEquiv.lean`,
such as monomial orders, leading terms, restriction, variable renaming, and substitution.

The core type and basic operations (`CMvPolynomial`, `C`, `X`, `coeff`, `eval`, etc.)
are in `CMvPolynomial.lean`. The `CommSemiring` and `CommRing` instances are in
`MvPolyEquiv.lean`.

## Main definitions

* `MonomialOrder`: Typeclass for comparing monomials.
* `leadingMonomial`, `leadingCoeff`, `leadingTerm`: Leading term operations
  according to a monomial order.
* `rename`: Rename variables using a function `σ → τ`.
* `aeval`: Algebra evaluation.
* `bind₁`: Substitution of polynomials for variables.
-/
namespace CPoly

open Std

variable {R : Type*}

namespace CMvPolynomial

/-! ## Leading-term operations -/

/-- Monomial ordering typeclass for variables `σ`.

  Provides a way to compare monomials for determining leading terms.
-/
class MonomialOrder (σ : Type*) [FinEnum σ] where
  compare : CMvMonomial σ → CMvMonomial σ → Ordering
  -- TODO: Add ordering axioms (transitivity, etc.)

/-- Baseline degree of a monomial.

  Currently this is the ordinary total degree and is independent of
  `MonomialOrder.compare`.
-/
def MonomialOrder.degree {σ : Type*} [FinEnum σ] (m : CMvMonomial σ) : ℕ :=
  m.totalDegree

/-- Leading monomial of a polynomial according to a monomial order.

  Returns `none` for the zero polynomial.
-/
def leadingMonomial {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [MonomialOrder σ]
    (p : CMvPolynomial σ R) : Option (CMvMonomial σ) :=
  ExtTreeMap.foldl
    (fun acc m _ =>
      match acc with
      | none => some m
      | some m' =>
          match MonomialOrder.compare m m' with
          | .gt => some m
          | _ => some m')
    none p.1

/-- Leading term of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial, and otherwise returns the monomial with
  leading monomial and leading coefficient.
-/
def leadingTerm {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder σ]
    (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  match leadingMonomial p with
  | none => 0
  | some m => monomial m (coeff m p)

/-- Leading coefficient of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial.
-/
def leadingCoeff {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [MonomialOrder σ]
    (p : CMvPolynomial σ R) : R :=
  match leadingMonomial p with
  | none => 0
  | some m => coeff m p

@[simp] lemma leadingCoeff_eq_zero_of_leadingMonomial_eq_none
    {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [MonomialOrder σ] {p : CMvPolynomial σ R}
    (h : leadingMonomial p = none) : leadingCoeff p = 0 := by
  simp [leadingCoeff, h]

lemma leadingCoeff_eq_coeff_of_leadingMonomial_eq_some
    {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [MonomialOrder σ] {p : CMvPolynomial σ R}
    {m : CMvMonomial σ} (h : leadingMonomial p = some m) : leadingCoeff p = coeff m p := by
  simp [leadingCoeff, h]

/-- Packaged form of `leadingCoeff`: it is the coefficient at the optional leading monomial,
defaulting to `0` when no leading monomial exists. -/
lemma leadingCoeff_eq_coeff_leadingMonomial
    {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [MonomialOrder σ] (p : CMvPolynomial σ R) :
    leadingCoeff p = (leadingMonomial p).elim 0 (fun m => coeff m p) := by
  grind [leadingCoeff]

@[simp] lemma leadingTerm_eq_zero_of_leadingMonomial_eq_none
    {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder σ]
    {p : CMvPolynomial σ R} (h : leadingMonomial p = none) :
    leadingTerm p = 0 := by
  grind [leadingTerm]

@[simp] lemma leadingTerm_eq_monomial_of_leadingMonomial_eq_some
    {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder σ]
    {p : CMvPolynomial σ R} {m : CMvMonomial σ} (h : leadingMonomial p = some m) :
    leadingTerm p = monomial m (coeff m p) := by
  grind [leadingTerm]

/-! ## Evaluation and substitution -/

/-- Algebra evaluation: evaluates polynomial in an algebra.

  Given an algebra `S` over `R` and a function `f : σ → S`, evaluates the polynomial.
-/
def aeval {σ : Type*} [FinEnum σ] {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : σ → S) (p : CMvPolynomial σ R) : S :=
  eval₂ (algebraMap R S) f p

@[simp] lemma aeval_eq_eval₂ {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : σ → S) (p : CMvPolynomial σ R) :
    aeval f p = eval₂ (algebraMap R S) f p := rfl

@[simp] lemma aeval_C {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) (c : R) :
    aeval f (CMvPolynomial.C (σ := σ) c) = algebraMap R S c := by
  unfold aeval
  rw [eval₂_equiv (p := CMvPolynomial.C (σ := σ) c) (f := algebraMap R S) (vals := f)]
  simp [CMvPolynomial.fromCMvPolynomial_C]

@[simp] lemma aeval_add {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) (p q : CMvPolynomial σ R) :
    aeval f (p + q) = aeval f p + aeval f q := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_add p q

@[simp] lemma aeval_mul {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) (p q : CMvPolynomial σ R) :
    aeval f (p * q) = aeval f p * aeval f q := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_mul p q

@[simp] lemma aeval_zero {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) :
    aeval f (0 : CMvPolynomial σ R) = 0 := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_zero

@[simp] lemma aeval_one {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) :
    aeval f (1 : CMvPolynomial σ R) = 1 := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_one

@[simp] lemma aeval_pow {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) (p : CMvPolynomial σ R) (k : ℕ) :
    aeval f (p ^ k) = (aeval f p) ^ k := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_pow p k

@[simp] lemma aeval_neg {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommRing R] [BEq R] [LawfulBEq R]
    [CommRing S] [Algebra R S]
    (f : σ → S) (p : CMvPolynomial σ R) :
    aeval f (-p) = -(aeval f p) := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_neg p

@[simp] lemma aeval_sub {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommRing R] [BEq R] [LawfulBEq R]
    [CommRing S] [Algebra R S]
    (f : σ → S) (p q : CMvPolynomial σ R) :
    aeval f (p - q) = aeval f p - aeval f q := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := S) (algebraMap R S) f).map_sub p q

/-- Substitution: substitutes polynomials for variables.

  Given `f : σ → CMvPolynomial τ R`, substitutes `f i` for variable `X i`.
-/
def bind₁ {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (p : CMvPolynomial σ R) : CMvPolynomial τ R :=
  ExtTreeMap.foldl
    (fun acc mono c => CMvPolynomial.C (σ := τ) c * MonoR.evalMonomial f mono + acc)
    0 p.1

/-- The computable substitution `bind₁` agrees with algebraic evaluation. -/
lemma bind₁_eq_aeval {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (p : CMvPolynomial σ R) :
    bind₁ f p = aeval (S := CMvPolynomial τ R) f p := by
  have hmap : ∀ c : R,
      (algebraMap R (CMvPolynomial τ R)) c = CMvPolynomial.C (σ := τ) c := by
    intro c
    rfl
  unfold bind₁ aeval CMvPolynomial.eval₂
  simp [hmap]

@[simp] lemma bind₁_C {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (c : R) :
    bind₁ f (CMvPolynomial.C (σ := σ) c) = CMvPolynomial.C (σ := τ) c := by
  rw [bind₁_eq_aeval]
  simpa using (aeval_C (σ := σ) (R := R) (S := CMvPolynomial τ R) f c)

@[simp] lemma bind₁_add {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (p q : CMvPolynomial σ R) :
    bind₁ f (p + q) = bind₁ f p + bind₁ f q := by
  repeat rw [bind₁_eq_aeval]
  simpa using (aeval_add (σ := σ) (R := R) (S := CMvPolynomial τ R) f p q)

@[simp] lemma bind₁_mul {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (p q : CMvPolynomial σ R) :
    bind₁ f (p * q) = bind₁ f p * bind₁ f q := by
  repeat rw [bind₁_eq_aeval]
  simpa using (aeval_mul (σ := σ) (R := R) (S := CMvPolynomial τ R) f p q)

/-! ## Core operations -/

/-- Rename variables using a function.

  Given `f : σ → τ`, renames variable `X i` to `X (f i)`.
-/
def rename {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*} [Zero R] [Add R] [BEq R] [LawfulBEq R]
    (f : σ → τ) (p : CMvPolynomial σ R) : CMvPolynomial τ R :=
  let renameMonomial (mono : CMvMonomial σ) : CMvMonomial τ :=
    Vector.ofFn (fun k => (Finset.univ.filter (fun i : σ => FinEnum.equiv (f i) = k)).sum
      (fun i => mono.get (FinEnum.equiv i)))
  ExtTreeMap.foldl (fun acc mono c => acc + monomial (renameMonomial mono) c) 0 p.1

-- `renameEquiv` is defined in `CompPoly.Multivariate.Rename`

/-- Embed the variables of a polynomial into a larger variable type along an
injection `f : σ ↪ τ`. This is the disjoint-sum-friendly replacement for the old
numeric `extend`/`polyCoe` machinery. The caller supplies the embedding explicitly,
so there is no hidden assumption about how the variable sets are combined.

We deliberately do *not* provide mixed-arity `HAdd`/`HMul`/`HSub` instances that
silently combine `CMvPolynomial σ R` and `CMvPolynomial τ R` into
`CMvPolynomial (σ ⊕ τ) R`: the order in which the two variable sets are joined is a
convention the caller should make explicit (e.g. via `rename`/`embedDomain`) rather
than have baked into instance resolution. -/
def embedDomain {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*}
    [Zero R] [Add R] [BEq R] [LawfulBEq R]
    (f : σ ↪ τ) (p : CMvPolynomial σ R) : CMvPolynomial τ R :=
  rename f p

/-- Iterative reconstruction of a polynomial by folding over terms. -/
def sumToIter {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] [Add R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  ExtTreeMap.foldl (fun acc m c => acc + monomial m c) 0 p.1

/-! ## Bridge and transport lemmas (technical) -/

lemma X_eq_monomial {σ : Type*} [FinEnum σ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (i : σ) :
    CMvPolynomial.X (R := R) i = CMvPolynomial.monomial
      (Vector.ofFn (fun j => if j = FinEnum.equiv i then 1 else 0))
      (1 : R) := by
  unfold CMvPolynomial.X CMvPolynomial.monomial
  by_cases h : (1 : R) = 0
  · ext m; unfold CMvPolynomial.coeff Lawful.fromUnlawful
    erw [Unlawful.filter_get]; simp [h]; grind
  · simp only [show ((1 : R) == 0) = false from by simp [h]]
    exact (if_neg (by decide)).symm

lemma toFinsupp_unitMono {σ : Type*} [FinEnum σ]
    (i : σ) :
    CMvMonomial.toFinsupp
      (Vector.ofFn (fun j : Fin (FinEnum.card σ) =>
        if j = FinEnum.equiv i then 1 else 0)) =
    Finsupp.single i 1 := by
  ext j
  simp only [CMvMonomial.toFinsupp, Finsupp.coe_mk, Finsupp.single_apply]
  rw [Vector.get_ofFn]
  simp only [EmbeddingLike.apply_eq_iff_eq, eq_comm]

lemma fromCMvPolynomial_monomial {σ : Type*} [FinEnum σ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (mono : CMvMonomial σ) (c : R) :
    fromCMvPolynomial (CMvPolynomial.monomial mono c) =
    MvPolynomial.monomial (CMvMonomial.toFinsupp mono) c := by
  by_cases hc : c = 0
  · subst hc; simp [CMvPolynomial.monomial, map_zero]
  · ext μ
    rw [coeff_eq, MvPolynomial.coeff_monomial]
    unfold CMvPolynomial.coeff CMvPolynomial.monomial
    simp only [show (c == (0 : R)) = false from by simp [hc]]
    unfold Lawful.fromUnlawful
    erw [Unlawful.filter_get]
    simp only [Unlawful.ofList]
    by_cases hm : CMvMonomial.toFinsupp mono = μ
    · subst hm; rw [if_pos rfl, CMvMonomial.ofFinsupp_toFinsupp]
      erw [ExtTreeMap.getElem?_ofList_of_mem
        (k := mono) (k_eq := compare_self) (v := c)
        (mem := by simp) (distinct := ?distinct)]
      · simp
      case distinct => simp
    · rw [if_neg hm]
      have hne : CMvMonomial.ofFinsupp μ ≠ mono :=
        fun h => hm (h ▸ CMvMonomial.toFinsupp_ofFinsupp)
      erw [ExtTreeMap.getElem?_ofList_of_contains_eq_false
        (by simp [hne])]
      rfl

lemma fromCMvPolynomial_X {σ : Type*} [FinEnum σ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (i : σ) :
    fromCMvPolynomial (CMvPolynomial.X (R := R) i) =
    MvPolynomial.X i := by
  rw [X_eq_monomial, fromCMvPolynomial_monomial, toFinsupp_unitMono]
  rfl

@[simp] lemma aeval_X {σ : Type*} [FinEnum σ] {R S : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring S] [Algebra R S]
    (f : σ → S) (i : σ) :
    aeval f (CMvPolynomial.X (R := R) i) = f i := by
  unfold aeval
  rw [eval₂_equiv (p := CMvPolynomial.X (R := R) i) (f := algebraMap R S) (vals := f)]
  simp [fromCMvPolynomial_X]

@[simp] lemma bind₁_X {σ τ : Type*} [FinEnum σ] [FinEnum τ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (i : σ) :
    bind₁ f (CMvPolynomial.X (R := R) i) = f i := by
  rw [bind₁_eq_aeval]
  simpa using (aeval_X (σ := σ) (R := R) (S := CMvPolynomial τ R) f i)

@[simp] lemma bind₁_id {σ : Type*} [FinEnum σ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial σ R) :
    bind₁ (fun i => CMvPolynomial.X (R := R) i) p = p := by
  rw [bind₁_eq_aeval]
  unfold aeval
  apply (CPoly.polyRingEquiv (σ := σ) (R := R)).injective
  rw [eval₂_equiv (p := p) (f := algebraMap R (CMvPolynomial σ R))
    (vals := fun i => CMvPolynomial.X (R := R) i)]
  have hmap := MvPolynomial.map_eval₂Hom
    (f := algebraMap R (CMvPolynomial σ R))
    (g := fun i => CMvPolynomial.X (R := R) i)
    (φ := (CPoly.polyRingEquiv (σ := σ) (R := R)).toRingHom)
    (p := fromCMvPolynomial p)
  have hcomp :
      ((CPoly.polyRingEquiv (σ := σ) (R := R)).toRingHom).comp
        (algebraMap R (CMvPolynomial σ R)) = MvPolynomial.C := by
    ext r m
    rw [RingHom.comp_apply]
    rw [show (algebraMap R (CMvPolynomial σ R)) r = CMvPolynomial.C (σ := σ) r from rfl]
    simpa using congrArg (fun q => MvPolynomial.coeff m q)
      (CMvPolynomial.fromCMvPolynomial_C (σ := σ) (R := R) r)
  have hcomp' :
      ((CPoly.polyRingEquiv (σ := σ) (R := R) : CMvPolynomial σ R →+* MvPolynomial σ R).comp
        (algebraMap R (CMvPolynomial σ R))) = MvPolynomial.C := by
    simpa using hcomp
  have hvars :
      (fun i => CPoly.polyRingEquiv (σ := σ) (R := R) (CMvPolynomial.X (R := R) i)) =
      (fun i => MvPolynomial.X i) := by
    funext i
    exact fromCMvPolynomial_X (R := R) i
  have hmap' :
      CPoly.polyRingEquiv (σ := σ) (R := R)
          (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial σ R))
            (fun i => CMvPolynomial.X (R := R) i) (fromCMvPolynomial p))
        = MvPolynomial.eval₂
            (((CPoly.polyRingEquiv (σ := σ) (R := R)).toRingHom).comp
              (algebraMap R (CMvPolynomial σ R)))
            (fun i => MvPolynomial.X i)
            (fromCMvPolynomial p) := by
    simpa [MvPolynomial.eval₂Hom, hvars] using hmap
  have hmap'' :
      CPoly.polyRingEquiv (σ := σ) (R := R)
          (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial σ R))
            (fun i => CMvPolynomial.X (R := R) i) (fromCMvPolynomial p))
        = MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X (fromCMvPolynomial p) := by
    simpa [hcomp'] using hmap'
  calc
    CPoly.polyRingEquiv (σ := σ) (R := R)
        (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial σ R))
          (fun i => CMvPolynomial.X (R := R) i) (fromCMvPolynomial p))
      = MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X (fromCMvPolynomial p) := hmap''
    _ = fromCMvPolynomial p := by
          simp [MvPolynomial.eval₂_eta (p := fromCMvPolynomial p)]
    _ = CPoly.polyRingEquiv (σ := σ) (R := R) p := rfl

lemma list_foldl_add_comm {β K V : Type*} [AddCommMonoid β]
    (g : K → V → β) (l : List (K × V)) (init : β) :
    List.foldl (fun acc pair => acc + g pair.1 pair.2) init l =
    List.foldl (fun acc pair => g pair.1 pair.2 + acc) init l := by
  induction l generalizing init with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [show init + g h.1 h.2 = g h.1 h.2 + init from add_comm _ _]
    exact ih _

lemma foldl_add_comm {β : Type*} [AddCommMonoid β] {σ : Type*} [FinEnum σ]
    {R' : Type*} (g : CMvMonomial σ → R' → β)
    (t : Std.ExtTreeMap (CMvMonomial σ) R') :
    Std.ExtTreeMap.foldl (fun acc m c => acc + g m c) (0 : β) t =
    Std.ExtTreeMap.foldl (fun acc m c => g m c + acc) (0 : β) t := by
  simp only [Std.ExtTreeMap.foldl_eq_foldl_toList]
  exact list_foldl_add_comm g t.toList 0

lemma fromCMvPolynomial_finsupp_sum {σ τ : Type*} [FinEnum σ] [FinEnum τ]
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (g : (σ →₀ ℕ) → R → CMvPolynomial τ R)
    (a : CMvPolynomial σ R) :
    fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) g) =
    Finsupp.sum (fromCMvPolynomial a)
      (fun μ c => fromCMvPolynomial (g μ c)) := by
  unfold Finsupp.sum; ext
  simp [MvPolynomial.coeff_sum, coeff_eq, coeff_sum]

/-! ## API lemmas for `sumToIter` -/

lemma sumToIter_eq {σ : Type*} [FinEnum σ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial σ R) : sumToIter p = p := by
  rw [eq_iff_fromCMvPolynomial]
  unfold sumToIter
  rw [foldl_add_comm (g := fun m c => monomial m c) (t := p.1)]
  rw [foldl_eq_sum (t := p) (f := fun m c => monomial m c)]
  rw [fromCMvPolynomial_finsupp_sum]
  simp [fromCMvPolynomial_monomial, CMvMonomial.toFinsupp_ofFinsupp]
  rw [Finsupp.sum]
  exact MvPolynomial.support_sum_monomial_coeff (fromCMvPolynomial p)

lemma coeff_sumToIter {σ : Type*} [FinEnum σ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (m : CMvMonomial σ) (p : CMvPolynomial σ R) :
    coeff m (sumToIter p) = coeff m p := by
  simp [sumToIter_eq (p := p)]

@[simp] lemma sumToIter_zero {σ : Type*} [FinEnum σ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R] :
    sumToIter (0 : CMvPolynomial σ R) = 0 := by
  simpa using sumToIter_eq (p := (0 : CMvPolynomial σ R))

lemma sumToIter_add {σ : Type*} [FinEnum σ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CMvPolynomial σ R) :
    sumToIter (p + q) = sumToIter p + sumToIter q := by
  simp [sumToIter_eq]

@[simp] lemma sumToIter_idempotent {σ : Type*} [FinEnum σ] {R : Type*}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial σ R) :
    sumToIter (sumToIter p) = sumToIter p := by
  simp [sumToIter_eq]

attribute [grind =]
  aeval_C aeval_X aeval_add aeval_mul
  aeval_zero aeval_one aeval_pow aeval_neg aeval_sub

end CMvPolynomial

namespace Lawful

/-! ### Equivalence between `npow` and `npowBySq`

`Lawful.npow` (defined in `Multivariate/Lawful.lean`) is the naive `O(k)`
specification; `Lawful.npowBySq` is the `O(log k)` repeated-squaring
implementation. We prove pointwise equality here so that the `NatPow` instance
can be safely routed through the fast version.

The proofs need `mul_assoc` / `mul_one` / `mul_comm`, which are only available
once the `CommSemiring (CMvPolynomial σ R)` instance has been built — that is
why these lemmas live in `Operations.lean` rather than in `Lawful.lean`. -/

variable {σ : Type*} [FinEnum σ] {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Additive law for the naive `npow`: $p^{a+b} = p^a \cdot p^b$. -/
lemma npow_add (p : Lawful σ R) (a b : ℕ) :
    npow (a + b) p = npow a p * npow b p := by
  induction b with
  | zero => simp [npow, mul_one]
  | succ b ih =>
    show npow (a + b + 1) p = npow a p * npow (b + 1) p
    show npow (a + b) p * p = npow a p * (npow b p * p)
    rw [ih, mul_assoc]

/-- The fast repeated-squaring `npowBySq` agrees pointwise with the naive
`npow`. This is the equivalence that lets the `NatPow (Lawful σ R)` instance
be routed through `npowBySq` without changing observable behavior. -/
theorem npowBySq_eq_npow (p : Lawful σ R) : ∀ k : ℕ, npowBySq p k = npow k p
  | 0 => by unfold npowBySq; rfl
  | k + 1 => by
    unfold npowBySq
    have ih : npowBySq p ((k + 1) / 2) = npow ((k + 1) / 2) p :=
      npowBySq_eq_npow p ((k + 1) / 2)
    rw [ih]
    have hsq : npow ((k + 1) / 2) p * npow ((k + 1) / 2) p =
        npow ((k + 1) / 2 + (k + 1) / 2) p := (npow_add p _ _).symm
    by_cases heven : (k + 1) % 2 = 0
    · simp only [heven, ↓reduceIte, hsq]
      congr 1; omega
    · simp only [heven, ↓reduceIte, hsq]
      have hodd : (k + 1) / 2 + (k + 1) / 2 + 1 = k + 1 := by omega
      -- Goal: p * npow ((k+1)/2 + (k+1)/2) p = npow (k+1) p.
      -- Rewriting (k+1) on the right-hand side as the explicit successor unfolds
      -- npow once into npow _ p * p, after which the equality is just commutativity.
      conv_rhs => rw [← hodd]
      show p * npow _ p = npow _ p * p
      exact mul_comm _ _
  termination_by k => k
  decreasing_by omega

end Lawful

end CPoly
