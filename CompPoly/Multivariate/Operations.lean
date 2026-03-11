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
* `rename`: Rename variables using a function `Fin n → Fin m`.
* `aeval`: Algebra evaluation.
* `bind₁`: Substitution of polynomials for variables.
-/
namespace CPoly

open Std

variable {R : Type}

namespace CMvPolynomial

/-! ## Leading-term operations -/

/-- Monomial ordering typeclass for `n` variables.

  Provides a way to compare monomials for determining leading terms.
-/
class MonomialOrder (n : ℕ) where
  compare : CMvMonomial n → CMvMonomial n → Ordering
  -- TODO: Add ordering axioms (transitivity, etc.)

/-- Baseline degree of a monomial.

  Currently this is the ordinary total degree and is independent of
  `MonomialOrder.compare`.
-/
def MonomialOrder.degree {n : ℕ} (m : CMvMonomial n) : ℕ :=
  m.totalDegree

/-- Leading monomial of a polynomial according to a monomial order.

  Returns `none` for the zero polynomial.
-/
def leadingMonomial {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : Option (CMvMonomial n) :=
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
def leadingTerm {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder n]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  match leadingMonomial p with
  | none => 0
  | some m => monomial m (coeff m p)

/-- Leading coefficient of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial.
-/
def leadingCoeff {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : R :=
  match leadingMonomial p with
  | none => 0
  | some m => coeff m p

@[simp] lemma leadingCoeff_eq_zero_of_leadingMonomial_eq_none
    {n : ℕ} {R : Type} [Zero R] [MonomialOrder n] {p : CMvPolynomial n R}
    (h : leadingMonomial p = none) : leadingCoeff p = 0 := by
  simp [leadingCoeff, h]

lemma leadingCoeff_eq_coeff_of_leadingMonomial_eq_some
    {n : ℕ} {R : Type} [Zero R] [MonomialOrder n] {p : CMvPolynomial n R}
    {m : CMvMonomial n} (h : leadingMonomial p = some m) : leadingCoeff p = coeff m p := by
  simp [leadingCoeff, h]

/-- Packaged form of `leadingCoeff`: it is the coefficient at the optional leading monomial,
defaulting to `0` when no leading monomial exists. -/
lemma leadingCoeff_eq_coeff_leadingMonomial
    {n : ℕ} {R : Type} [Zero R] [MonomialOrder n] (p : CMvPolynomial n R) :
    leadingCoeff p = (leadingMonomial p).elim 0 (fun m => coeff m p) := by
  grind [leadingCoeff]

@[simp] lemma leadingTerm_eq_zero_of_leadingMonomial_eq_none
    {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder n]
    {p : CMvPolynomial n R} (h : leadingMonomial p = none) :
    leadingTerm p = 0 := by
  grind [leadingTerm]

@[simp] lemma leadingTerm_eq_monomial_of_leadingMonomial_eq_some
    {n : ℕ} {R : Type} [Zero R] [BEq R] [LawfulBEq R] [MonomialOrder n]
    {p : CMvPolynomial n R} {m : CMvMonomial n} (h : leadingMonomial p = some m) :
    leadingTerm p = monomial m (coeff m p) := by
  grind [leadingTerm]

/-! ## Evaluation and substitution -/

/-- Algebra evaluation: evaluates polynomial in an algebra.

  Given an algebra `σ` over `R` and a function `f : Fin n → σ`, evaluates the polynomial.
-/
def aeval {n : ℕ} {R σ : Type} [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) : σ :=
  eval₂ (algebraMap R σ) f p

@[simp] lemma aeval_eq_eval₂ {n : ℕ} {R σ : Type}
    [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) :
    aeval f p = eval₂ (algebraMap R σ) f p := rfl

@[simp] lemma aeval_C {n : ℕ} {R σ : Type}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (c : R) :
    aeval f (CMvPolynomial.C (n := n) c) = algebraMap R σ c := by
  unfold aeval
  rw [eval₂_equiv (p := CMvPolynomial.C (n := n) c) (f := algebraMap R σ) (vals := f)]
  simp [CMvPolynomial.fromCMvPolynomial_C]

@[simp] lemma aeval_add {n : ℕ} {R σ : Type}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p q : CMvPolynomial n R) :
    aeval f (p + q) = aeval f p + aeval f q := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := σ) (algebraMap R σ) f).map_add p q

@[simp] lemma aeval_mul {n : ℕ} {R σ : Type}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p q : CMvPolynomial n R) :
    aeval f (p * q) = aeval f p * aeval f q := by
  unfold aeval
  simpa [CMvPolynomial.eval₂Hom_apply] using
    (CMvPolynomial.eval₂Hom (S := σ) (algebraMap R σ) f).map_mul p q

/-- Substitution: substitutes polynomials for variables.

  Given `f : Fin n → CMvPolynomial m R`, substitutes `f i` for variable `X i`.
-/
def bind₁ {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  ExtTreeMap.foldl
    (fun acc mono c => CMvPolynomial.C (n := m) c * MonoR.evalMonomial f mono + acc)
    0 p.1

/-- The computable substitution `bind₁` agrees with algebraic evaluation. -/
lemma bind₁_eq_aeval {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p : CMvPolynomial n R) :
    bind₁ f p = aeval (σ := CMvPolynomial m R) f p := by
  have hmap : ∀ c : R,
      (algebraMap R (CMvPolynomial m R)) c = CMvPolynomial.C (n := m) c := by
    intro c
    rfl
  unfold bind₁ aeval CMvPolynomial.eval₂
  simp [hmap]

@[simp] lemma bind₁_C {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (c : R) :
    bind₁ f (CMvPolynomial.C (n := n) c) = CMvPolynomial.C (n := m) c := by
  rw [bind₁_eq_aeval]
  simpa using (aeval_C (n := n) (R := R) (σ := CMvPolynomial m R) f c)

@[simp] lemma bind₁_add {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p q : CMvPolynomial n R) :
    bind₁ f (p + q) = bind₁ f p + bind₁ f q := by
  repeat rw [bind₁_eq_aeval]
  simpa using (aeval_add (n := n) (R := R) (σ := CMvPolynomial m R) f p q)

@[simp] lemma bind₁_mul {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p q : CMvPolynomial n R) :
    bind₁ f (p * q) = bind₁ f p * bind₁ f q := by
  repeat rw [bind₁_eq_aeval]
  simpa using (aeval_mul (n := n) (R := R) (σ := CMvPolynomial m R) f p q)

/-! ## Core operations -/

/-- Rename variables using a function.

  Given `f : Fin n → Fin m`, renames variable `X i` to `X (f i)`.
-/
def rename {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → Fin m) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  let renameMonomial (mono : CMvMonomial n) : CMvMonomial m :=
    Vector.ofFn (fun j => (Finset.univ.filter (fun i => f i = j)).sum (fun i => mono.get i))
  ExtTreeMap.foldl (fun acc mono c => acc + monomial (renameMonomial mono) c) 0 p.1

-- `renameEquiv` is defined in `CompPoly.Multivariate.Rename`

/-- Iterative reconstruction of a polynomial by folding over terms. -/
def sumToIter {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  ExtTreeMap.foldl (fun acc m c => acc + monomial m c) 0 p.1

/-! ## Bridge and transport lemmas (technical) -/

lemma X_eq_monomial {k : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (i : Fin k) :
    CMvPolynomial.X (R := R) i = CMvPolynomial.monomial
      (Vector.ofFn (fun j => if j = i then 1 else 0))
      (1 : R) := by
  unfold CMvPolynomial.X CMvPolynomial.monomial
  by_cases h : (1 : R) = 0
  · ext m; unfold CMvPolynomial.coeff Lawful.fromUnlawful
    erw [Unlawful.filter_get]; simp [h]; grind
  · simp only [show ((1 : R) == 0) = false from by simp [h]]
    exact (if_neg (by decide)).symm

lemma toFinsupp_unitMono {k : ℕ}
    (i : Fin k) :
    CMvMonomial.toFinsupp
      (Vector.ofFn (fun j : Fin k =>
        if j = i then 1 else 0)) =
    Finsupp.single i 1 := by
  ext j
  simp [CMvMonomial.toFinsupp, Vector.get,
    Finsupp.single_apply, eq_comm]

lemma fromCMvPolynomial_monomial {k : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (mono : CMvMonomial k) (c : R) :
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

lemma fromCMvPolynomial_X {k : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (i : Fin k) :
    fromCMvPolynomial (CMvPolynomial.X (R := R) i) =
    MvPolynomial.X i := by
  rw [X_eq_monomial, fromCMvPolynomial_monomial, toFinsupp_unitMono]
  rfl

@[simp] lemma aeval_X {n : ℕ} {R σ : Type}
    [CommSemiring R] [BEq R] [LawfulBEq R]
    [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (i : Fin n) :
    aeval f (CMvPolynomial.X (R := R) i) = f i := by
  unfold aeval
  rw [eval₂_equiv (p := CMvPolynomial.X (R := R) i) (f := algebraMap R σ) (vals := f)]
  simp [fromCMvPolynomial_X]

@[simp] lemma bind₁_X {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (i : Fin n) :
    bind₁ f (CMvPolynomial.X (R := R) i) = f i := by
  rw [bind₁_eq_aeval]
  simpa using (aeval_X (n := n) (R := R) (σ := CMvPolynomial m R) f i)

@[simp] lemma bind₁_id {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) :
    bind₁ (fun i => CMvPolynomial.X (R := R) i) p = p := by
  rw [bind₁_eq_aeval]
  unfold aeval
  apply (CPoly.polyRingEquiv (n := n) (R := R)).injective
  rw [eval₂_equiv (p := p) (f := algebraMap R (CMvPolynomial n R))
    (vals := fun i => CMvPolynomial.X (R := R) i)]
  have hmap := MvPolynomial.map_eval₂Hom
    (f := algebraMap R (CMvPolynomial n R))
    (g := fun i => CMvPolynomial.X (R := R) i)
    (φ := (CPoly.polyRingEquiv (n := n) (R := R)).toRingHom)
    (p := fromCMvPolynomial p)
  have hcomp :
      ((CPoly.polyRingEquiv (n := n) (R := R)).toRingHom).comp
        (algebraMap R (CMvPolynomial n R)) = MvPolynomial.C := by
    ext r m
    rw [RingHom.comp_apply]
    rw [show (algebraMap R (CMvPolynomial n R)) r = CMvPolynomial.C (n := n) r from rfl]
    simpa using congrArg (fun q => MvPolynomial.coeff m q)
      (CMvPolynomial.fromCMvPolynomial_C (n := n) (R := R) r)
  have hcomp' :
      ((CPoly.polyRingEquiv (n := n) (R := R) : CMvPolynomial n R →+* MvPolynomial (Fin n) R).comp
        (algebraMap R (CMvPolynomial n R))) = MvPolynomial.C := by
    simpa using hcomp
  have hvars :
      (fun i => CPoly.polyRingEquiv (n := n) (R := R) (CMvPolynomial.X (R := R) i)) =
      (fun i => MvPolynomial.X i) := by
    funext i
    exact fromCMvPolynomial_X (R := R) i
  have hmap' :
      CPoly.polyRingEquiv (n := n) (R := R)
          (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial n R))
            (fun i => CMvPolynomial.X (R := R) i) (fromCMvPolynomial p))
        = MvPolynomial.eval₂
            (((CPoly.polyRingEquiv (n := n) (R := R)).toRingHom).comp
              (algebraMap R (CMvPolynomial n R)))
            (fun i => MvPolynomial.X i)
            (fromCMvPolynomial p) := by
    simpa [MvPolynomial.eval₂Hom, hvars] using hmap
  have hmap'' :
      CPoly.polyRingEquiv (n := n) (R := R)
          (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial n R))
            (fun i => CMvPolynomial.X (R := R) i) (fromCMvPolynomial p))
        = MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X (fromCMvPolynomial p) := by
    simpa [hcomp'] using hmap'
  calc
    CPoly.polyRingEquiv (n := n) (R := R)
        (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial n R))
          (fun i => CMvPolynomial.X (R := R) i) (fromCMvPolynomial p))
      = MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X (fromCMvPolynomial p) := hmap''
    _ = fromCMvPolynomial p := by
          simp [MvPolynomial.eval₂_eta (p := fromCMvPolynomial p)]
    _ = CPoly.polyRingEquiv (n := n) (R := R) p := rfl

lemma list_foldl_add_comm {β K V : Type} [AddCommMonoid β]
    (g : K → V → β) (l : List (K × V)) (init : β) :
    List.foldl (fun acc pair => acc + g pair.1 pair.2) init l =
    List.foldl (fun acc pair => g pair.1 pair.2 + acc) init l := by
  induction l generalizing init with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [show init + g h.1 h.2 = g h.1 h.2 + init from add_comm _ _]
    exact ih _

lemma foldl_add_comm {β : Type} [AddCommMonoid β] {k : ℕ}
    {R' : Type} (g : CMvMonomial k → R' → β)
    (t : Std.ExtTreeMap (CMvMonomial k) R') :
    Std.ExtTreeMap.foldl (fun acc m c => acc + g m c) (0 : β) t =
    Std.ExtTreeMap.foldl (fun acc m c => g m c + acc) (0 : β) t := by
  simp only [Std.ExtTreeMap.foldl_eq_foldl_toList]
  exact list_foldl_add_comm g t.toList 0

lemma fromCMvPolynomial_finsupp_sum {n k : ℕ} [CommSemiring R] [BEq R] [LawfulBEq R]
    (g : (Fin n →₀ ℕ) → R → CMvPolynomial k R)
    (a : CMvPolynomial n R) :
    fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) g) =
    Finsupp.sum (fromCMvPolynomial a)
      (fun μ c => fromCMvPolynomial (g μ c)) := by
  unfold Finsupp.sum; ext
  simp [MvPolynomial.coeff_sum, coeff_eq, coeff_sum]

/-! ## API lemmas for `sumToIter` -/

lemma sumToIter_eq {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) : sumToIter p = p := by
  rw [eq_iff_fromCMvPolynomial]
  unfold sumToIter
  rw [foldl_add_comm (g := fun m c => monomial m c) (t := p.1)]
  rw [foldl_eq_sum (t := p) (f := fun m c => monomial m c)]
  rw [fromCMvPolynomial_finsupp_sum]
  simp [fromCMvPolynomial_monomial, CMvMonomial.toFinsupp_ofFinsupp]
  rw [Finsupp.sum]
  exact MvPolynomial.support_sum_monomial_coeff (fromCMvPolynomial p)

lemma coeff_sumToIter {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (m : CMvMonomial n) (p : CMvPolynomial n R) :
    coeff m (sumToIter p) = coeff m p := by
  simp [sumToIter_eq (p := p)]

@[simp] lemma sumToIter_zero {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] :
    sumToIter (0 : CMvPolynomial n R) = 0 := by
  simpa using sumToIter_eq (p := (0 : CMvPolynomial n R))

lemma sumToIter_add {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CMvPolynomial n R) :
    sumToIter (p + q) = sumToIter p + sumToIter q := by
  simp [sumToIter_eq]

@[simp] lemma sumToIter_idempotent {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) :
    sumToIter (sumToIter p) = sumToIter p := by
  simp [sumToIter_eq]

end CMvPolynomial

end CPoly
