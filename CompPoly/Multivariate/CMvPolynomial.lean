/- 
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen, Dimitris Mitsios, Quang Dao
-/
import CompPoly.Multivariate.Lawful
import CompPoly.Univariate.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Computable multivariate polynomials

Sparse computable multivariate polynomials over an arbitrary ordered variable type.
-/

namespace CPoly

open Std

attribute [local instance] beqOfOrd

/-- A computable multivariate polynomial over the ordered variable type `σ`. -/
abbrev CMvPolynomial (σ : Type) [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    (R : Type) [Zero R] : Type :=
  Lawful σ R

variable {σ τ : Type} {R : Type}

namespace CMvPolynomial

/-- Construct a constant polynomial. -/
def C [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [BEq R] [LawfulBEq R] [Zero R]
    (c : R) : CMvPolynomial σ R :=
  Lawful.C (σ := σ) (R := R) c

/-- Construct the polynomial `X i`. -/
def X [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R] [One R] [BEq R] [LawfulBEq R]
    (i : σ) : CMvPolynomial σ R :=
  Lawful.fromUnlawful <| .ofList [(CMvMonomial.single i 1, (1 : R))]

/-- Extract the coefficient of a monomial. -/
def coeff [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (m : CMvMonomial σ) (p : CMvPolynomial σ R) : R :=
  p.1[m]?.getD 0

attribute [grind =] coeff.eq_def

/-- Extensionality by coefficients. -/
@[ext, grind ext]
theorem ext [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (p q : CMvPolynomial σ R)
    (h : ∀ m, coeff m p = coeff m q) : p = q := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  apply Subtype.ext
  apply ExtTreeMap.ext_getElem?
  intro m
  specialize h m
  unfold coeff at h
  cases hp' : p[m]? with
  | none =>
      cases hq' : q[m]? with
      | none =>
          rfl
      | some b =>
          have hb : b ≠ 0 := by
            intro hz
            exact hq m (by simpa [hq', hz])
          have : 0 = b := by simpa [hp', hq'] using h
          exact False.elim (hb this.symm)
  | some a =>
      have ha : a ≠ 0 := by
        intro hz
        exact hp m (by simpa [hp', hz])
      cases hq' : q[m]? with
      | none =>
          have : a = 0 := by simpa [hp', hq'] using h
          exact False.elim (ha this)
      | some b =>
          have hab : a = b := by simpa [hp', hq'] using h
          simpa [hp', hq', hab]

section

variable [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
variable [BEq R] [LawfulBEq R]

@[simp, grind =]
lemma fromUnlawful_zero [Zero R] : Lawful.fromUnlawful (σ := σ) (R := R) 0 = (0 : Lawful σ R) := by
  unfold Lawful.fromUnlawful
  rfl

variable [AddMonoid R] {m : CMvMonomial σ} {p q : CMvPolynomial σ R}

@[simp, grind =]
lemma add_getD? : (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0 := by
  erw [Unlawful.filter_get]
  exact Unlawful.add_getD?

@[simp, grind =]
lemma coeff_add : coeff m (p + q) = coeff m p + coeff m q := by
  simp only [coeff, add_getD?]

/-- `Lawful.fromUnlawful` commutes with the left fold used in the multiplication backend. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful₀
    {t : List (CMvMonomial σ × R)} {f : CMvMonomial σ → R → Unlawful σ R} :
    ∀ init : Unlawful σ R,
      Lawful.fromUnlawful (List.foldl (fun u term => (f term.1 term.2) + u) init t) =
      List.foldl (fun l term => (Lawful.fromUnlawful (f term.1 term.2)) + l)
        (Lawful.fromUnlawful init) t := by
  induction t with
  | nil =>
      intro init
      simp
  | cons head tail ih =>
      intro init
      have hinit :
          Lawful.fromUnlawful (σ := σ) (R := R) (f head.1 head.2 + init) =
            Lawful.fromUnlawful (σ := σ) (R := R) (f head.1 head.2) +
              Lawful.fromUnlawful (σ := σ) (R := R) init := by
        ext m
        unfold coeff
        erw [Unlawful.filter_get]
        rw [CMvPolynomial.add_getD?
          (m := m)
          (p := Lawful.fromUnlawful (σ := σ) (R := R) (f head.1 head.2))
          (q := Lawful.fromUnlawful (σ := σ) (R := R) init)]
        iterate 2 erw [Unlawful.filter_get]
        exact Unlawful.add_getD?
      calc
        Lawful.fromUnlawful
            (List.foldl (fun u term => f term.1 term.2 + u) (f head.1 head.2 + init) tail)
            =
          List.foldl (fun l term => Lawful.fromUnlawful (f term.1 term.2) + l)
            (Lawful.fromUnlawful (f head.1 head.2 + init)) tail := ih _
        _ =
          List.foldl (fun l term => Lawful.fromUnlawful (f term.1 term.2) + l)
            (Lawful.fromUnlawful (f head.1 head.2) + Lawful.fromUnlawful init) tail := by
              rw [hinit]

/-- `Lawful.fromUnlawful` commutes with the term fold over an unlawful polynomial. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful {t : Unlawful σ R}
    {f : CMvMonomial σ → R → Unlawful σ R} :
    Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
    ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t := by
  simp only [ExtTreeMap.foldl_eq_foldl_toList]
  simpa using
    (fromUnlawful_fold_eq_fold_fromUnlawful₀ (σ := σ) (R := R)
      (t := t.toList) (f := f) (init := 0))

end

private lemma unlawful_singleton_add_eq_insert
    [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Add R]
    (p : Unlawful σ R) (term : CMvMonomial σ × R) (h : term.1 ∉ p) :
    Unlawful.ofList [term] + p = p.insert term.1 term.2 := by
  ext k
  by_cases hk : k = term.1
  · subst hk
    grind
  · have hcmp : compare term.1 k ≠ .eq := by
      intro hcmp
      exact hk (LawfulEqOrd.eq_of_compare hcmp).symm
    grind

private lemma unlawful_fold_singletons_eq_insertMany
    [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Add R]
    (init : Unlawful σ R)
    (l : List (CMvMonomial σ × R))
    (hdistinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq))
    (hdisjoint : ∀ a, a ∈ init → (l.map Prod.fst).contains a = false) :
    List.foldl (fun acc term => Unlawful.ofList [term] + acc) init l = init.insertMany l := by
  induction l generalizing init with
  | nil =>
      simp
  | cons head tail ih =>
      have htail : tail.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
        simpa using (List.pairwise_cons.1 hdistinct).2
      have hhead_not_mem_init : head.1 ∉ init := by
        intro hmem
        have := hdisjoint head.1 hmem
        simp at this
      rw [List.foldl_cons, unlawful_singleton_add_eq_insert _ _ hhead_not_mem_init]
      rw [Std.ExtTreeMap.insertMany_cons]
      exact ih (init := init.insert head.1 head.2) htail (by
        intro a ha
        rcases (ExtTreeMap.mem_insert.1 ha) with hEq | haInit
        · have hhead_not_in_tail : (tail.map Prod.fst).contains head.1 = false := by
            apply Bool.eq_false_iff.2
            intro hmem
            rw [List.contains_iff_mem] at hmem
            rcases List.mem_map.1 hmem with ⟨b, hb, hbEq⟩
            exact (List.pairwise_cons.1 hdistinct).1 b hb <| by
              simpa [hbEq] using (compare_self head.1)
          have haEq : head.1 = a := LawfulEqOrd.eq_of_compare hEq
          simpa [haEq] using hhead_not_in_tail
        · have hfalse : ¬ a = head.1 ∧ ∀ x : R, (a, x) ∉ tail := by
            simpa using hdisjoint a haInit
          apply Bool.eq_false_iff.2
          intro hmem
          rw [List.contains_iff_mem] at hmem
          rcases List.mem_map.1 hmem with ⟨⟨b1, b2⟩, hb, hbEq⟩
          simp at hbEq
          subst b1
          exact hfalse.2 b2 hb)

private lemma unlawful_fold_singletons_eq_self [BEq R] [LawfulBEq R] [Zero R] [Add R]
    [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    (t : Unlawful σ R) :
    ExtTreeMap.foldl (fun acc m c => Unlawful.ofList [(m, c)] + acc) 0 t = t := by
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  have hfold :
      List.foldl (fun acc term => Unlawful.ofList [term] + acc) (∅ : Unlawful σ R) t.toList = t := by
    rw [unlawful_fold_singletons_eq_insertMany (init := (∅ : Unlawful σ R)) (l := t.toList)]
    · rw [← Std.ExtTreeMap.ofList_eq_insertMany_empty (l := t.toList)]
      simpa using (Std.ExtTreeMap.toList_ofList (m := t))
    · simpa using Std.ExtTreeMap.distinct_keys_toList (t := t)
    · intro a ha
      cases ha
  simpa [OfNat.ofNat, Unlawful.C] using hfold

/-- Evaluate a polynomial using a coefficient homomorphism and variable assignment. -/
def eval₂ {S : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    [Semiring R] [CommSemiring S] :
    (R →+* S) → (σ → S) → CMvPolynomial σ R → S :=
  fun f vs p =>
    ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1

/-- Evaluate a polynomial at a point in the coefficient ring. -/
def eval [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [CommSemiring R] :
    (σ → R) → CMvPolynomial σ R → R :=
  eval₂ (RingHom.id _)

/-- Construct the monomial polynomial `c * m`. -/
def monomial [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [BEq R] [LawfulBEq R] [Zero R]
    (m : CMvMonomial σ) (c : R) : CMvPolynomial σ R :=
  if c == 0 then 0 else Lawful.fromUnlawful <| Unlawful.ofList [(m, c)]

private lemma singleton_term_eq_monomial
    [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [BEq R] [LawfulBEq R] [Zero R]
    (p : CMvPolynomial σ R) (term : CMvMonomial σ × R) (hlookup : p.1[term.1]? = some term.2) :
    Lawful.fromUnlawful (Unlawful.ofList [term]) = monomial term.1 term.2 := by
  have hne : term.2 ≠ 0 := by
    intro hz
    exact p.2 term.1 (by simpa [hlookup, hz])
  unfold monomial
  simp [hne]

/-- Rename variables using a function on indices. -/
def rename [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    [Ord τ] [TransOrd τ] [LawfulEqOrd τ]
    [BEq R] [LawfulBEq R] [Zero R] [Add R]
    (f : σ → τ) (p : CMvPolynomial σ R) : CMvPolynomial τ R :=
  Lawful.fromUnlawful <|
    ExtTreeMap.foldl (fun acc mono c => Unlawful.ofList [(CMvMonomial.rename f mono, c)] + acc) 0 p.1

/-- Reconstruct a polynomial by folding singleton monomials over its stored terms. -/
lemma fold_monomials_eq [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    [BEq R] [LawfulBEq R] [AddMonoid R]
    (p : CMvPolynomial σ R) :
    ExtTreeMap.foldl (fun acc mono c => monomial mono c + acc) 0 p.1 = p := by
  have hsingletons :
      Lawful.fromUnlawful
          (ExtTreeMap.foldl (fun acc mono c => Unlawful.ofList [(mono, c)] + acc) 0 p.1)
        =
      ExtTreeMap.foldl
        (fun acc mono c => Lawful.fromUnlawful (Unlawful.ofList [(mono, c)]) + acc) 0 p.1 := by
    simp only [ExtTreeMap.foldl_eq_foldl_toList]
    simpa using
      (fromUnlawful_fold_eq_fold_fromUnlawful₀ (σ := σ) (R := R)
        (t := p.1.toList)
        (f := fun mono c => Unlawful.ofList [(mono, c)])
        (init := 0))
  have hterms :
      ∀ (l : List (CMvMonomial σ × R)),
        (∀ term, term ∈ l → term ∈ p.1.toList) →
        ∀ init : CMvPolynomial σ R,
          l.foldl
              (fun acc term => Lawful.fromUnlawful (Unlawful.ofList [term]) + acc) init
            =
          l.foldl (fun acc term => monomial term.1 term.2 + acc) init := by
    intro l hsub init
    induction l generalizing init with
    | nil =>
        rfl
    | cons head tail ih =>
        rw [List.foldl_cons, List.foldl_cons]
        have hlookupOfList :
            (Std.ExtTreeMap.ofList p.1.toList compare)[head.1]? = some head.2 :=
          Std.ExtTreeMap.getElem?_ofList_of_mem
            (k_eq := by simpa using (compare_self head.1))
            (distinct := Std.ExtTreeMap.distinct_keys_toList (t := p.1))
            (mem := hsub head (by simp))
        have hlookup : p.1[head.1]? = some head.2 := by
          simpa using (Std.ExtTreeMap.toList_ofList (m := p.1) ▸ hlookupOfList)
        have hhead := singleton_term_eq_monomial (p := p) (term := head) (hlookup := hlookup)
        calc
          List.foldl (fun acc term => Lawful.fromUnlawful (Unlawful.ofList [term]) + acc)
              (Lawful.fromUnlawful (Unlawful.ofList [head]) + init) tail
            =
              List.foldl (fun acc term => monomial term.1 term.2 + acc)
                (Lawful.fromUnlawful (Unlawful.ofList [head]) + init) tail := by
                  apply ih
                  intro term hmem
                  exact hsub term (by simp [hmem])
          _ =
              List.foldl (fun acc term => monomial term.1 term.2 + acc)
                (monomial head.1 head.2 + init) tail := by
                  rw [hhead]
  have hterms₀ :
      ExtTreeMap.foldl
          (fun acc mono c => Lawful.fromUnlawful (Unlawful.ofList [(mono, c)]) + acc) 0 p.1
        =
      ExtTreeMap.foldl (fun acc mono c => monomial mono c + acc) 0 p.1 := by
    simp only [ExtTreeMap.foldl_eq_foldl_toList]
    exact hterms p.1.toList (by intro term hmem; exact hmem) 0
  calc
    ExtTreeMap.foldl (fun acc mono c => monomial mono c + acc) 0 p.1
      =
        ExtTreeMap.foldl
          (fun acc mono c => Lawful.fromUnlawful (Unlawful.ofList [(mono, c)]) + acc) 0 p.1 := by
            exact hterms₀.symm
    _ =
        Lawful.fromUnlawful
          (ExtTreeMap.foldl (fun acc mono c => Unlawful.ofList [(mono, c)] + acc) 0 p.1) := by
            exact hsingletons.symm
    _ = Lawful.fromUnlawful p.1 := by
          rw [unlawful_fold_singletons_eq_self]
    _ = p := Lawful.fromUnlawful_cast

private def evalMonomialSubst [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    [Ord τ] [TransOrd τ] [LawfulEqOrd τ]
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (vals : σ → CMvPolynomial τ R) (m : CMvMonomial σ) : CMvPolynomial τ R :=
  m.entries.foldl (fun acc entry => acc * vals entry.1 ^ entry.2) 1

/-- Substitute polynomials for variables. -/
def bind₁ [Ord σ] [TransOrd σ] [LawfulEqOrd σ]
    [Ord τ] [TransOrd τ] [LawfulEqOrd τ]
    [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : σ → CMvPolynomial τ R) (p : CMvPolynomial σ R) : CMvPolynomial τ R :=
  ExtTreeMap.foldl
    (fun acc mono c => CMvPolynomial.C (σ := τ) c * evalMonomialSubst f mono + acc)
    0 p.1

def maxDegreesMap [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (p : CMvPolynomial σ R) : Std.ExtTreeMap σ Nat compare :=
  ExtTreeMap.foldl
    (fun acc mono _ =>
      mono.entries.foldl
        (fun acc entry =>
          acc.alter entry.1 fun
            | none => some entry.2
            | some d => some (max d entry.2))
        acc)
    ∅ p.1

/-- The support of a polynomial, viewed as a `Finset` of `Finsupp` monomials. -/
noncomputable def support [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (p : CMvPolynomial σ R) : Finset (σ →₀ ℕ) :=
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  (Lawful.monomials p).map CMvMonomial.toFinsupp |>.toFinset

/-- The total degree of a polynomial. -/
def totalDegree [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R] :
    CMvPolynomial σ R → ℕ :=
  fun p => ExtTreeMap.foldl (fun d mono _ => max d mono.totalDegree) 0 p.1

/-- The multiset of variables with multiplicity given by the polynomial degree in each variable. -/
def degrees [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (p : CMvPolynomial σ R) : Multiset σ :=
  (maxDegreesMap (σ := σ) (R := R) p).foldl
    (fun acc i d => Multiset.replicate d i + acc) 0

/-- The degree of a polynomial in a variable. -/
def degreeOf [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (i : σ) (p : CMvPolynomial σ R) : ℕ :=
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  Multiset.count i p.degrees

/-- Variables that occur in the polynomial. -/
def vars [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (p : CMvPolynomial σ R) : Finset σ :=
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  p.degrees.toFinset

/-- `degreeOf` is the multiplicity of a variable in `degrees`. -/
lemma degreeOf_eq_count_degrees [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [Zero R]
    (i : σ) (p : CMvPolynomial σ R) :
    p.degreeOf i =
      (by
        letI : DecidableEq σ := decEqOfLawfulEqOrd _
        exact Multiset.count i p.degrees) := by
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  rfl

/-- Filter a polynomial, keeping only monomials satisfying `keep`. -/
def restrictBy [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [BEq R] [LawfulBEq R] [Zero R]
    (keep : CMvMonomial σ → Prop) [DecidablePred keep]
    (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  Lawful.fromUnlawful <| p.1.filter (fun m _ => decide (keep m))

/-- Restrict to monomials of total degree at most `d`. -/
def restrictTotalDegree [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  restrictBy (fun m => m.totalDegree ≤ d) p

/-- Restrict to monomials whose stored exponents are all at most `d`. -/
def restrictDegree [Ord σ] [TransOrd σ] [LawfulEqOrd σ] [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  restrictBy (fun m => m.entries.all fun entry => entry.2 ≤ d) p

end CMvPolynomial

end CPoly
