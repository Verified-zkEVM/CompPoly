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

variable [CommSemiring R] {m : CMvMonomial σ} {p q : CMvPolynomial σ R}

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
