/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Derek Sorensen
-/
import CompPoly.Multivariate.Lawful
import CompPoly.Univariate.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Batteries.Data.Vector.Lemmas

/-!
# Computable multivariate polynomials

Polynomials of the form `α₁ * m₁ + α₂ * m₂ + ... + αₖ * mₖ` where `αᵢ` is any semiring
and `mᵢ` is a `CMvMonomial`.

This is implemented as a wrapper around `CPoly.Lawful`, which ensures that all stored
coefficients are non-zero.

## Main definitions

* `CPoly.CMvPolynomial n R`: The type of multivariate polynomials in `n` variables
  with coefficients in `R`.
-/
namespace CPoly

open Std

/-- A computable multivariate polynomial in `n` variables with coefficients in `R`. -/
abbrev CMvPolynomial (n : ℕ) (R : Type) [Zero R] : Type := Lawful n R

variable {R : Type}

namespace CMvPolynomial

/-- Construct a constant polynomial. -/
def C {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R] (c : R) : CMvPolynomial n R :=
  Lawful.C (n := n) (R := R) c

/-- Construct the polynomial $X_i$. -/
def X {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] (i : Fin n) : CMvPolynomial n R :=
  let monomial : CMvMonomial n := Vector.ofFn (fun j => if j = i then 1 else 0)
  Lawful.fromUnlawful <| .ofList [(monomial, (1 : R))]

/-- Extract the coefficient of a monomial. -/
def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : CMvPolynomial n R) : R :=
  p.1[m]?.getD 0

attribute [grind =] coeff.eq_def

/-- Extensionality: two polynomials are equal if all their coefficients are equal. -/
@[ext, grind ext]
theorem ext {n : ℕ} [Zero R] (p q : CMvPolynomial n R)
    (h : ∀ m, coeff m p = coeff m q) : p = q := by
  unfold coeff at h
  rcases p with ⟨p, hp⟩; rcases q with ⟨q, hq⟩
  congr
  apply ExtTreeMap.ext_getElem?
  intros k; specialize h k
  by_cases k ∈ p <;> by_cases k ∈ q <;> grind

attribute [local grind =] Option.some_inj

section

variable [BEq R] [LawfulBEq R]

@[simp, grind =]
lemma fromUnlawful_zero {n : ℕ} [Zero R] : Lawful.fromUnlawful 0 = (0 : Lawful n R) := by
  unfold Lawful.fromUnlawful
  grind

variable {n : ℕ} [CommSemiring R] {m : CMvMonomial n} {p q : CMvPolynomial n R}

@[simp, grind =]
lemma add_getD? : (p + q).val[m]?.getD 0 = p.val[m]?.getD 0 + q.val[m]?.getD 0 := by
  erw [Unlawful.filter_get]
  exact Unlawful.add_getD?

@[simp, grind =]
lemma coeff_add : coeff m (p + q) = coeff m p + coeff m q := by simp only [coeff, add_getD?]

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects the sum fold. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful₀
    {t : List (CMvMonomial n × R)} {f : CMvMonomial n → R → Unlawful n R} :
    ∀ init : Unlawful n R,
    Lawful.fromUnlawful (List.foldl (fun u term => (f term.1 term.2) + u) init t) =
    List.foldl (fun l term => (Lawful.fromUnlawful (f term.1 term.2)) + l)
               (Lawful.fromUnlawful init) t := by
  induction' t with head tail ih
  · simp
  · intro init
    simp only [List.foldl_cons, ih]
    congr 1; ext m
    simp only [CMvMonomial.eq_1, coeff_add]
    unfold coeff Lawful.fromUnlawful
    iterate 3 erw [Unlawful.filter_get]
    exact Unlawful.add_getD?

/-- Auxiliary lemma showing that conversion from unlawful polynomials respects
    the fold over terms. -/
lemma fromUnlawful_fold_eq_fold_fromUnlawful {t : Unlawful n R}
    {f : CMvMonomial n → R → Unlawful n R} :
  Lawful.fromUnlawful (ExtTreeMap.foldl (fun u m c => (f m c) + u) 0 t) =
  ExtTreeMap.foldl (fun l m c => (Lawful.fromUnlawful (f m c)) + l) 0 t := by
  simp only [CMvMonomial.eq_1, ExtTreeMap.foldl_eq_foldl_toList]
  erw [fromUnlawful_fold_eq_fold_fromUnlawful₀ 0]
  simp
  rfl

end

/-- Evaluate a polynomial at a point given by a ring homomorphism `f`
    and variable assignments `vs`. -/
def eval₂ {R S : Type} {n : ℕ} [Semiring R] [CommSemiring S] :
    (R →+* S) → (Fin n → S) → CMvPolynomial n R → S :=
  fun f vs p => ExtTreeMap.foldl (fun s m c => (f c * MonoR.evalMonomial vs m) + s) 0 p.1

/-- Evaluate a polynomial at a given point. -/
def eval {R : Type} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvPolynomial n R → R :=
  eval₂ (RingHom.id _)

/-- The support of a polynomial (set of monomials with non-zero coefficients),
    represented as Finsupps. -/
def support {R : Type} {n : ℕ} [Zero R] (p : CMvPolynomial n R) : Finset (Fin n →₀ ℕ) :=
  (Lawful.monomials p).map CMvMonomial.toFinsupp |>.toFinset

/-- The total degree of a polynomial (maximum total degree of its monomials). -/
def totalDegree {R : Type} {n : ℕ} [inst : CommSemiring R] : CMvPolynomial n R → ℕ :=
  fun p => Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
    (fun s => Finsupp.sum s (fun _ e => e))

/-- The degree of a polynomial in a specific variable. -/
def degreeOf {R : Type} {n : ℕ} [Zero R] (i : Fin n) : CMvPolynomial n R → ℕ :=
  fun p =>
    Multiset.count i
    (Finset.sup (List.toFinset (List.map CMvMonomial.toFinsupp (Lawful.monomials p)))
      fun s => Finsupp.toMultiset s)

/-- Construct a monomial `c * m` as a `CMvPolynomial n R`.

  Creates a polynomial with a single monomial term. If `c = 0`, returns the zero polynomial.
-/
def monomial {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (m : CMvMonomial n) (c : R) : CMvPolynomial n R :=
  if c == 0 then 0 else Lawful.fromUnlawful <| Unlawful.ofList [(m, c)]

/-- Monomial ordering typeclass for `n` variables.

  Provides a way to compare monomials for determining leading terms.
-/
class MonomialOrder (n : ℕ) where
  compare : CMvMonomial n → CMvMonomial n → Ordering
  -- TODO: Add ordering axioms (transitivity, etc.)

/-- Degree of a monomial according to a monomial order.

  Returns the degree of a monomial as determined by the ordering.
  The exact meaning depends on the specific monomial order implementation
  (e.g., total degree for graded orders, weighted degree, etc.).
-/
def MonomialOrder.degree {n : ℕ} [MonomialOrder n] (m : CMvMonomial n) : ℕ :=
  sorry

/-- Leading monomial of a polynomial according to a monomial order.

  Returns `none` for the zero polynomial.
-/
def leadingMonomial {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : Option (CMvMonomial n) :=
  sorry

/-- Leading coefficient of a polynomial according to a monomial order.

  Returns `0` for the zero polynomial.
-/
def leadingCoeff {n : ℕ} {R : Type} [Zero R] [MonomialOrder n]
    (p : CMvPolynomial n R) : R :=
  sorry

/-- Multiset of all variable degrees appearing in the polynomial.

  Each variable `i` appears `degreeOf i p` times in the multiset.
-/
def degrees {n : ℕ} {R : Type} [Zero R] (p : CMvPolynomial n R) : Multiset (Fin n) :=
  Finset.univ.sum fun i => Multiset.replicate (p.degreeOf i) i

/-- Extract the set of variables that appear in a polynomial.

  Returns the set of variable indices `i : Fin n` such that `degreeOf i p > 0`.
-/
def vars {n : ℕ} {R : Type} [Zero R] (p : CMvPolynomial n R) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < p.degreeOf i

/-- `degreeOf` is the multiplicity of a variable in `degrees`. -/
lemma degreeOf_eq_count_degrees {n : ℕ} {R : Type} [Zero R]
    (i : Fin n) (p : CMvPolynomial n R) :
    p.degreeOf i = Multiset.count i p.degrees := by
  classical
  unfold CMvPolynomial.degrees
  symm
  calc
    Multiset.count i (∑ j, Multiset.replicate (p.degreeOf j) j)
        = ∑ j ∈ Finset.univ, Multiset.count i (Multiset.replicate (p.degreeOf j) j) := by
          simpa [Finset.sum] using
            (Multiset.count_sum' (s := Finset.univ)
              (a := i) (f := fun j => Multiset.replicate (p.degreeOf j) j))
    _ = ∑ j ∈ Finset.univ, if j = i then p.degreeOf j else 0 := by
          simp [Multiset.count_replicate, eq_comm]
    _ = p.degreeOf i := by
          simp

/-- Restrict polynomial to monomials with total degree ≤ d.

  Filters out all monomials where `m.totalDegree > d`.
-/
def restrictBy {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (keep : CMvMonomial n → Prop) [DecidablePred keep]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  Lawful.fromUnlawful <| p.1.filter (fun m _ => decide (keep m))

def restrictTotalDegree {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial n R) : CMvPolynomial n R :=
  restrictBy (fun m => m.totalDegree ≤ d) p

/-- Restrict polynomial to monomials whose degree in each variable is ≤ d.

  Filters out all monomials where `m.degreeOf i > d` for some variable `i`.
-/
def restrictDegree {n : ℕ} {R : Type} [BEq R] [LawfulBEq R] [Zero R]
    (d : ℕ) (p : CMvPolynomial n R) : CMvPolynomial n R :=
  restrictBy (fun m => ∀ i : Fin n, m.degreeOf i ≤ d) p

/-- Algebra evaluation: evaluates polynomial in an algebra.

  Given an algebra `σ` over `R` and a function `f : Fin n → σ`, evaluates the polynomial.
-/
def aeval {n : ℕ} {R σ : Type} [CommSemiring R] [CommSemiring σ] [Algebra R σ]
    (f : Fin n → σ) (p : CMvPolynomial n R) : σ :=
  sorry

/-- Substitution: substitutes polynomials for variables.

  Given `f : Fin n → CMvPolynomial m R`, substitutes `f i` for variable `X i`.
-/
def bind₁ {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → CMvPolynomial m R) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  sorry

/-- Rename variables using a function.

  Given `f : Fin n → Fin m`, renames variable `X i` to `X (f i)`.
-/
def rename {n m : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (f : Fin n → Fin m) (p : CMvPolynomial n R) : CMvPolynomial m R :=
  let renameMonomial (mono : CMvMonomial n) : CMvMonomial m :=
    Vector.ofFn (fun j => (Finset.univ.filter (fun i => f i = j)).sum (fun i => mono.get i))
  ExtTreeMap.foldl (fun acc mono c => acc + monomial (renameMonomial mono) c) 0 p.1

-- `renameEquiv` is defined in `CompPoly.Multivariate.Rename`

end CMvPolynomial

/-! ### Ring instances via transfer from `MvPolynomial`

The ring structure on `CMvPolynomial n R` is established by defining an injection
`fromCMvPolynomial : CMvPolynomial n R → MvPolynomial (Fin n) R` and transferring
the ring axioms from `MvPolynomial`. -/

section RingInstances

open CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Map a `CMvPolynomial` to the corresponding `MvPolynomial` for algebraic transfer. -/
def fromCMvPolynomial (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
  let support : List (Fin n →₀ ℕ) := p.monomials.map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by grind
  Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

omit [BEq R] [LawfulBEq R] in
lemma coeff_eq {m} (a : CMvPolynomial n R) :
    MvPolynomial.coeff m (fromCMvPolynomial a) = a.coeff (CMvMonomial.ofFinsupp m) := rfl

@[aesop simp]
lemma eq_iff_fromCMvPolynomial {u v : CMvPolynomial n R} :
    u = v ↔ fromCMvPolynomial u = fromCMvPolynomial v := by
  constructor
  · rintro rfl; rfl
  · intro h
    ext m
    have : MvPolynomial.coeff (CMvMonomial.toFinsupp m) (fromCMvPolynomial u) =
           MvPolynomial.coeff (CMvMonomial.toFinsupp m) (fromCMvPolynomial v) := by rw [h]
    simp only [coeff_eq, CMvMonomial.ofFinsupp_toFinsupp] at this
    exact this

lemma fromCMvPolynomial_injective : Function.Injective (@fromCMvPolynomial n R _) := by
  intros a b h
  exact eq_iff_fromCMvPolynomial.mpr h

@[simp]
lemma map_add (a b : CMvPolynomial n R) :
    fromCMvPolynomial (a + b) = fromCMvPolynomial a + fromCMvPolynomial b := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_eq, coeff_eq, coeff_eq]
  unfold CMvPolynomial.coeff
  unfold_projs
  unfold CPoly.Lawful.add
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  unfold_projs
  unfold Unlawful.add Lawful.fromUnlawful
  simp only [ExtTreeMap.get?_eq_getElem?, Unlawful.zero_eq_zero]
  erw [Unlawful.filter_get]
  by_cases h : (CMvMonomial.ofFinsupp m) ∈ a.1 <;> by_cases h' : (CMvMonomial.ofFinsupp m) ∈ b.1
  · erw [ExtTreeMap.mergeWith_of_mem_mem h h', Option.getD_some]
    have h₁ : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) =
      (a.1)[CMvMonomial.ofFinsupp m] := by simp [h]
    have h₂ : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) =
      (b.1)[CMvMonomial.ofFinsupp m] := by simp [h']
    erw [h₁, h₂]
    rfl
  · erw [ExtTreeMap.mergeWith_of_mem_left h h']
    have : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h']
    erw [this]
    have {x : R} : x + 0 = x := by simp
    specialize @this ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0)
    unfold_projs at this
    erw [this]
    rfl
  · erw [ExtTreeMap.mergeWith_of_mem_right h h']
    have : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h]
    erw [this]
    have {x : R} : 0 + x = x := by simp
    specialize @this ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0)
    unfold_projs at this
    erw [this]
    rfl
  · erw [ExtTreeMap.mergeWith_of_not_mem h h']
    have h₁ : ((a.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h]
    have h₂ : ((b.1)[CMvMonomial.ofFinsupp m]?.getD 0) = 0 := by
      simp [h']
    erw [h₁, h₂, Option.getD_none]
    have : 0 + 0 = (0 : R) := by simp
    unfold_projs at this
    erw [this]
    rfl

@[simp]
lemma map_zero : fromCMvPolynomial (0 : CMvPolynomial n R) = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  unfold fromCMvPolynomial
  simp only
    [ Lawful.mem_iff_cast,
      Lawful.not_mem_zero,
      not_false_eq_true,
      getElem?_neg, Option.getD_none
    ]
  rfl

instance : TransCmp (fun x y ↦ compareOfLessAndEq (α := ℕ) x y) where
  eq_swap {a b} := by apply compareOfLessAndEq_eq_swap <;> omega
  isLE_trans {a b c} h₁ h₂ := by rw [isLE_compareOfLessAndEq] at * <;> omega

instance {n : ℕ} : TransCmp (α := CMvMonomial n)
    (Vector.compareLex (n := n) fun x y => compareOfLessAndEq (α := ℕ) x y) :=
  inferInstanceAs (TransCmp (Vector.compareLex (n := n) fun x y => compareOfLessAndEq (α := ℕ) x y))

@[simp]
lemma map_one : fromCMvPolynomial (1 : CMvPolynomial n R) = 1 := by
  ext m
  have : MvPolynomial.coeff m 1 = if m = 0 then 1 else (0 : R) := by
    unfold MvPolynomial.coeff
    unfold_projs
    simp only [Nat.zero_eq, Unlawful.zero_eq_zero]
    split_ifs with h <;>
      unfold AddMonoidAlgebra.single Finsupp.toFun Finsupp.single <;>
        simp [h]
  rw [this]
  unfold fromCMvPolynomial MvPolynomial.coeff
  simp only [Lawful.getElem?_eq_val_getElem?, Finsupp.coe_mk]
  unfold_projs
  unfold Lawful.C Unlawful.C MonoR.C
  simp only [Nat.cast_one]

  have triv_lem : (1 : R) = 0 → ∀ x y : R, x = y := by
    intros h
    have (x : R) : x = 0 := by
      have : x * 1 = x * 0 := by
        rw [h]
      simp only [mul_one, mul_zero] at this
      exact this
    intros x y; rw [this x, this y]

  split_ifs with g g' g'
  · rw [Nat.cast_one] at g; apply triv_lem g
  · rw [Nat.cast_one] at g; apply triv_lem g
  · have finsupp_m_eq_one : CMvMonomial.ofFinsupp m = CMvMonomial.zero := by
      rw [g']
      unfold CMvMonomial.ofFinsupp CMvMonomial.zero
      ext i h
      simp only [Nat.zero_eq, Finsupp.coe_mk]
      grind
    rw [finsupp_m_eq_one]
    have one_one_get₁ :
      ({(CMvMonomial.zero, 1)} : Unlawful n R)[(@CMvMonomial.zero n)]?.getD 0 = One.one := by
      unfold_projs; simp only [ExtTreeMap.empty_eq_emptyc, ExtTreeMap.get?_eq_getElem?,
        ExtTreeMap.getElem?_insert_self, Unlawful.zero_eq_zero, Option.getD_some]
    convert one_one_get₁
  · have : CMvMonomial.ofFinsupp m ≠ CMvMonomial.zero := by
      unfold CMvMonomial.ofFinsupp CMvMonomial.zero
      intros h
      have {i} : (Vector.ofFn m).get i = (Vector.replicate n 0).get i := by
        rw [h]
      apply g'
      ext i
      simp only [Finsupp.coe_mk]
      simp only [Vector.get_ofFn, Vector.get_replicate] at this
      exact this
    rw [ExtTreeMap.get?_eq_getElem?, getElem?_neg]
    simp only [Unlawful.zero_eq_zero, Option.getD_none]
    unfold Unlawful.ofList
    simp only [ExtTreeMap.ofList_singleton, ExtTreeMap.mem_insert, Std.compare_eq_iff_eq,
      ExtTreeMap.not_mem_empty, or_false]
    tauto

attribute [local grind=] Unlawful.add Lawful.add Unlawful.mul Lawful.mul

instance instAddCommSemigroup {n : ℕ} : AddCommSemigroup (CPoly.CMvPolynomial n R) where
  add_assoc := by aesop (add safe apply add_assoc)
  add_comm := by grind

instance instAddMonoid {n : ℕ} : AddMonoid (CPoly.CMvPolynomial n R) where
  zero_add _ := by aesop
  add_zero _ := by aesop
  nsmul n p := (List.replicate n p).sum
  nsmul_succ {m x} := by grind

instance instAddCommMonoid {n : ℕ} : AddCommMonoid (CPoly.CMvPolynomial n R) where
  toAddMonoid := inferInstance
  add_comm := by grind

omit [BEq R] [LawfulBEq R] in
lemma toList_pairs_monomial_coeff {β : Type} [AddCommMonoid β]
    {t : Unlawful n R}
  {f : CMvMonomial n → R → β} :
  t.toList.map (fun term => f term.1 term.2) =
    t.monomials.map (fun m => f m (t.coeff m)) := by
  unfold Unlawful.monomials Unlawful.coeff
  rw [←ExtTreeMap.map_fst_toList_eq_keys]
  rw [List.map_congr_left, List.map_map]
  grind

omit [BEq R] [LawfulBEq R] in
lemma foldl_eq_sum {β : Type} [AddCommMonoid β]
    {t : CMvPolynomial n R}
    {f : CMvMonomial n → R → β} :
    ExtTreeMap.foldl (fun x m c => (f m c) + x) 0 t.1 =
      Finsupp.sum (fromCMvPolynomial t) (f ∘ CMvMonomial.ofFinsupp) := by
  unfold Finsupp.sum Finset.sum
  simp only [Function.comp_apply, add_comm]
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  rw [←List.foldl_map (g := fun x y ↦ x + y), ←List.sum_eq_foldl]
  rw [toList_pairs_monomial_coeff]
  conv => rhs; arg 1; arg 1; ext x; arg 2; rw [←MvPolynomial.coeff, coeff_eq]
  congr 1
  have monomials_dedup_self : (Lawful.monomials t).dedup = Lawful.monomials t := by
    unfold Lawful.monomials
    simp only [List.dedup_eq_self]
    grind [ExtTreeMap.distinct_keys_toList]
  rw [List.dedup_map_of_injective CMvMonomial.injective_toFinsupp]
  rw [monomials_dedup_self]
  aesop

lemma coeff_sum [AddCommMonoid α]
    (s : Finset α)
    (f : α → CMvPolynomial n R)
    (m : CMvMonomial n) :
    CMvPolynomial.coeff m (∑ x ∈ s, f x) = ∑ x ∈ s, CMvPolynomial.coeff m (f x) := by
  rw [←Finset.sum_map_toList s, ←Finset.sum_map_toList s]
  induction' s.toList with h t ih
  · grind
  · simp [CMvPolynomial.coeff_add]
    congr

lemma fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial
    {f : (Fin n →₀ ℕ) → R → Lawful n R }
    {a : CMvPolynomial n R} :
    fromCMvPolynomial (Finsupp.sum (fromCMvPolynomial a) f) =
      Finsupp.sum (fromCMvPolynomial a) (fun m c ↦ fromCMvPolynomial (f m c)) := by
  unfold Finsupp.sum; ext
  simp [MvPolynomial.coeff_sum, coeff_eq, coeff_sum]

@[simp]
lemma map_mul (a b : CMvPolynomial n R) :
    fromCMvPolynomial (a * b) = fromCMvPolynomial a * fromCMvPolynomial b := by
  dsimp only [HMul.hMul, Mul.mul, Lawful.mul, Unlawful.mul]
  simp only [CMvPolynomial.fromUnlawful_fold_eq_fold_fromUnlawful]
  unfold MonoidAlgebra.mul'
  rw [foldl_eq_sum]; simp_rw [foldl_eq_sum]
  let F₀ (p q) : CMvMonomial n → R → Lawful n R :=
    fun p_1 q_1 ↦ Lawful.fromUnlawful {(p + p_1 , q * q_1)}
  set F₁ : (Fin n →₀ ℕ) → R → Lawful n R :=
    (fun p q ↦ Finsupp.sum (fromCMvPolynomial b) (F₀ p q ∘ CMvMonomial.ofFinsupp))
      ∘ CMvMonomial.ofFinsupp with eqF₁
  let F₂ a₁ b₁ :
    Multiplicative (Fin n →₀ ℕ) → R → MonoidAlgebra R (Multiplicative (Fin n →₀ ℕ)) :=
    fun a₂ b₂ ↦ MonoidAlgebra.single (a₁ * a₂) (b₁ * b₂)
  set F₃ : Multiplicative (Fin n →₀ ℕ) → R → MvPolynomial (Fin n) R :=
    fun a₁ b₁ ↦ Finsupp.sum (fromCMvPolynomial b) (F₂ a₁ b₁) with eqF₃
  have fromCMvPolynomial_F₁_eq_F₃ {m₁ : Multiplicative (Fin n →₀ ℕ)} {c₁ : R} :
      fromCMvPolynomial (F₁ m₁ c₁) = F₃ m₁ c₁ := by
    dsimp only [Function.comp_apply, F₁, F₀, F₃, F₂]
    rw [fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial]
    simp only [Function.comp_apply]
    congr
    ext (m₂ : Multiplicative _) c₂ m
    rw [coeff_eq]
    unfold CMvPolynomial.coeff Lawful.fromUnlawful
    erw [Unlawful.filter_get, ←CMvMonomial.map_mul, ExtTreeMap.singleton_eq_insert]
    erw [ExtTreeMap.getElem?_insert]
    by_cases m_in : m = m₁ * m₂
    · rw [←m_in]
      simp only [compare_self]
      unfold MvPolynomial.coeff MonoidAlgebra.single
      simp only [m_in, Finsupp.single_eq_same]
      rfl
    · simp only
        [ Std.compare_eq_iff_eq,
          ExtTreeMap.not_mem_empty,
          not_false_eq_true,
          getElem?_neg
        ]
      unfold MvPolynomial.coeff MonoidAlgebra.single
      rw [Finsupp.single_eq_of_ne (by symm; grind)]
      split
      next h contra =>
        exfalso; apply m_in; symm
        apply CMvMonomial.injective_ofFinsupp contra
      next h => simp_all only [Option.getD_none]
  have : F₃ = fun σ x ↦ fromCMvPolynomial (F₁ σ x) := by
    ext x
    rw [fromCMvPolynomial_F₁_eq_F₃]
  rw [this]
  rw [fromCMvPolynomial_sum_eq_sum_fromCMvPolynomial]
  rfl

instance instMonoidWithZero {n : ℕ} : MonoidWithZero (CPoly.CMvPolynomial n R) where
  zero_mul := by aesop
  mul_zero := by aesop
  mul_assoc := by aesop (add safe apply _root_.mul_assoc)
  one_mul := by aesop
  mul_one := by aesop

instance instSemiring {n : ℕ} : Semiring (CPoly.CMvPolynomial n R) where
  left_distrib {p q r} := by
    simp_all only [eq_iff_fromCMvPolynomial, map_mul, map_add]
    apply mul_add
  right_distrib {p q r} := by
    simp_all only [eq_iff_fromCMvPolynomial, map_mul, map_add]
    apply add_mul

instance instCommSemiring {n : ℕ} : CommSemiring (CPoly.CMvPolynomial n R) where
  natCast_zero := by grind
  natCast_succ := by intro n; simp
  npow_zero := by intro x; simp [npowRecAuto, npowRec]
  npow_succ := by intro n x; simp [npowRecAuto, npowRec]
  mul_comm := by aesop (add safe apply _root_.mul_comm)

end RingInstances

section CommRingInstance

open CMvPolynomial

variable {n : ℕ} {R : Type} [CommRing R] [BEq R] [LawfulBEq R]

@[simp]
lemma map_neg (a : CMvPolynomial n R) :
    fromCMvPolynomial (-a) = -fromCMvPolynomial a := by
  ext m
  rw [coeff_eq]
  simp only [MvPolynomial.coeff_neg, coeff_eq]
  unfold CMvPolynomial.coeff
  show (Lawful.fromUnlawful (a.1.map fun _ v ↦ -v)).1[CMvMonomial.ofFinsupp m]?.getD 0 =
       -(a.1[CMvMonomial.ofFinsupp m]?.getD 0)
  change (Lawful.fromUnlawful (a.1.map fun _ v ↦ -v)).1[CMvMonomial.ofFinsupp m]?.getD 0 =
       -(a.1[CMvMonomial.ofFinsupp m]?.getD 0)
  conv_lhs => simp only [Lawful.fromUnlawful]
  erw [Unlawful.filter_get (a := (a.1.map fun _ v ↦ -v))]
  erw [ExtTreeMap.getElem?_map]
  cases a.1[CMvMonomial.ofFinsupp m]? with
  | none => simp
  | some v => simp

/-- `CMvPolynomial n R` forms a commutative ring when `R` is a commutative ring. -/
instance instCommRing {n : ℕ} : CommRing (CMvPolynomial n R) where
  __ := instCommSemiring (R := R)
  neg_add_cancel a := by
    rw [eq_iff_fromCMvPolynomial]
    simp [map_add, map_neg, map_zero]
  zsmul := zsmulRec
  mul_comm := mul_comm

end CommRingInstance

namespace CMvPolynomial

/-- Convert sum representation to iterative form.

  TODO: Clarify intended behavior - may be related to converting between different
  polynomial representations or evaluation strategies.
-/
def sumToIter {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]
    (p : CMvPolynomial n R) : CMvPolynomial n R :=
  sorry

end CMvPolynomial

-- TODO: Phase 1 items requiring Semiring/CommSemiring instances from MvPolyEquiv.lean
--       (circular dependency):
-- TODO: `Algebra R (CMvPolynomial n R)` instance
-- TODO: `Module R (CMvPolynomial n R)` instance
-- TODO: `finSuccEquiv` - Equivalence between (n+1)-variable and n-variable polynomials
-- TODO: `optionEquivLeft` - Equivalence for option-indexed variables
-- See MvPolyEquiv.lean for: eval₂Hom, isEmptyRingEquiv, SMulZeroClass

end CPoly
