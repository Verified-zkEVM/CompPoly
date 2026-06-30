/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdusa
-/
import CompPoly.Multivariate.CMvMonomial
import CompPoly.Multivariate.Wheels
import CompPoly.Data.ExtTreeMap.ExtTreeMap
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Unlawful multivariate polynomials

This file defines the `Unlawful` type, which represents multivariate polynomials
as a map from monomials to coefficients. Unlike `Lawful`, it does not enforce
the absence of zero coefficients.

## Main definitions

* `CPoly.Unlawful σ R`: A map from `CMvMonomial σ` to `R`, implemented using `Std.ExtTreeMap`.
-/
set_option allowUnsafeReducibility true in
attribute [local reducible] instDecidableEqOfLawfulBEq
attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

/--
  Polynomial in variables `σ` with coefficients in `R`.
  Internally represented as a tree map from monomials to coefficients.
-/
abbrev Unlawful (σ : Type*) [FinEnum σ] (R : Type*) : Type _ :=
  Std.ExtTreeMap (CMvMonomial σ) R (Ord.compare (α := CMvMonomial σ))

section Instances

variable {σ : Type*} [FinEnum σ] {R : Type*}

instance : EmptyCollection (Unlawful σ R) := ⟨(∅ : Std.ExtTreeMap (CMvMonomial σ) R compare)⟩

instance : Singleton (MonoR σ R) (Unlawful σ R) :=
  inferInstanceAs (Singleton (MonoR σ R) (Std.ExtTreeMap (CMvMonomial σ) R compare))

instance : Insert (MonoR σ R) (Unlawful σ R) :=
  inferInstanceAs (Insert (MonoR σ R) (Std.ExtTreeMap (CMvMonomial σ) R compare))

instance : LawfulSingleton (MonoR σ R) (Unlawful σ R) :=
  inferInstanceAs (LawfulSingleton (MonoR σ R) (Std.ExtTreeMap (CMvMonomial σ) R compare))

instance : Membership (CMvMonomial σ) (Unlawful σ R) :=
  inferInstanceAs (Membership (CMvMonomial σ) (Std.ExtTreeMap (CMvMonomial σ) R compare))

@[default_instance]
instance (priority := high) : GetElem (Unlawful σ R) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (GetElem (Std.ExtTreeMap (CMvMonomial σ) R compare) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp))

instance : GetElem? (Unlawful σ R) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (GetElem? (Std.ExtTreeMap (CMvMonomial σ) R compare) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp))

instance : LawfulGetElem (Unlawful σ R) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (LawfulGetElem (Std.ExtTreeMap (CMvMonomial σ) R compare) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp))

end Instances

namespace Unlawful

attribute [grind ext] Std.ExtTreeMap.ext_getElem?

@[ext, grind ext]
lemma ext_getElem? {σ : Type*} [FinEnum σ] {R} {t₁ t₂ : Unlawful σ R}
    (h : ∀ (k : CMvMonomial σ), t₁[k]? = t₂[k]?) : t₁ = t₂ :=
  Std.ExtTreeMap.ext_getElem? h

variable {σ : Type*} [FinEnum σ] {R : Type*}

/-- Construct an `Unlawful` polynomial from a list of monomial-coefficient pairs. -/
@[simp, grind =]
def ofList (l : List (CMvMonomial σ × R)) : Unlawful σ R := ExtTreeMap.ofList l compare

/-- Check if the polynomial has no zero coefficients. -/
abbrev isNoZeroCoef [Zero R] (p : Unlawful σ R) : Prop := ∀ (m : CMvMonomial σ), p[m]? ≠ some 0

def toFinset [DecidableEq R] (p : Unlawful σ R) : Finset (CMvMonomial σ × R) :=
  p.toList.toFinset

/-- The list of monomials present in the polynomial. -/
abbrev monomials (p : Unlawful σ R) : List (CMvMonomial σ) :=
  p.keys

@[simp]
lemma mem_monomials {m : CMvMonomial σ} {up : Unlawful σ R} :
    m ∈ up.monomials ↔ m ∈ up := ExtTreeMap.mem_keys

instance [Repr R] : Repr (Unlawful σ R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial σ × R) :=
      ⟨fun (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

/-- Constant polynomial. -/
@[grind =]
def C [BEq R] [LawfulBEq R] [Zero R] (c : R) : Unlawful σ R :=
  if c = 0 then ∅ else .ofList [MonoR.C c]

section

variable {m : ℕ} [Zero R] {x : CMvMonomial σ}

section

variable [BEq R] [LawfulBEq R]

instance : OfNat (Unlawful σ R) 0 := ⟨C 0⟩

instance [NatCast R] [NeZero m] : OfNat (Unlawful σ R) m := ⟨C m⟩

@[simp, grind =]
lemma C_zero : C (σ := σ) (0 : R) = 0 := rfl

end

@[simp, grind =]
lemma C_zero' : C (σ := σ) (0 : ℕ) = 0 := rfl

@[simp, grind =]
lemma zero_eq_zero : (Zero.zero : R) = 0 := rfl

lemma zero_eq_empty [BEq R] [LawfulBEq R] : (0 : Unlawful σ R) = ∅ := by
  unfold_projs
  simp [C]

@[simp, grind .]
lemma not_mem_C_zero : x ∉ C 0 := by grind

section

variable [BEq R] [LawfulBEq R]

@[simp, grind .]
lemma not_mem_zero : x ∉ (0 : Unlawful σ R) := by rw [← C_zero]; grind

@[simp, grind .]
lemma isNoZeroCoef_zero : isNoZeroCoef (σ := σ) (R := R) 0 := by rw [← C_zero]; grind

end

end

/-- Pointwise addition of coefficients. -/
def add [Add R] (p₁ p₂ : Unlawful σ R) : Unlawful σ R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (Unlawful σ R) := ⟨add⟩

@[grind =]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Unlawful σ R} :
    p₁ + p₂ = p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂ := rfl

/-- Add a single monomial-coefficient term to a polynomial. -/
def addMonoR [Add R] (p : Unlawful σ R) (term : MonoR σ R) : Unlawful σ R :=
  p + .ofList [term]

/-- Multiply a polynomial by a single monomial term. -/
def mul₀ [Mul R] (t : MonoR σ R) (p : Unlawful σ R) : Unlawful σ R :=
  .ofList (p.toList.map fun (k, v) => (t.1 + k, t.2 * v))

attribute [grind =] ExtTreeMap.ofList_eq_empty_iff List.map_eq_nil_iff ExtTreeMap.toList_eq_nil_iff

@[simp, grind =]
lemma mul₀_zero [Zero R] [BEq R] [LawfulBEq R] [Mul R] {t : MonoR σ R} : mul₀ t 0 = 0 := by
  unfold mul₀
  grind

/-- Polynomial multiplication using a nested fold (distributive law). -/
def mul [Mul R] [Add R] [Zero R] [BEq R] [LawfulBEq R] (p₁ p₂ : Unlawful σ R) : Unlawful σ R :=
  p₁.foldl (init := 0)
    fun p m₁ c₁ ↦
      (p₂.foldl (init := 0) fun p' m₂ c₂ ↦ {(m₁ + m₂, c₁ * c₂)} + p') + p

instance [BEq R] [LawfulBEq R] [Mul R] [Add R] [Zero R] : Mul (Unlawful σ R) := ⟨mul⟩

section Neg

variable [Neg R]

/-- Negation (negates all coefficients). -/
def neg (p : Unlawful σ R) : Unlawful σ R :=
  p.map fun _ v ↦ -v

instance : Neg (Unlawful σ R) := ⟨neg⟩

/-- Subtraction. -/
def sub [Add R] (p₁ p₂ : Unlawful σ R) : Unlawful σ R :=
  Unlawful.add p₁ (-p₂)

instance [Add R] : Sub (Unlawful σ R) := ⟨sub⟩

end Neg

/-- Return the term with the lexicographically largest monomial. -/
def leadingTerm? : Unlawful σ R → Option (MonoR σ R) :=
  ExtTreeMap.maxEntry?

/-- Return the lexicographically largest monomial. -/
def leadingMonomial? : Unlawful σ R → Option (CMvMonomial σ) :=
  .map Prod.fst ∘ Unlawful.leadingTerm?

instance instDecidableEq [DecidableEq R] : DecidableEq (Unlawful σ R) := fun x y ↦
  if h : x.toList = y.toList
  then Decidable.isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else Decidable.isFalse (by grind)

def coeff {R : Type*} {σ : Type*} [FinEnum σ] [Zero R] (m : CMvMonomial σ) (p : Unlawful σ R) : R :=
  p[m]?.getD 0

@[simp, grind =]
lemma filter_get {R : Type*} [BEq R] [LawfulBEq R] {v : R} {m : CMvMonomial σ} (a : Unlawful σ R) :
    (ExtTreeMap.filter (fun _ c => c != v) a)[m]?.getD v = a[m]?.getD v := by
  grind

lemma add_getD? [AddZeroClass R] {m : CMvMonomial σ} {p q : Unlawful σ R} :
    (p.add q)[m]?.getD 0 = p[m]?.getD 0 + q[m]?.getD 0 := by
  unfold Unlawful.add
  by_cases m ∈ p <;> by_cases m ∈ q <;> grind [add_zero, zero_add]

end Unlawful

end CPoly
