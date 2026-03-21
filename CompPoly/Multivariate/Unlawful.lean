/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdusa, Quang Dao
-/
import CompPoly.Multivariate.CMvMonomial
import CompPoly.Multivariate.Wheels
import Mathlib.Algebra.Lie.OfAssociative
import Std.Data.ExtTreeMap
import ExtTreeMapLemmas.ExtTreeMap

/-!
# Unlawful multivariate polynomials

Raw sparse polynomials represented as tree maps from lawful sparse monomials to coefficients.
-/

namespace CPoly

open Std

attribute [local instance] beqOfOrd

/-- Polynomial in variables `σ` with coefficients in `R`, without the no-zero-coefficient invariant. -/
@[grind =]
def Unlawful (σ : Type) [Ord σ] (R : Type) : Type :=
  Std.ExtTreeMap (CMvMonomial σ) R (Ord.compare (α := CMvMonomial σ))

section Instances

variable {σ : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ] {R : Type}

instance : EmptyCollection (Unlawful σ R) :=
  ⟨(∅ : Std.ExtTreeMap (CMvMonomial σ) R compare)⟩

instance : Singleton (MonoR σ R) (Unlawful σ R) :=
  inferInstanceAs (Singleton (MonoR σ R) (Std.ExtTreeMap (CMvMonomial σ) R compare))

instance : Insert (MonoR σ R) (Unlawful σ R) :=
  inferInstanceAs (Insert (MonoR σ R) (Std.ExtTreeMap (CMvMonomial σ) R compare))

instance : LawfulSingleton (MonoR σ R) (Unlawful σ R) :=
  inferInstanceAs (LawfulSingleton (MonoR σ R) (Std.ExtTreeMap (CMvMonomial σ) R compare))

instance : Membership (CMvMonomial σ) (Unlawful σ R) :=
  inferInstanceAs (Membership (CMvMonomial σ) (Std.ExtTreeMap (CMvMonomial σ) R compare))

@[default_instance]
instance (priority := high) : GetElem (Unlawful σ R) (CMvMonomial σ) R (fun p m => m ∈ p) :=
  inferInstanceAs
    (GetElem (Std.ExtTreeMap (CMvMonomial σ) R compare) (CMvMonomial σ) R
      (fun p m => m ∈ p))

instance : GetElem? (Unlawful σ R) (CMvMonomial σ) R (fun p m => m ∈ p) :=
  inferInstanceAs
    (GetElem? (Std.ExtTreeMap (CMvMonomial σ) R compare) (CMvMonomial σ) R
      (fun p m => m ∈ p))

instance : LawfulGetElem (Unlawful σ R) (CMvMonomial σ) R (fun p m => m ∈ p) :=
  inferInstanceAs
    (LawfulGetElem (Std.ExtTreeMap (CMvMonomial σ) R compare) (CMvMonomial σ) R
      (fun p m => m ∈ p))

end Instances

namespace Unlawful

attribute [grind ext] Std.ExtTreeMap.ext_getElem?

@[ext, grind ext]
lemma ext_getElem? {σ : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ] {R : Type}
    {t₁ t₂ : Unlawful σ R}
    (h : ∀ (k : CMvMonomial σ), t₁[k]? = t₂[k]?) : t₁ = t₂ :=
  Std.ExtTreeMap.ext_getElem? h

variable {σ : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ] {R : Type}

/-- Construct an unlawful polynomial from a list of terms. -/
@[simp, grind =]
def ofList (l : List (CMvMonomial σ × R)) : Unlawful σ R :=
  ExtTreeMap.ofList l compare

/-- Predicate asserting that no stored coefficient is zero. -/
abbrev isNoZeroCoef [Zero R] (p : Unlawful σ R) : Prop :=
  ∀ (m : CMvMonomial σ), p[m]? ≠ some 0

def toFinset [DecidableEq R] (p : Unlawful σ R) : Finset (CMvMonomial σ × R) :=
  p.toList.toFinset

/-- The monomials stored in the polynomial. -/
abbrev monomials (p : Unlawful σ R) : List (CMvMonomial σ) :=
  p.keys

@[simp]
lemma mem_monomials {m : CMvMonomial σ} {p : Unlawful σ R} :
    m ∈ p.monomials ↔ m ∈ p :=
  ExtTreeMap.mem_keys

instance [Repr σ] [Repr R] : Repr (Unlawful σ R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial σ × R) :=
      ⟨fun (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

/-- Constant polynomial. -/
@[grind =]
def C [BEq R] [LawfulBEq R] [Zero R] (c : R) : Unlawful σ R :=
  if c == 0 then ∅ else .ofList [MonoR.C c]

section

variable {m : ℕ} [Zero R]

section

variable [BEq R] [LawfulBEq R]

instance : OfNat (Unlawful σ R) 0 := ⟨C 0⟩

instance [NatCast R] [NeZero m] : OfNat (Unlawful σ R) m := ⟨C m⟩

end

end

/-- Pointwise addition of coefficients. -/
def add [Add R] (p₁ p₂ : Unlawful σ R) : Unlawful σ R :=
  p₁.mergeWith (fun _ c₁ c₂ => c₁ + c₂) p₂

instance [Add R] : Add (Unlawful σ R) := ⟨add⟩

@[grind =]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Unlawful σ R} :
    p₁ + p₂ = p₁.mergeWith (fun _ c₁ c₂ => c₁ + c₂) p₂ :=
  rfl

/-- Add a single term to an unlawful polynomial. -/
def addMonoR [Add R] (p : Unlawful σ R) (term : MonoR σ R) : Unlawful σ R :=
  p + .ofList [term]

/-- Multiply by a single term. -/
def mul₀ [Mul R] (t : MonoR σ R) (p : Unlawful σ R) : Unlawful σ R :=
  .ofList (p.toList.map fun (m, c) => (t.1 + m, t.2 * c))

/-- Polynomial multiplication by distributive expansion. -/
def mul [Mul R] [Add R] [Zero R] [BEq R] [LawfulBEq R]
    (p₁ p₂ : Unlawful σ R) : Unlawful σ R :=
  p₁.foldl (init := 0) fun p m₁ c₁ =>
    (p₂.foldl (init := 0) fun p' m₂ c₂ => {(m₁ + m₂, c₁ * c₂)} + p') + p

instance [BEq R] [LawfulBEq R] [Mul R] [Add R] [Zero R] : Mul (Unlawful σ R) := ⟨mul⟩

section Neg

variable [Neg R]

/-- Negate all coefficients. -/
def neg (p : Unlawful σ R) : Unlawful σ R :=
  p.map fun _ c => -c

instance : Neg (Unlawful σ R) := ⟨neg⟩

/-- Subtraction of unlawful polynomials. -/
def sub [Add R] (p₁ p₂ : Unlawful σ R) : Unlawful σ R :=
  Unlawful.add p₁ (-p₂)

instance [Add R] : Sub (Unlawful σ R) := ⟨sub⟩

end Neg

/-- The maximum term with respect to the storage comparator. -/
def leadingTerm? : Unlawful σ R → Option (MonoR σ R) :=
  ExtTreeMap.maxEntry?

/-- The maximum monomial with respect to the storage comparator. -/
def leadingMonomial? : Unlawful σ R → Option (CMvMonomial σ) :=
  Option.map Prod.fst ∘ leadingTerm?

instance instDecidableEq [DecidableEq R] : DecidableEq (Unlawful σ R) := fun x y =>
  if h : x.toList = y.toList then
    .isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else
    .isFalse (by grind)

def coeff [Zero R] (m : CMvMonomial σ) (p : Unlawful σ R) : R :=
  p[m]?.getD 0

@[simp, grind =]
lemma filter_get [BEq R] [LawfulBEq R] {v : R} {m : CMvMonomial σ} (p : Unlawful σ R) :
    (ExtTreeMap.filter (fun _ c => c != v) p)[m]?.getD v = p[m]?.getD v := by
  grind

lemma add_getD? [CommSemiring R] {m : CMvMonomial σ} {p q : Unlawful σ R} :
    (p.add q)[m]?.getD 0 = p[m]?.getD 0 + q[m]?.getD 0 := by
  unfold Unlawful.add
  by_cases hm₁ : m ∈ p <;> by_cases hm₂ : m ∈ q <;> grind [zero_add, add_zero]

end Unlawful

end CPoly
