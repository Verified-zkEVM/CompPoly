/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Quang Dao
-/
import CompPoly.Multivariate.Unlawful
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Lawful multivariate polynomials

`Lawful σ R` is the canonical sparse polynomial representation obtained by filtering zero
coefficients from `Unlawful σ R`.
-/

namespace CPoly

open Std

attribute [local instance] beqOfOrd

/-- The subtype of unlawful polynomials with no stored zero coefficients. -/
def Lawful (σ : Type) [Ord σ] [TransOrd σ] [LawfulEqOrd σ] (R : Type) [Zero R] :=
  { p : Unlawful σ R // p.isNoZeroCoef }

section Instances

variable {σ : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ] {R : Type} [Zero R]

instance : EmptyCollection (Lawful σ R) :=
  ⟨⟨∅, by
    intro m hm
    cases hm
  ⟩⟩

instance : GetElem (Lawful σ R) (CMvMonomial σ) R (fun p m => m ∈ p.1) :=
  ⟨fun p m h => p.1[m]'h⟩

instance : GetElem? (Lawful σ R) (CMvMonomial σ) R (fun p m => m ∈ p.1) :=
  ⟨fun p m => p.1[m]?, fun p m => p.1[m]!⟩

instance : Membership (CMvMonomial σ) (Lawful σ R) :=
  ⟨fun p m => m ∈ p.1⟩

end Instances

namespace Lawful

variable {σ : Type} [Ord σ] [TransOrd σ] [LawfulEqOrd σ] {R : Type} [Zero R]
variable {p : Lawful σ R} {m x : CMvMonomial σ}

lemma getElem?_eq_val_getElem? : p[m]? = p.1[m]? :=
  rfl

lemma mem_iff_cast : x ∈ p.1 ↔ x ∈ p :=
  Iff.rfl

@[grind =]
lemma mem_iff : x ∈ p ↔ ∃ v, v ≠ 0 ∧ p[x]? = some v := by
  rw [← mem_iff_cast, ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  rcases p with ⟨p, hp⟩
  have hpx := hp x
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_, hv⟩
    intro hz
    exact hpx (hv.trans <| congrArg some hz)
  · rintro ⟨v, hv, hvp⟩
    exact ⟨v, hvp⟩

@[simp]
theorem getElem?_ne_some_zero : p[m]? ≠ some 0 := by
  rcases p with ⟨p, hp⟩
  simpa using hp m

@[grind .]
theorem getD_getElem?_ne_zero_of_mem (h : m ∈ p) : p[m]?.getD 0 ≠ 0 := by
  rcases p.mem_iff.mp h with ⟨v, hv, hvp⟩
  simpa [hvp] using hv

@[simp, grind =]
lemma getElem_eq_getElem (h : m ∈ p) : p[m] = p.1[m] :=
  rfl

section

variable [BEq R] [LawfulBEq R]

/-- Filter out zero coefficients to obtain a lawful polynomial. -/
def fromUnlawful (p : Unlawful σ R) : Lawful σ R :=
  ⟨
    p.filter fun _ c => c != 0,
    by
      intro m
      have hfilter :
          (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? =
            p[m]?.filter (fun c => c != 0) :=
        Std.ExtTreeMap.getElem?_filter_with_getKey
          (m := p) (k := m) (f := fun _ c => c != 0)
      cases h : p[m]? with
      | none =>
          intro hz
          have hz' : p[m]?.filter (fun c => c != 0) = some 0 := by
            exact hfilter ▸ hz
          simpa [h] using hz'
      | some val =>
          by_cases hval : val = 0
          · intro hz
            have hz' : p[m]?.filter (fun c => c != 0) = some 0 := by
              exact hfilter ▸ hz
            simpa [h, hval] using hz'
          · intro hz
            have hz' : p[m]?.filter (fun c => c != 0) = some 0 := by
              exact hfilter ▸ hz
            simpa [h, hval] using hz'
  ⟩

@[grind ←]
protected lemma grind_fromUnlawful_congr {p₁ p₂ : Unlawful σ R}
    (h : p₁ = p₂) : Lawful.fromUnlawful p₁ = Lawful.fromUnlawful p₂ := by
  cases h
  rfl

/-- Constant lawful polynomial. -/
def C (c : R) : Lawful σ R :=
  fromUnlawful (Unlawful.C (σ := σ) c)

instance : OfNat (Lawful σ R) 0 := ⟨C 0⟩

instance {m : ℕ} [NeZero m] [NatCast R] : OfNat (Lawful σ R) m := ⟨C m⟩

lemma cast_fromUnlawful : (fromUnlawful p.1).1 = p.1 := by
  rcases p with ⟨p, hp⟩
  apply ExtTreeMap.ext_getElem?
  intro m
  have hfilter :
      (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? =
        p[m]?.filter (fun c => c != 0) :=
    Std.ExtTreeMap.getElem?_filter_with_getKey
      (m := p) (k := m) (f := fun _ c => c != 0)
  have hpm := hp m
  cases h : p[m]? with
  | none =>
      have hlookup : (fromUnlawful p).1[m]? = none := by
        change (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? = none
        exact hfilter.trans (by simp [h])
      change (fromUnlawful p).1[m]? = none
      exact hlookup
  | some val =>
      have hval : val ≠ 0 := by
        intro hz
        exact hpm (by simpa [h, hz])
      have hlookup : (fromUnlawful p).1[m]? = some val := by
        change (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? = some val
        exact hfilter.trans (by simp [h, hval])
      change (fromUnlawful p).1[m]? = some val
      exact hlookup

lemma fromUnlawful_cast {p : Lawful σ R} : fromUnlawful p.1 = p := by
  cases p with
  | mk p hp =>
      apply Subtype.ext
      apply ExtTreeMap.ext_getElem?
      intro m
      have hfilter :
          (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? =
            p[m]?.filter (fun c => c != 0) :=
        Std.ExtTreeMap.getElem?_filter_with_getKey
          (m := p) (k := m) (f := fun _ c => c != 0)
      have hpm := hp m
      cases h : p[m]? with
      | none =>
          have hlookup : (fromUnlawful p).1[m]? = none := by
            change (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? = none
            exact hfilter.trans (by simp [h])
          change (fromUnlawful p).1[m]? = none
          exact hlookup
      | some val =>
          have hval : val ≠ 0 := by
            intro hz
            exact hpm (by simpa [h, hz])
          have hlookup : (fromUnlawful p).1[m]? = some val := by
            change (ExtTreeMap.filter (fun _ c => c != 0) p)[m]? = some val
            exact hfilter.trans (by simp [h, hval])
          change (fromUnlawful p).1[m]? = some val
          exact hlookup

/-- Addition of lawful polynomials. -/
def add [Add R] (p₁ p₂ : Lawful σ R) : Lawful σ R :=
  fromUnlawful (p₁.1 + p₂.1)

instance [Add R] : Add (Lawful σ R) := ⟨add⟩

@[grind =]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Lawful σ R} :
    p₁ + p₂ = Lawful.fromUnlawful (p₁.1.add p₂.1) :=
  rfl

/-- Multiplication of lawful polynomials. -/
def mul [Mul R] [Add R] : Lawful σ R → Lawful σ R → Lawful σ R
  | p₁, p₂ => fromUnlawful (p₁.1 * p₂.1)

instance [Mul R] [Add R] [Zero R] : Mul (Lawful σ R) := ⟨mul⟩

/-- Polynomial exponentiation. -/
def npow [NatCast R] [Add R] [Mul R] : ℕ → Lawful σ R → Lawful σ R
  | 0, _ => 1
  | n + 1, p => npow n p * p

instance [NatCast R] [Add R] [Mul R] : NatPow (Lawful σ R) := ⟨fun e p => npow p e⟩

/-- The list of monomials in a lawful polynomial. -/
abbrev monomials (p : Lawful σ R) : List (CMvMonomial σ) :=
  p.1.monomials

@[simp]
lemma mem_monomials_iff {w : CMvMonomial σ} : w ∈ p.monomials ↔ w ∈ p := by
  show w ∈ p.1.monomials ↔ w ∈ p.1
  simpa using (Unlawful.mem_monomials (m := w) (p := p.1))

end

section

variable [BEq R] [LawfulBEq R]

/-- Negation of lawful polynomials. -/
def neg [Neg R] (p : Lawful σ R) : Lawful σ R :=
  fromUnlawful (-p.1)

instance [Neg R] : Neg (Lawful σ R) := ⟨neg⟩

/-- Subtraction of lawful polynomials. -/
def sub [Add R] [Neg R] (p₁ p₂ : Lawful σ R) : Lawful σ R :=
  p₁ + (-p₂)

instance [Add R] [Neg R] : Sub (Lawful σ R) := ⟨sub⟩

instance [DecidableEq R] : DecidableEq (Lawful σ R) := fun x y =>
  if h : x.1 = y.1 then
    .isTrue (by
      cases x
      cases y
      simp at h
      subst h
      rfl)
  else
    .isFalse (by
      intro hxy
      apply h
      exact congrArg Subtype.val hxy)

end

end Lawful

end CPoly
