/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi
-/
import CompPoly.Multivariate.Unlawful
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# 'Lawful' finite supports

This file defines the `Lawful` subtype, which consists of `Unlawful` polynomials
where all stored coefficients are guaranteed to be non-zero. This provides a canonical
representation (similar to `Finsupp`) and is the primary representation used for
computable multivariate polynomials.

## Main definitions

* `CPoly.Lawful σ R`: The subtype of `Unlawful σ R` with no zero coefficients.
-/
set_option allowUnsafeReducibility true in
attribute [local reducible] instDecidableEqOfLawfulBEq
attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

/-- The subtype of polynomials with no zero coefficients. -/
def Lawful (σ : Type*) [FinEnum σ] (R : Type*) [Zero R] : Type _ :=
  {p : Unlawful σ R // p.isNoZeroCoef}

variable {σ : Type*} [FinEnum σ] {R : Type*} [Zero R]

section Instances

@[grind=]
instance instEmptyCol : EmptyCollection (Lawful σ R) := ⟨∅, by grind⟩

instance : GetElem (Lawful σ R) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m h ↦ lp.1[m]'h⟩

instance : GetElem? (Lawful σ R) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp.1) :=
  ⟨fun lp m ↦ lp.1[m]?, fun lp m ↦ lp.1[m]!⟩

instance : Membership (CMvMonomial σ) (Lawful σ R) :=
  ⟨fun lp m ↦ m ∈ lp.1⟩

instance : LawfulGetElem (Lawful σ R) (CMvMonomial σ) R (fun lp m ↦ m ∈ lp) :=
  ⟨
    fun ⟨c, hc⟩ i _ ↦ by have := getElem?_def c i; aesop,
    fun ⟨c, hc⟩ i ↦ by have := getElem!_def c i; aesop
  ⟩

end Instances

namespace Lawful

variable {p : Lawful σ R} {m x : CMvMonomial σ}

@[simp, grind _=_]
lemma getElem?_eq_val_getElem? : p[m]? = p.1[m]? := rfl

@[simp, grind _=_]
lemma mem_iff_cast : x ∈ p.1 ↔ x ∈ p := by rfl

@[grind =]
lemma mem_iff : x ∈ p ↔ ∃ v, v ≠ 0 ∧ p[x]? = .some v := by
  erw [←mem_iff_cast, ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
  rcases p with ⟨p, hp⟩
  specialize hp x
  grind

@[simp]
theorem getElem?_ne_some_zero : p[m]? ≠ some 0 := by
  rcases p; grind

@[grind .]
theorem getD_getElem?_ne_zero_of_mem (h : m ∈ p) : p[m]?.getD 0 ≠ 0 := by
  grind

@[simp, grind =]
lemma getElem_eq_getElem (h : m ∈ p) : p[m] = p.1[m] := by rfl

variable [BEq R] [LawfulBEq R]

/-- Convert an `Unlawful` polynomial to a `Lawful` one by filtering out zero coefficients. -/
def fromUnlawful (p : Unlawful σ R) : Lawful σ R :=
  {
    val := p.filter fun _ c ↦ c != 0
    property _ := by aesop (add simp ExtTreeMap.getElem?_filter) (add safe (by grind))
  }

@[grind←]
protected lemma grind_fromUnlawful_congr {p₁ p₂ : Unlawful σ R}
    (h : p₁ = p₂) : Lawful.fromUnlawful p₁ = Lawful.fromUnlawful p₂ := by grind

/-- Construct a constant polynomial. -/
def C (c : R) : Lawful σ R :=
  ⟨Unlawful.C c, by grind⟩

instance instOfNat_zero : OfNat (Lawful σ R) 0 := ⟨C 0⟩

lemma zero_def : Zero.zero (α := Lawful σ R) = C 0 := rfl

instance instOfNat {m : ℕ} [NeZero m] [NatCast R] : OfNat (Lawful σ R) m := ⟨C m⟩

@[simp, grind =]
lemma C_zero : C (σ := σ) (0 : R) = 0 := rfl

@[simp, grind =]
lemma C_zero' : C (σ := σ) (0 : ℕ) = 0 := rfl

lemma zero_eq_zero : (0 : Lawful σ R) = ⟨0, by grind⟩ := rfl

lemma zero_eq_empty : (0 : Lawful σ R) = ∅ := by
  unfold_projs
  simp [C, Unlawful.zero_eq_empty]

@[simp, grind .]
lemma not_mem_C_zero : x ∉ C 0 := by simp [zero_eq_empty]; unfold_projs; grind

@[simp, grind .]
lemma not_mem_zero : x ∉ (0 : Lawful σ R) := by rw [zero_eq_zero]; exact Unlawful.not_mem_zero

@[simp]
lemma cast_fromUnlawful : (fromUnlawful p.1).1 = p.1 := by
  unfold fromUnlawful
  rcases p with ⟨p, hp⟩
  simp; ext1 x
  grind

section

/-- Addition of polynomials (results in a lawful polynomial). -/
def add [Add R] (p₁ p₂ : Lawful σ R) : Lawful σ R :=
  fromUnlawful <| p₁.val + p₂.val

instance [Add R] : Add (Lawful σ R) := ⟨add⟩

@[grind=]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Lawful σ R} :
    p₁ + p₂ = Lawful.fromUnlawful (p₁.1.add p₂.1) := rfl

/--
  Note to self: This goes too far.
-/
@[grind=]
protected lemma grind_add_skip_aggressive [Add R] {p₁ p₂ : Lawful σ R} :
    p₁ + p₂ = fromUnlawful (ExtTreeMap.mergeWith (fun _ c₁ c₂ => c₁ + c₂) p₁.1 p₂.1) := rfl

/-- Multiplication of polynomials (results in a lawful polynomial). -/
def mul [Mul R] [Add R] (p₁ p₂ : Lawful σ R) : Lawful σ R :=
  fromUnlawful <| p₁.val * p₂.val

instance [Mul R] [Add R] [Zero R] : Mul (Lawful σ R) := ⟨mul⟩

/-- Polynomial exponentiation via repeated multiplication. `O(k)` multiplications.

This is the specification; `npowBySq` is the efficient `O(log k)` implementation
used by the `NatPow` instance once the equivalence with this naive form has been
proven. -/
def npow [NatCast R] [Add R] [Mul R] : ℕ → Lawful σ R → Lawful σ R
  | .zero  , _ => 1
  | .succ n, p => (npow n p) * p

/-- Polynomial exponentiation via repeated squaring. `O(log k)` multiplications
instead of `O(k)`.

For `k > 0`, computes `p ^ k` by recursing on `k / 2`:
* If `k` is even: `(p ^ (k / 2))²`
* If `k` is odd:  `p · (p ^ (k / 2))²`

Equivalent to `npow` (see `npowBySq_eq_npow`). -/
@[inline, specialize]
def npowBySq [NatCast R] [Add R] [Mul R] (p : Lawful σ R) : ℕ → Lawful σ R
  | 0 => 1
  | k + 1 =>
    let half := npowBySq p ((k + 1) / 2)
    let sq := half * half
    if (k + 1) % 2 = 0 then sq else p * sq
  decreasing_by omega

instance [NatCast R] [Add R] [Mul R] : NatPow (Lawful σ R) := ⟨fun e b ↦ npow b e⟩

/-- The list of monomials in a polynomial. -/
abbrev monomials (p : Lawful σ R) : List (CMvMonomial σ) :=
  p.1.monomials

/-- Check if a polynomial is a non-zero constant. -/
def NzConst {σ : Type*} [FinEnum σ] {R : Type*} [Zero R] (p : Lawful σ R) : Prop :=
  p.val.size = 1 ∧ p.val.contains CMvMonomial.zero

omit [BEq R] [LawfulBEq R] in
@[simp, grind _=_]
lemma mem_monomials_iff {w : CMvMonomial σ} : w ∈ Lawful.monomials p ↔ w ∈ p := by
  grind

instance {p : Lawful σ R} : Decidable (NzConst p) := by
  dsimp [NzConst]
  infer_instance

end

@[simp, grind=]
lemma fromUnlawful_cast {p : Lawful σ R} : fromUnlawful p.1 = p := by
  unfold fromUnlawful
  congr
  rcases p with ⟨p, hp⟩
  ext
  grind

section

variable [BEq R] [LawfulBEq R]

/-- Negation of a polynomial. -/
def neg [Neg R] (p : Lawful σ R) : Lawful σ R :=
  fromUnlawful p.1.neg

instance [Neg R] : Neg (Lawful σ R) := ⟨neg⟩

/-- Subtraction of polynomials. -/
def sub [Add R] [Neg R] (p₁ p₂ : Lawful σ R) : Lawful σ R :=
  p₁ + (-p₂)

instance [Add R] [Neg R] : Sub (Lawful σ R) := ⟨sub⟩

instance instDecidableEq [DecidableEq R] : DecidableEq (Lawful σ R) := fun x y ↦
  if h : x.1.toList = y.1.toList
  then Decidable.isTrue (by have := ExtTreeMap.ext_toList (t₁ := x.1) (t₂ := y.1)
                            simp_rw [Subtype.val_inj] at this
                            grind)
  else Decidable.isFalse (by grind)

end

end Lawful

end CPoly
