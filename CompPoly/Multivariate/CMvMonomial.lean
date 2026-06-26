/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.FinEnum
import Batteries.Data.Vector.Basic
import Batteries.Data.Vector.Lemmas

/-!
# Computable monomials

Monomials of the form `X₀ᵃ * X₁ᵇ * ... * Xₖᶻ`. These are represented as vectors of natural numbers,
where each element corresponds to the exponent of a variable.

The variables are indexed by a type `σ` carrying a `FinEnum σ` instance. The exponents are stored
in a `Vector ℕ (FinEnum.card σ)` indexed through the enumeration `FinEnum.equiv : σ ≃ Fin (card σ)`.

## Main definitions

* `CPoly.CMvMonomial σ`: The type of monomials in variables `σ`, implemented as
  `Vector ℕ (FinEnum.card σ)`.
-/
namespace CPoly

open FinEnum

/--
  Monomial in variables `σ`.
  - `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂ (with the variables in enumeration order).
-/
@[grind =]
def CMvMonomial (σ : Type*) [FinEnum σ] : Type := Vector ℕ (FinEnum.card σ)

syntax "#m[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#m[$elems,*]) => `(#v[$elems,*])

variable {σ : Type*} [FinEnum σ]

instance : Repr (CMvMonomial σ) where
  reprPrec m _ :=
    let indexed := (Array.range m.size).zip m.1
    let toFormat : Std.ToFormat (ℕ × ℕ) :=
      ⟨λ (i, p) ↦ "X" ++ repr i ++ "^" ++ repr p⟩
    @Std.Format.joinSep _ toFormat indexed.toList " * "

section Instances

instance : GetElem (CMvMonomial σ) ℕ ℕ fun _ idx ↦ idx < FinEnum.card σ :=
  inferInstanceAs (GetElem (Vector ℕ (FinEnum.card σ)) ℕ ℕ _)

instance : GetElem? (CMvMonomial σ) ℕ ℕ fun _ idx ↦ idx < FinEnum.card σ :=
  inferInstanceAs (GetElem? (Vector ℕ (FinEnum.card σ)) ℕ ℕ _)

instance : DecidableEq (CMvMonomial σ) :=
  inferInstanceAs (DecidableEq (Vector ℕ (FinEnum.card σ)))

instance : Ord (CMvMonomial σ) :=
  inferInstanceAs (Ord (Vector ℕ (FinEnum.card σ)))

instance : Std.TransCmp (Ord.compare (α := CMvMonomial σ)) :=
  inferInstanceAs (Std.TransCmp (Ord.compare (α := Vector ℕ (FinEnum.card σ))))

instance : Std.LawfulEqCmp (Ord.compare (α := CMvMonomial σ)) :=
  inferInstanceAs (Std.LawfulEqCmp (Ord.compare (α := Vector ℕ (FinEnum.card σ))))

end Instances

namespace CMvMonomial

variable {m m₁ m₂ : CMvMonomial σ}

@[ext, grind ext]
protected theorem ext (h : (i : Nat) → (_ : i < FinEnum.card σ) → m₁[i] = m₂[i]) : m₁ = m₂ :=
  Vector.ext h

/-- The total degree of a monomial (sum of all exponents). -/
def totalDegree (m : CMvMonomial σ) : ℕ := m.sum

/-- The degree of the variable `i` in the monomial. -/
def degreeOf (m : CMvMonomial σ) (i : σ) : ℕ := m.get (FinEnum.equiv i)

/-- The zero monomial (all exponents are zero). -/
def zero : CMvMonomial σ := Vector.replicate (FinEnum.card σ) 0

instance : Zero (CMvMonomial σ) := ⟨zero⟩

/-- Monomial multiplication (adds exponents element-wise). -/
def add : CMvMonomial σ → CMvMonomial σ → CMvMonomial σ :=
  Vector.zipWith .add

instance : Add (CMvMonomial σ) := ⟨add⟩

@[simp]
lemma add_zero : m + 0 = m := by unfold_projs; dsimp [add, zero, CMvMonomial]; grind

/-- Check if $m_1$ divides $m_2$ (true if all exponents of $m_1$ are $\le$ those of $m_2$). -/
def divides (m₁ m₂ : CMvMonomial σ) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)

instance : Dvd (CMvMonomial σ) := ⟨fun m₁ m₂ ↦ divides m₁ m₂⟩

instance : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

/--
  The monomial division $m_1 / m_2$ (subtracts exponents element-wise).

  The result makes sense assuming  `m₂ | m₁`.
-/
def div (m₁ m₂ : CMvMonomial σ) : CMvMonomial σ :=
  Vector.zipWith Nat.sub m₁ m₂

instance : Div (CMvMonomial σ) := ⟨div⟩

/-- Convert a `CMvMonomial` to a `Finsupp`. -/
def toFinsupp (m : CMvMonomial σ) : σ →₀ ℕ :=
  ⟨Finset.univ.filter (fun i => m.get (FinEnum.equiv i) ≠ 0),
   fun i => m.get (FinEnum.equiv i),
   by intro i; simp⟩

/-- Convert a `Finsupp` to a `CMvMonomial`. -/
def ofFinsupp (m : σ →₀ ℕ) : CPoly.CMvMonomial σ := Vector.ofFn (fun k => m (FinEnum.equiv.symm k))

@[grind =, simp]
theorem ofFinsupp_toFinsupp : ofFinsupp m.toFinsupp = m := by
  unfold ofFinsupp
  ext i hi
  erw [Vector.getElem_ofFn]
  simp only [toFinsupp, Finsupp.coe_mk, Equiv.apply_symm_apply]
  rfl

@[grind =, simp]
theorem toFinsupp_ofFinsupp {m : σ →₀ ℕ} : (ofFinsupp m).toFinsupp = m := by
  ext i
  simp only [toFinsupp, ofFinsupp, Finsupp.coe_mk]
  rw [Vector.get_ofFn, Equiv.symm_apply_apply]

lemma injective_ofFinsupp : Function.Injective (ofFinsupp (σ := σ)) :=
  Function.HasLeftInverse.injective ⟨toFinsupp, fun _ ↦ toFinsupp_ofFinsupp⟩

lemma injective_toFinsupp : Function.Injective (toFinsupp (σ := σ)) :=
  Function.HasLeftInverse.injective ⟨ofFinsupp, fun _ ↦ ofFinsupp_toFinsupp⟩

def equivFinsupp : CMvMonomial σ ≃ (σ →₀ ℕ) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv := fun _ ↦ ofFinsupp_toFinsupp
  right_inv := fun _ ↦ toFinsupp_ofFinsupp

@[simp, grind =]
lemma map_mul {m₁ m₂ : Multiplicative (σ →₀ ℕ)} :
    ofFinsupp (m₁ * m₂) = (ofFinsupp m₁) + (ofFinsupp m₂) := by
  unfold_projs; ext
  erw [Vector.getElem_ofFn, Vector.getElem_zipWith]
  simp [Multiplicative.toAdd, Multiplicative.ofAdd, ofFinsupp]

@[simp, grind =]
theorem ofFinsupp_zero : ofFinsupp (0 : σ →₀ ℕ) = (zero : CMvMonomial σ) := by
  unfold ofFinsupp zero
  ext i hi
  erw [Vector.getElem_ofFn, Vector.getElem_replicate]
  simp

end CMvMonomial

abbrev MonoR (σ : Type*) [FinEnum σ] (R : Type*) := CMvMonomial σ × R

namespace MonoR

variable {σ : Type*} [FinEnum σ] {R : Type*}

instance [DecidableEq R] : DecidableEq (CMvMonomial σ × R) :=
  instDecidableEqProd

section

instance [Repr R] : Repr (MonoR σ R) where
  reprPrec
  | (m, c), _ => repr c ++ " * " ++ repr m

@[simp, grind=]
def C (c : R) : MonoR σ R := (CMvMonomial.zero, c)

variable [CommSemiring R] [HMod R R R] [BEq R]

def divides (t₁ t₂ : MonoR σ R) : Bool :=
  t₁.1 ∣ t₂.1 ∧ t₁.2 % t₂.2 == 0

instance : Dvd (MonoR σ R) := ⟨fun t₁ t₂ ↦ divides t₁ t₂⟩

instance {t₁ t₂ : MonoR σ R} : Decidable (t₁ ∣ t₂) := by
  dsimp [(·∣·)]
  infer_instance

end

def evalMonomial {R : Type*} {σ : Type*} [FinEnum σ] [CommSemiring R] :
    (σ → R) → CMvMonomial σ → R :=
  fun vals m => ∏ (i : σ), (vals i) ^ m.get (FinEnum.equiv i)

end MonoR

end CPoly

@[reducible]
alias Finsupp.ofCMvMonomial := CPoly.CMvMonomial.toFinsupp

@[reducible]
alias Finsupp.toCMvMonomial := CPoly.CMvMonomial.ofFinsupp
