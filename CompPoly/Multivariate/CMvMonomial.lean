import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Lattice
import Std.Classes.Ord.Vector

/-!
# Computable monomials

Monomials of the form `X₀ᵃ * X₁ᵇ * ... * Xₖᶻ`.

## Main definitions

* `CPoly.CMvMonomial
-/

namespace CPoly

/--
  Monomial in `n` variables.
  - `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂
-/
@[grind =]
def CMvMonomial (n : ℕ) : Type := Vector ℕ n

syntax "#m[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#m[$elems,*]) => `(#v[$elems,*])

variable {n : ℕ}

instance : Repr (CMvMonomial n) where
  reprPrec m _ :=
    let indexed := (Array.range m.size).zip m.1
    let toFormat : Std.ToFormat (ℕ × ℕ) :=
      ⟨λ (i, p) ↦ "X" ++ repr i ++ "^" ++ repr p⟩
    @Std.Format.joinSep _ toFormat indexed.toList " * "

section Instances

instance : GetElem (CMvMonomial n) ℕ ℕ fun _ idx ↦ idx < n :=
  inferInstanceAs (GetElem (Vector ℕ n) ℕ ℕ _)

instance : GetElem? (CMvMonomial n) ℕ ℕ fun _ idx ↦ idx < n :=
  inferInstanceAs (GetElem? (Vector ℕ n) ℕ ℕ _)

instance : DecidableEq (CMvMonomial n) :=
  inferInstanceAs (DecidableEq (Vector ℕ n))

instance : Ord (CMvMonomial n) :=
  inferInstanceAs (Ord (Vector ℕ n))

instance : Std.TransCmp (Ord.compare (α := CMvMonomial n)) :=
  inferInstanceAs (Std.TransCmp (Ord.compare (α := Vector ℕ n)))

instance : Std.LawfulEqCmp (Ord.compare (α := CMvMonomial n)) :=
  inferInstanceAs (Std.LawfulEqCmp (Ord.compare (α := Vector ℕ n)))

instance : GetElem (CMvMonomial n) ℕ ℕ fun _ idx ↦ idx < n :=
  inferInstanceAs (GetElem (Vector ℕ n) ℕ ℕ _)

instance : GetElem? (CMvMonomial n) ℕ ℕ fun _ idx ↦ idx < n :=
  inferInstanceAs (GetElem? (Vector ℕ n) ℕ ℕ _)

instance : DecidableEq (CMvMonomial n) :=
  inferInstanceAs (DecidableEq (Vector ℕ n))

instance : Ord (CMvMonomial n) :=
  inferInstanceAs (Ord (Vector ℕ n))

instance : Std.TransCmp (α := Vector ℕ n) (Ord.compare (α := CMvMonomial n)) :=
  inferInstanceAs (Std.TransCmp (Ord.compare (α := Vector ℕ n)))

instance : Std.LawfulEqCmp (α := Vector ℕ n) (Ord.compare (α := CMvMonomial n)) :=
  inferInstanceAs (Std.LawfulEqCmp (Ord.compare (α := Vector ℕ n)))

instance : Std.TransCmp (α := CMvMonomial n) (Ord.compare (α := Vector ℕ n)) :=
  inferInstanceAs (Std.TransCmp (Ord.compare (α := Vector ℕ n)))

instance : Std.LawfulEqCmp (α := CMvMonomial n) (Ord.compare (α := Vector ℕ n)) :=
  inferInstanceAs (Std.LawfulEqCmp (Ord.compare (α := Vector ℕ n)))

end Instances

namespace CMvMonomial

variable {m m₁ m₂ : CMvMonomial n}

@[ext, grind ext]
protected theorem ext (h : (i : Nat) → (_ : i < n) → m₁[i] = m₂[i]) : m₁ = m₂ :=
  Vector.ext h

def extend (n' : ℕ) (m : CMvMonomial n) : CMvMonomial (max n n') :=
  cast (have : n + (n' - n) = n ⊔ n' :=
          if h : n' ≤ n
          then by simp [h]
          else by have := le_of_lt (not_le.1 h)
                  rw [sup_of_le_right this, Nat.add_sub_cancel' this]
        this ▸ rfl)
       (m.append (Vector.replicate (n' - n) 0))

def totalDegree (m : CMvMonomial n) : ℕ := m.sum

def degreeOf (m : CMvMonomial n) (i : Fin n) : ℕ := m.get i

def zero : CMvMonomial n := Vector.replicate n 0

instance : Zero (CMvMonomial n) := ⟨zero⟩

def add : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add

instance : Add (CMvMonomial n) := ⟨add⟩

@[simp]
lemma add_zero : m + 0 = m := by unfold_projs; dsimp [add, zero, CMvMonomial]; grind

def divides (m₁ m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)

instance : Dvd (CMvMonomial n) := ⟨fun m₁ m₂ ↦ divides m₁ m₂⟩

instance : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

/--
  The polynomial `m₁ / m₂`.

  The result makes sense assuming  `m₁ | m₂`.
-/
def div (m₁ m₂ : CMvMonomial n) : CMvMonomial n :=
  Vector.zipWith Nat.sub m₁ m₂

instance : Div (CMvMonomial n) := ⟨div⟩

instance : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

def toFinsupp (m : CMvMonomial n) : Fin n →₀ ℕ :=
  ⟨{i : Fin n | m[i] ≠ 0}, m.get, by aesop⟩

def ofFinsupp (m : Fin n →₀ ℕ) : CPoly.CMvMonomial n := Vector.ofFn m

@[grind =, simp]
theorem ofFinsupp_toFinsupp : ofFinsupp m.toFinsupp = m := by
  unfold toFinsupp ofFinsupp
  ext i hi
  erw [Vector.getElem_ofFn]
  rfl

@[grind =, simp]
theorem toFinsupp_ofFinsupp {m : Fin n →₀ ℕ} : (ofFinsupp m).toFinsupp = m := by
  ext i; aesop (add simp [CMvMonomial.toFinsupp, CMvMonomial.ofFinsupp, Vector.get])

lemma injective_ofFinsupp : Function.Injective (ofFinsupp (n := n)) :=
  Function.HasLeftInverse.injective ⟨toFinsupp, fun _ ↦ toFinsupp_ofFinsupp⟩

lemma injective_toFinsupp : Function.Injective (toFinsupp (n := n)) :=
  Function.HasLeftInverse.injective ⟨ofFinsupp, fun _ ↦ ofFinsupp_toFinsupp⟩

def equivFinsupp : CMvMonomial n ≃ (Fin n →₀ ℕ) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv := fun _ ↦ ofFinsupp_toFinsupp
  right_inv := fun _ ↦ toFinsupp_ofFinsupp

@[simp, grind =]
lemma map_mul {m₁ m₂ : Multiplicative (Fin n →₀ ℕ)} :
    ofFinsupp (m₁ * m₂) = (ofFinsupp m₁) + (ofFinsupp m₂) := by
  unfold_projs; ext
  erw [Vector.getElem_ofFn, Vector.getElem_zipWith]
  simp [Multiplicative.toAdd, Multiplicative.ofAdd, ofFinsupp]

end CMvMonomial

abbrev MonoR (n : ℕ) (R : Type) := CMvMonomial n × R

namespace MonoR

variable {n : ℕ} {R : Type}

instance [DecidableEq R] : DecidableEq (CMvMonomial n × R) :=
  instDecidableEqProd

section

instance [Repr R] : Repr (MonoR n R) where
  reprPrec
    | (m, c), _ => repr c ++ " * " ++ repr m

@[simp, grind=]
def C (c : R) : MonoR n R := (CMvMonomial.zero, c)

variable [CommSemiring R] [HMod R R R] [BEq R]

def divides (t₁ t₂ : MonoR n R) : Bool :=
  t₁.1 ∣ t₂.1 ∧ t₁.2 % t₂.2 == 0

instance : Dvd (MonoR n R) := ⟨fun t₁ t₂ ↦ divides t₁ t₂⟩

instance {t₁ t₂ : MonoR n R} : Decidable (t₁ ∣ t₂) := by
  dsimp [(·∣·)]
  infer_instance

end

def evalMonomial {R : Type} {n : ℕ} [CommSemiring R] : (Fin n → R) → CMvMonomial n → R :=
  fun vals m => ∏ (i : Fin n), (vals i) ^ m.get i

end MonoR

end CPoly

@[reducible]
alias Finsupp.ofCMvMonomial := CPoly.CMvMonomial.toFinsupp

@[reducible]
alias Finsupp.toCMvMonomial := CPoly.CMvMonomial.ofFinsupp
