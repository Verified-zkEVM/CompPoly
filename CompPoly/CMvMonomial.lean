import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Lattice
namespace CPoly

/--
  Monomial in `n` variables.
  - `#v[e₀, e₁, e₂]` denotes X₀^e₀ * X₁^e₁ * X₂^e₂
-/
abbrev CMvMonomial (n : ℕ) : Type := Vector ℕ n

syntax "#m[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#m[ $elems,* ]) => `(#v[ $elems,* ])

instance {n : ℕ} : Repr (CMvMonomial n) where
  reprPrec m _ :=
    let indexed := (Array.range m.size).zip m.1
    let toFormat : Std.ToFormat (ℕ × ℕ) :=
      ⟨λ (i, p) ↦ "X" ++ repr i ++ "^" ++ repr p⟩
    @Std.Format.joinSep _ toFormat indexed.toList " * "

namespace CMvMonomial

variable {n : ℕ}

def extend (n' : ℕ) (m : CMvMonomial n) : CMvMonomial (max n n') :=
  cast (have : n + (n' - n) = n ⊔ n' :=
          if h : n' ≤ n
          then by simp [h]
          else by have := le_of_lt (not_le.1 h)
                  rw [sup_of_le_right this, Nat.add_sub_cancel' this]
        this ▸ rfl)
       (m.append (Vector.replicate (n' - n) 0))

def totalDegree (m : CMvMonomial n) : ℕ := m.sum

def one : CMvMonomial n := Vector.replicate n 0

instance : One (CMvMonomial n) := ⟨one⟩

def mul : CMvMonomial n → CMvMonomial n → CMvMonomial n :=
  Vector.zipWith .add

instance : Mul (CMvMonomial n) := ⟨mul⟩

lemma mul_one {m : CMvMonomial n} : m * one = m := by
  unfold one
  unfold_projs
  unfold CMvMonomial.mul
  grind

def divides (m₁ : CMvMonomial n) (m₂ : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith (flip Nat.ble) m₁ m₂) (· == true)

instance : Dvd (CMvMonomial n) := ⟨fun m₁ m₂ ↦ divides m₁ m₂⟩ -- Do not eta.

instance {m₁ m₂ : CMvMonomial n} : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

/--
  The polynomial `m₁ / m₂`.

  The result makes sense assuming  `m₁ | m₂`.
-/
def div (m₁ m₂ : CMvMonomial n) : CMvMonomial n :=
  Vector.zipWith Nat.sub m₁ m₂

instance : Div (CMvMonomial n) := ⟨div⟩

instance {m₁ m₂ : CMvMonomial n} : Decidable (m₁ ∣ m₂) := by dsimp [(·∣·)]; infer_instance

def toFinsupp (m : CPoly.CMvMonomial n) : Fin n →₀ ℕ :=
  ⟨{i : Fin n | m[i] ≠ 0}, m.get, by aesop⟩

def ofFinsupp (m : Fin n →₀ ℕ) : CPoly.CMvMonomial n := Vector.ofFn m

@[grind=, simp]
theorem ofFinsupp_toFinsupp {m : CMvMonomial n} : ofFinsupp m.toFinsupp = m := by
  ext i hi; aesop (add simp CMvMonomial.ofFinsupp)

@[grind=, simp]
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

lemma map_mul {n : ℕ} {m₁ m₂ : Multiplicative (Fin n →₀ ℕ)} :
  CMvMonomial.ofFinsupp (n := n) (m₁ * m₂) =
    CMvMonomial.mul (CMvMonomial.ofFinsupp m₁) (CMvMonomial.ofFinsupp m₂)
:= by
  unfold_projs
  ext
  simp [Multiplicative.toAdd, Multiplicative.ofAdd, CMvMonomial.mul, ofFinsupp]

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

@[grind=]
def C (c : R) : MonoR n R := (CMvMonomial.one, c)

variable [CommSemiring R]

def divides [HMod R R R] [BEq R] (t₁ t₂ : MonoR n R) : Bool :=
  t₁.1 ∣ t₂.1 ∧ t₁.2 % t₂.2 == 0

instance [HMod R R R] [BEq R] : Dvd (MonoR n R) := ⟨fun t₁ t₂ ↦ divides t₁ t₂⟩ -- Do not eta.

instance [HMod R R R] [BEq R] {t₁ t₂ : MonoR n R} : Decidable (t₁ ∣ t₂) := by
  dsimp [(·∣·)]
  infer_instance

end

end MonoR

end CPoly

@[reducible]
alias Finsupp.ofCMvMonomial := CPoly.CMvMonomial.toFinsupp

@[reducible]
alias Finsupp.toCMvMonomial := CPoly.CMvMonomial.ofFinsupp
