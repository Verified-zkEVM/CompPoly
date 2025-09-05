import CompPoly.CMvMonomial
import CompPoly.Wheels
import Mathlib.Algebra.Lie.OfAssociative
import Std.Classes.Ord.Vector

attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

/--
  Polynomial in `n` variables with coefficients in `R`.
-/
abbrev Unlawful (n : ℕ) (R : Type) : Type :=
  Std.ExtTreeMap (CMvMonomial n) R

namespace Unlawful

variable {n : ℕ} {R : Type}

def extend (n' : ℕ) (p : Unlawful n R) : Unlawful (n ⊔ n') R :=
  .ofList (p.keys.map (CMvMonomial.extend n') |>.zip p.values)

abbrev isNoZeroCoef [Zero R] (p : Unlawful n R) : Prop := ∀ (m : CMvMonomial n), p[m]? ≠ some 0

def toFinset [DecidableEq R] (p : Unlawful n R) : Finset (CMvMonomial n × R) :=
  p.toList.toFinset

abbrev monomials (p : Unlawful n R) : List (CMvMonomial n) :=
  p.keys

@[simp]
lemma mem_monomials {m : CMvMonomial n} {up : Unlawful n R} :
  m ∈ up.monomials ↔ m ∈ up := ExtTreeMap.mem_keys

instance [Repr R] : Repr (Unlawful n R) where
  reprPrec p _ :=
    if p.isEmpty then "0" else
    let toFormat : Std.ToFormat (CMvMonomial n × R) :=
      ⟨λ (m, c) => repr c ++ " * " ++ repr m⟩
    @Std.Format.joinSep _ toFormat p.toList " + "

@[grind=]
def C [BEq R] [LawfulBEq R] [Zero R] (c : R) : Unlawful n R :=
  if c = 0 then Std.ExtTreeMap.empty else .ofList [MonoR.C c]

section

variable {m : ℕ} [Zero R] {x : CMvMonomial n}

section

variable [BEq R] [LawfulBEq R]

instance : OfNat (Unlawful n R) 0 := ⟨C 0⟩

instance [NatCast R] [NeZero m] : OfNat (Unlawful n R) m := ⟨C m⟩

@[simp, grind _=_]
lemma C_zero : C (n := n) (0 : R) = 0 := rfl

end

@[simp, grind]
lemma C_zero' : C (n := n) (0 : ℕ) = 0 := rfl

@[simp, grind _=_]
lemma zero_eq_zero : (Zero.zero : R) = 0 := rfl

@[grind←]
lemma zero_eq_empty [BEq R] [LawfulBEq R] : (0 : Unlawful n R) = ∅ := by unfold_projs; simp [C]

@[simp, grind]
lemma not_mem_C_zero : x ∉ C 0 := by grind

section

variable [BEq R] [LawfulBEq R]

@[simp, grind]
lemma not_mem_zero : x ∉ (0 : Unlawful n R) := by grind

@[simp, grind]
lemma isNoZeroCoef_zero : isNoZeroCoef (n := n) (R := R) 0 := fun _ ↦ by simp

end

end

def add [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (Unlawful n R) := ⟨add⟩

@[grind=]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Unlawful n R} :
  p₁ + p₂ = p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂ := rfl

def addMonoR [Add R] (p : Unlawful n R) (term : MonoR n R) : Unlawful n R :=
  p + (ExtTreeMap.ofList [term] : Unlawful n R)

def mul₀ [Mul R] (t : MonoR n R) (p : Unlawful n R) : Unlawful n R :=
  ExtTreeMap.ofList (p.toList.map fun (k, v) ↦ (t.1*k, t.2*v))

attribute [grind=] ExtTreeMap.ofList_eq_empty_iff List.map_eq_nil_iff ExtTreeMap.toList_eq_nil_iff

@[simp, grind=]
lemma mul₀_zero [Zero R] [BEq R] [LawfulBEq R] [Mul R] {t : MonoR n R} : mul₀ t 0 = 0 := by
  unfold mul₀
  grind

def mul [Mul R] [Add R] [Zero R] [BEq R] [LawfulBEq R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.foldl (init := 0)
    fun p m₁ c₁ ↦
      (p₂.foldl (init := 0) fun p' m₂ c₂ ↦ {(m₁ * m₂, c₁ * c₂)} + p') + p

instance [BEq R] [LawfulBEq R] [Mul R] [Add R] [Zero R] : Mul (Unlawful n R) := ⟨mul⟩

def neg [Neg R] (p : Unlawful n R) : Unlawful n R :=
  p.map fun _ v ↦ -v

instance [Neg R] : Neg (Unlawful n R) := ⟨neg⟩

def sub [Neg R] [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  Unlawful.add p₁ (-p₂)

instance [Neg R] [Add R] : Sub (Unlawful n R) := ⟨sub⟩

def leadingTerm? : Unlawful n R → Option (MonoR n R) :=
  ExtTreeMap.maxEntry?

def leadingMonomial? : Unlawful n R → Option (CMvMonomial n) :=
  .map Prod.fst ∘ Unlawful.leadingTerm?

instance instDecidableEq [DecidableEq R] : DecidableEq (Unlawful n R) := fun x y ↦
  if h : x.toList = y.toList
  then Decidable.isTrue (ExtTreeMap.ext_toList (h ▸ List.perm_rfl))
  else Decidable.isFalse (by grind)

def coeff {R : Type} {n : ℕ} [Zero R] (m : CMvMonomial n) (p : Unlawful n R) : R :=
  p[m]?.getD 0

lemma filter_get {R : Type} [BEq R] [LawfulBEq R] {v : R} {m : CMvMonomial n} (a : Unlawful n R) :
    (ExtTreeMap.filter (fun _ c => c != v) a)[m]?.getD v = a[m]?.getD v := by
  by_cases h : m ∈ a
  · by_cases h' : a[m] = v
    · erw [ExtTreeMap.filter_not_pred h (by simp [h'])]
      have : a[m]? = .some v := by
        aesop
      rw [this]
      simp
    · erw [ExtTreeMap.filter_mem h (by simp [h'])]
      have : a[m]?.getD v = a[m] := by
        have : a[m]? = some a[m] := by
          simp [h]
        rw [this]
        simp
      rw [this]
      simp
  · simp [h, ExtTreeMap.filter_not_mem h]

lemma add_getD? [CommSemiring R] {m : CMvMonomial n} {p q : Unlawful n R} :
  (p.add q)[m]?.getD 0 = p[m]?.getD 0 + q[m]?.getD 0
:= by
  rw [Unlawful.add]
  by_cases in_p : m ∈ p <;> by_cases in_q : m ∈ q
  · simp [ExtTreeMap.mergeWith₀ in_p in_q]
    by_cases sum_0 : p[m] + q[m] != 0
      <;> by_cases pm_0 : p[m] = 0 <;> by_cases qm_0 : q[m] = 0
      <;> grind [add_comm]
  · simp [ExtTreeMap.mergeWith₁ in_p in_q]
    by_cases p[m] = 0
    · aesop
    · rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at in_p
      rcases in_p with ⟨c₁, in_p⟩
      simp [in_p]
      by_cases c₁_eq_0 : c₁ = 0 <;> simp [c₁_eq_0, in_q]
  · simp [ExtTreeMap.mergeWith₂ in_p in_q]
    by_cases q[m] = 0
    · aesop
    · rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at in_q
      rcases in_q with ⟨c₁, in_q⟩
      simp [in_q]
      by_cases c₁_eq_0 : c₁ = 0 <;> simp [c₁_eq_0, in_p]
  · simp [ExtTreeMap.mergeWith₃ in_p in_q]
    aesop

end Unlawful

end CPoly
