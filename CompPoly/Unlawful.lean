import CompPoly.CMvMonomial
import CompPoly.Wheels
import Mathlib.Algebra.Lie.OfAssociative
import Std.Classes.Ord.Vector
import ExtTreeMapLemmas.ExtTreeMap

attribute [local instance 5] instDecidableEqOfLawfulBEq

namespace CPoly

open Std

/--
  Polynomial in `n` variables with coefficients in `R`.
-/
@[grind =]
def Unlawful (n : ℕ) (R : Type) : Type :=
  Std.ExtTreeMap (CMvMonomial n) R (Ord.compare (α := CMvMonomial n))

variable {n : ℕ} {R : Type}

instance : EmptyCollection (Unlawful n R) := ⟨(∅ : Std.ExtTreeMap (CMvMonomial n) R compare)⟩

instance : Singleton (MonoR n R) (Unlawful n R) :=
  inferInstanceAs (Singleton (MonoR n R) (Std.ExtTreeMap (CMvMonomial n) R compare))

instance : Insert (MonoR n R) (Unlawful n R) :=
  inferInstanceAs (Insert (MonoR n R) (Std.ExtTreeMap (CMvMonomial n) R compare))

instance : LawfulSingleton (MonoR n R) (Unlawful n R) :=
  inferInstanceAs (LawfulSingleton (MonoR n R) (Std.ExtTreeMap (CMvMonomial n) R compare))

instance : Membership (CMvMonomial n) (Unlawful n R) :=
  inferInstanceAs (Membership (CMvMonomial n) (Std.ExtTreeMap (CMvMonomial n) R compare))

@[default_instance]
instance (priority := high) : GetElem (Unlawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (GetElem (Std.ExtTreeMap (CMvMonomial n) R compare) (CMvMonomial n) R (fun lp m ↦ m ∈ lp))

instance : GetElem? (Unlawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (GetElem? (Std.ExtTreeMap (CMvMonomial n) R compare) (CMvMonomial n) R (fun lp m ↦ m ∈ lp))

instance : LawfulGetElem (Unlawful n R) (CMvMonomial n) R (fun lp m ↦ m ∈ lp) :=
  inferInstanceAs
    (LawfulGetElem (Std.ExtTreeMap (CMvMonomial n) R compare) (CMvMonomial n) R (fun lp m ↦ m ∈ lp))

namespace Unlawful

attribute [grind ext] Std.ExtTreeMap.ext_getElem?

@[ext, grind ext]
lemma ext_getElem? {n R} {t₁ t₂ : Unlawful n R}
  (h : ∀ (k : CMvMonomial n), t₁[k]? = t₂[k]?) : t₁ = t₂ :=
  Std.ExtTreeMap.ext_getElem? h

variable {n : ℕ} {R : Type}

@[simp, grind =]
def ofList (l : List (CMvMonomial n × R)) : Unlawful n R := ExtTreeMap.ofList l compare

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

@[grind =]
def C [BEq R] [LawfulBEq R] [Zero R] (c : R) : Unlawful n R :=
  if c = 0 then ∅ else .ofList [MonoR.C c]

section

variable {m : ℕ} [Zero R] {x : CMvMonomial n}

section

variable [BEq R] [LawfulBEq R]

instance : OfNat (Unlawful n R) 0 := ⟨C 0⟩

instance [NatCast R] [NeZero m] : OfNat (Unlawful n R) m := ⟨C m⟩

@[simp, grind =]
lemma C_zero : C (n := n) (0 : R) = 0 := rfl

end

@[simp, grind =]
lemma C_zero' : C (n := n) (0 : ℕ) = 0 := rfl

@[simp, grind =]
lemma zero_eq_zero : (Zero.zero : R) = 0 := rfl

lemma zero_eq_empty [BEq R] [LawfulBEq R] : (0 : Unlawful n R) = ∅ := by unfold_projs; simp [C]

@[simp, grind]
lemma not_mem_C_zero : x ∉ C 0 := by grind

section

variable [BEq R] [LawfulBEq R]

@[simp, grind]
lemma not_mem_zero : x ∉ (0 : Unlawful n R) := by rw [←C_zero]; grind

@[simp, grind]
lemma isNoZeroCoef_zero : isNoZeroCoef (n := n) (R := R) 0 := by rw [←C_zero]; grind

end

end

def add [Add R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂

instance [Add R] : Add (Unlawful n R) := ⟨add⟩

@[grind=]
protected lemma grind_add_skip [Add R] {p₁ p₂ : Unlawful n R} :
  p₁ + p₂ = p₁.mergeWith (fun _ c₁ c₂ ↦ c₁ + c₂) p₂ := rfl

def addMonoR [Add R] (p : Unlawful n R) (term : MonoR n R) : Unlawful n R :=
  p + .ofList [term]

def mul₀ [Mul R] (t : MonoR n R) (p : Unlawful n R) : Unlawful n R :=
  .ofList (p.toList.map fun (k, v) ↦ (t.1+k, t.2*v))

attribute [grind=] ExtTreeMap.ofList_eq_empty_iff List.map_eq_nil_iff ExtTreeMap.toList_eq_nil_iff

@[simp, grind=]
lemma mul₀_zero [Zero R] [BEq R] [LawfulBEq R] [Mul R] {t : MonoR n R} : mul₀ t 0 = 0 := by
  unfold mul₀
  grind

def mul [Mul R] [Add R] [Zero R] [BEq R] [LawfulBEq R] (p₁ p₂ : Unlawful n R) : Unlawful n R :=
  p₁.foldl (init := 0)
    fun p m₁ c₁ ↦
      (p₂.foldl (init := 0) fun p' m₂ c₂ ↦ {(m₁ + m₂, c₁ * c₂)} + p') + p

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


@[simp, grind =]
lemma filter_get {R : Type} [BEq R] [LawfulBEq R] {v : R} {m : CMvMonomial n} (a : Unlawful n R) :
    (ExtTreeMap.filter (fun _ c => c != v) a)[m]?.getD v = a[m]?.getD v := by
  grind

lemma add_getD? [CommSemiring R] {m : CMvMonomial n} {p q : Unlawful n R} :
  (p.add q)[m]?.getD 0 = p[m]?.getD 0 + q[m]?.getD 0
:= by
  rw [Unlawful.add]
  by_cases in_p : m ∈ p <;> by_cases in_q : m ∈ q
  · erw [ExtTreeMap.mergeWith₀ in_p in_q, Option.getD_some]
    change p[m] + q[m] = p[m]?.getD 0 + q[m]?.getD 0
    grind
  · erw [ExtTreeMap.mergeWith₁ in_p in_q, show q[m]?.getD 0 = 0 by grind, add_zero]
    grind
  · erw [ExtTreeMap.mergeWith₂ in_p in_q, show p[m]?.getD 0 = 0 by grind, zero_add]
    grind
  · erw [
      ExtTreeMap.mergeWith₃ in_p in_q,
      show p[m]?.getD 0 = 0 by grind,
      show q[m]?.getD 0 = 0 by grind
    ]
    grind

end Unlawful

end CPoly
