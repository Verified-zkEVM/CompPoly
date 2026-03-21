/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Quang Dao
-/
import Batteries.Data.Array.Merge
import Batteries.Data.Vector.Basic
import Init.Data.Order.Ord
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Lattice

/-!
# Computable monomials

Sparse computable monomials of the form `∏ i, Xᵢ ^ eᵢ`, stored as canonical sparse arrays of
`(variable, exponent)` pairs.
-/

namespace CPoly

open Std

/-- Local helper for deriving `DecidableEq` from a lawful comparator. -/
def decEqOfLawfulEqOrd (α : Type) [Ord α] [LawfulEqOrd α] : DecidableEq α := fun a b =>
  if h : compare a b = .eq then
    .isTrue (LawfulEqOrd.eq_of_compare h)
  else
    .isFalse (fun hab => h <| hab ▸ compare_self)

/-- Canonical sparse monomial entries. -/
abbrev MonomialEntry (σ : Type) := σ × Nat

instance [Ord σ] : Ord (MonomialEntry σ) where
  compare := compareLex (compareOn Prod.fst) (compareOn Prod.snd)

instance [Ord σ] [TransOrd σ] : TransOrd (MonomialEntry σ) :=
  inferInstanceAs <| TransOrd (σ × Nat)

instance [Ord σ] [LawfulEqOrd σ] : LawfulEqOrd (MonomialEntry σ) :=
  inferInstanceAs <| LawfulEqOrd (σ × Nat)

/-- Raw sparse monomial storage. Missing variables are understood to have exponent `0`. -/
structure RawMonomial (σ : Type) where
  totalDegree : Nat
  entries : Array (MonomialEntry σ)

namespace RawMonomial

variable {σ : Type}

/-- The sum of all stored exponents. -/
def sumEntries (entries : Array (MonomialEntry σ)) : Nat :=
  entries.foldl (fun acc entry => acc + entry.2) 0

/-- Compare monomial entries only by their variable key. -/
def keyOrd [Ord σ] : Ord (MonomialEntry σ) where
  compare a b := compare a.1 b.1

/-- Normalize sparse entries by sorting by variable, merging duplicates, and dropping zero entries. -/
def normalizeEntries [Ord σ] (entries : Array (MonomialEntry σ)) : Array (MonomialEntry σ) :=
  letI : Ord (MonomialEntry σ) := keyOrd
  letI : BEq (MonomialEntry σ) := beqOfOrd
  (entries.qsortOrd.mergeAdjacentDups fun a b => (a.1, a.2 + b.2)).filter fun entry => entry.2 != 0

/-- Canonical normalization of a raw monomial. -/
def normalize [Ord σ] (m : RawMonomial σ) : RawMonomial σ :=
  let entries := normalizeEntries m.entries
  { totalDegree := sumEntries entries, entries }

/-- A raw monomial is lawful iff it is in the image of normalization. -/
def IsLawful [Ord σ] (m : RawMonomial σ) : Prop :=
  ∃ raw, normalize raw = m

end RawMonomial

/-- Canonical computable monomials over an arbitrary ordered variable type. -/
structure CMvMonomial (σ : Type) [Ord σ] where
  toRaw : RawMonomial σ
  lawful : RawMonomial.IsLawful toRaw

/-- Finite-arity convenience syntax for `CMvMonomial (Fin n)`. -/
syntax "#m[" withoutPosition(term,*,?) "]" : term

variable {σ τ : Type}

namespace CMvMonomial

section Instances

instance [Ord σ] : Coe (CMvMonomial σ) (RawMonomial σ) := ⟨CMvMonomial.toRaw⟩

instance [Ord σ] [Repr σ] : Repr (CMvMonomial σ) where
  reprPrec m _ :=
    let toFormat : Std.ToFormat (MonomialEntry σ) :=
      ⟨fun (i, e) => "X" ++ repr i ++ "^" ++ repr e⟩
    @Std.Format.joinSep _ toFormat m.toRaw.entries.toList " * "

instance [Ord σ] : Ord (CMvMonomial σ) where
  compare := compareOn (fun m : CMvMonomial σ => m.toRaw.entries)

instance [Ord σ] [TransOrd σ] : TransOrd (CMvMonomial σ) :=
  inferInstanceAs <| TransCmp (compareOn (fun m : CMvMonomial σ => m.toRaw.entries))

end Instances

/-- Construct a lawful monomial from raw storage by normalization. -/
def ofRaw [Ord σ] (m : RawMonomial σ) : CMvMonomial σ :=
  ⟨RawMonomial.normalize m, ⟨m, rfl⟩⟩

/-- Build a monomial from explicit sparse entries. -/
def ofEntries [Ord σ] (entries : Array (MonomialEntry σ)) : CMvMonomial σ :=
  ofRaw { totalDegree := 0, entries }

/-- The canonical sparse entries. -/
def entries [Ord σ] (m : CMvMonomial σ) : Array (MonomialEntry σ) :=
  m.toRaw.entries

/-- The cached total degree. -/
def totalDegree [Ord σ] (m : CMvMonomial σ) : Nat :=
  m.toRaw.totalDegree

theorem totalDegree_eq_sumEntries [Ord σ] (m : CMvMonomial σ) :
    m.totalDegree = RawMonomial.sumEntries m.entries := by
  rcases m with ⟨m, ⟨raw, hraw⟩⟩
  cases hraw
  rfl

/-- Degree lookup in a single variable. Missing variables have degree `0`. -/
def degreeOf [Ord σ] (m : CMvMonomial σ) (i : σ) : Nat :=
  match Array.binSearch (α := MonomialEntry σ) m.entries ((i, (0 : Nat)) : MonomialEntry σ)
      (fun (a b : MonomialEntry σ) => (compare a.1 b.1).isLT) with
  | some entry => entry.2
  | none => 0

/-- The zero monomial. -/
def zero [Ord σ] : CMvMonomial σ :=
  ofEntries #[]

instance [Ord σ] : Zero (CMvMonomial σ) := ⟨zero⟩

/-- A single-variable monomial. -/
def single [Ord σ] (i : σ) (e : Nat) : CMvMonomial σ :=
  ofEntries #[ (i, e) ]

private def mergeAddEntries [Ord σ] (xs ys : Array (MonomialEntry σ)) : Array (MonomialEntry σ) :=
  letI : Ord (MonomialEntry σ) := RawMonomial.keyOrd
  Array.mergeDedupWith xs ys fun a b => (a.1, a.2 + b.2)

/-- Monomial multiplication, implemented by exponent addition on sparse support. -/
def add [Ord σ] (m₁ m₂ : CMvMonomial σ) : CMvMonomial σ :=
  ofEntries <| mergeAddEntries m₁.entries m₂.entries

instance [Ord σ] : Add (CMvMonomial σ) := ⟨add⟩

private def dividesEntries [Ord σ] (xs ys : Array (MonomialEntry σ)) : Bool :=
  go 0 0
where
  go (i j : Nat) : Bool :=
    if hi : i < xs.size then
      if hj : j < ys.size then
        let x := xs[i]
        let y := ys[j]
        match compare x.1 y.1 with
        | .lt => false
        | .eq => (x.2 <= y.2) && go (i + 1) (j + 1)
        | .gt => go i (j + 1)
      else
        false
    else
      true
  termination_by xs.size - i + (ys.size - j)

/-- Check if `m₁` divides `m₂`. -/
def divides [Ord σ] (m₁ m₂ : CMvMonomial σ) : Bool :=
  dividesEntries m₁.entries m₂.entries

instance [Ord σ] : Dvd (CMvMonomial σ) := ⟨fun m₁ m₂ => divides m₁ m₂⟩

instance [Ord σ] {m₁ m₂ : CMvMonomial σ} : Decidable (m₁ ∣ m₂) := by
  dsimp [(· ∣ ·)]
  infer_instance

private def divEntries [Ord σ] (xs ys : Array (MonomialEntry σ)) : Array (MonomialEntry σ) :=
  go 0 0 #[]
where
  go (i j : Nat) (acc : Array (σ × Nat)) : Array (σ × Nat) :=
    if hi : i < xs.size then
      let x := xs[i]
      if hj : j < ys.size then
        let y := ys[j]
        match compare x.1 y.1 with
        | .lt => go (i + 1) j (acc.push x)
        | .eq =>
            let e := x.2 - y.2
            let acc := if e = 0 then acc else acc.push (x.1, e)
            go (i + 1) (j + 1) acc
        | .gt => go i (j + 1) acc
      else
        acc ++ xs[i:]
    else
      acc
  termination_by xs.size - i + (ys.size - j)

/-- Monomial division, assuming the divisor divides the dividend. -/
def div [Ord σ] (m₁ m₂ : CMvMonomial σ) : CMvMonomial σ :=
  ofEntries <| divEntries m₁.entries m₂.entries

instance [Ord σ] : Div (CMvMonomial σ) := ⟨div⟩

/-- Convert a computable monomial to a `Finsupp`. -/
noncomputable def toFinsupp [Ord σ] [LawfulEqOrd σ] (m : CMvMonomial σ) : σ →₀ ℕ :=
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  m.entries.foldl (fun acc entry => acc + Finsupp.single entry.1 entry.2) 0

/-- Convert a `Finsupp` to a computable monomial. -/
noncomputable def ofFinsupp [Ord σ] [LawfulEqOrd σ] (m : σ →₀ ℕ) : CMvMonomial σ :=
  letI : DecidableEq σ := decEqOfLawfulEqOrd _
  ofEntries <| m.support.toList.toArray.map fun i => (i, m i)

/-- Rename variables in a monomial, merging collisions in the target support. -/
def rename [Ord σ] [Ord τ] (f : σ → τ) (m : CMvMonomial σ) : CMvMonomial τ :=
  ofEntries <| m.entries.map fun entry => (f entry.1, entry.2)

/-- Finite-arity convenience constructor from a dense exponent vector. -/
def ofExponents {n : ℕ} (exps : Vector ℕ n) : CMvMonomial (Fin n) :=
  ofEntries <| (Array.finRange n).zip exps.1 |>.filter fun entry => entry.2 != 0

open Lean in
macro_rules
  | `(#m[$elems,*]) => `(CPoly.CMvMonomial.ofExponents #v[$elems,*])

end CMvMonomial

instance [Ord σ] [LawfulEqOrd σ] : LawfulEqOrd (CMvMonomial σ) where
  compare_self := by
    intro a
    simpa [Ord.compare, compareOn] using
      (ReflOrd.compare_self (α := Array (MonomialEntry σ)) (a := a.toRaw.entries))
  eq_of_compare {a b} h := by
    have hEntries : a.toRaw.entries = b.toRaw.entries := LawfulEqOrd.eq_of_compare h
    have hDeg : a.toRaw.totalDegree = b.toRaw.totalDegree := by
      calc
        a.toRaw.totalDegree = RawMonomial.sumEntries a.toRaw.entries := CMvMonomial.totalDegree_eq_sumEntries a
        _ = RawMonomial.sumEntries b.toRaw.entries := by simpa [hEntries]
        _ = b.toRaw.totalDegree := (CMvMonomial.totalDegree_eq_sumEntries b).symm
    cases a with
    | mk a ha =>
        cases b with
        | mk b hb =>
            cases a
            cases b
            cases hEntries
            cases hDeg
            have hproof : ha = hb := Subsingleton.elim _ _
            cases hproof
            rfl

instance [Ord σ] [LawfulEqOrd σ] : DecidableEq (CMvMonomial σ) :=
  decEqOfLawfulEqOrd _

abbrev MonoR (σ : Type) [Ord σ] (R : Type) := CMvMonomial σ × R

namespace MonoR

variable {R : Type}

instance [Ord σ] [LawfulEqOrd σ] [DecidableEq R] : DecidableEq (CMvMonomial σ × R) :=
  instDecidableEqProd

section

instance [Ord σ] [Repr σ] [Repr R] : Repr (MonoR σ R) where
  reprPrec
  | (m, c), _ => repr c ++ " * " ++ repr m

@[simp, grind =]
def C [Ord σ] (c : R) : MonoR σ R := (CMvMonomial.zero, c)

variable [Ord σ] [CommSemiring R] [HMod R R R] [BEq R]

def divides (t₁ t₂ : MonoR σ R) : Bool :=
  t₁.1 ∣ t₂.1 ∧ t₁.2 % t₂.2 == 0

instance : Dvd (MonoR σ R) := ⟨fun t₁ t₂ => divides t₁ t₂⟩

instance {t₁ t₂ : MonoR σ R} : Decidable (t₁ ∣ t₂) := by
  dsimp [(· ∣ ·)]
  infer_instance

end

/-- Evaluate a monomial by multiplying only over its stored sparse support. -/
def evalMonomial {R : Type} [Ord σ] [CommSemiring R] : (σ → R) → CMvMonomial σ → R :=
  fun vals m => m.toRaw.entries.foldl (fun acc entry => acc * vals entry.1 ^ entry.2) 1

end MonoR

end CPoly

@[reducible]
alias Finsupp.ofCMvMonomial := CPoly.CMvMonomial.toFinsupp

@[reducible]
alias Finsupp.toCMvMonomial := CPoly.CMvMonomial.ofFinsupp
