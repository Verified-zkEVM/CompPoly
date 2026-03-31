/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi, Julian Sutherland, Andrei Burdușa, Dimitris Mitsios
-/
import Batteries.Data.Vector.Lemmas
import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Ring.Defs
import CompPoly.Multivariate.Lawful
import Batteries.Data.Vector.Basic

/-!
# `CMvPolynomial`/`MvPolynomial` Core

Core conversions between `CMvPolynomial` and `MvPolynomial`.
-/

open Std

namespace CPoly

open CMvPolynomial

section

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

def fromCMvPolynomial  (p : CMvPolynomial n R) : MvPolynomial (Fin n) R :=
  let support : List (Fin n →₀ ℕ) := p.monomials.map CMvMonomial.toFinsupp
  let toFun (f : Fin n →₀ ℕ) : R := p[CMvMonomial.ofFinsupp f]?.getD 0
  let mem_support_fun {a : Fin n →₀ ℕ} : a ∈ support ↔ toFun a ≠ 0 := by grind
  Finsupp.mk support.toFinset toFun (by simp [mem_support_fun])

noncomputable def toCMvPolynomial (p : MvPolynomial (Fin n) R) : CMvPolynomial n R :=
  let ⟨s, f, _⟩ := p
  let unlawful := .ofList <| s.toList.map fun m ↦ (CMvMonomial.ofFinsupp m, f m)
  ⟨
    unlawful,
    by
      intros m contra
      obtain ⟨elem, h₁⟩ : ∃ (h : m ∈ unlawful), unlawful[m] = 0 :=
        ExtTreeMap.getElem?_eq_some_iff.1 contra
      obtain ⟨a, ha₁, ⟨rfl⟩⟩ : ∃ a ∈ s, .ofFinsupp a = m := by
        have elem' :
            m ∈ ExtTreeMap.ofList
              (s.toList.map fun m => (CMvMonomial.ofFinsupp m, f m)) compare := by
          simpa [unlawful] using elem
        rw [ExtTreeMap.mem_ofList] at elem'
        simpa using elem'
      have : f a = 0 := by
        dsimp [unlawful] at h₁
        erw [ExtTreeMap.getElem_ofList_of_mem (v := f a)
                                              (mem := by simp; use a)
                                              (distinct := ?distinct)] at h₁ <;> try simp
        exact h₁
        case distinct =>
          simp only [List.pairwise_map]
          exact List.distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
      grind
  ⟩

instance {n : ℕ} {R : Type*} : Membership (Vector ℕ n) (Unlawful n R) := inferInstance

omit [BEq R] [LawfulBEq R] in
@[grind =, simp]
theorem toCMvPolynomial_fromCMvPolynomial {p : CMvPolynomial n R} :
    toCMvPolynomial (fromCMvPolynomial p) = p := by
  unfold fromCMvPolynomial toCMvPolynomial
  dsimp
  ext m; simp only [CMvPolynomial.coeff]; congr 1
  by_cases eq : m ∈ p <;> simp [eq]
  · erw [ExtTreeMap.getElem_ofList_of_mem (k := m)
                                          (k_eq := by simp)
                                          (v := p[m])
                                          (mem := by simp; grind)
                                          (distinct := ?distinct)]
    grind
    case distinct =>
      simp only [Std.compare_eq_iff_eq, List.pairwise_map]
      exact List.distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)

omit [BEq R] [LawfulBEq R] in
@[grind =, simp]
theorem fromCMvPolynomial_toCMvPolynomial {p : MvPolynomial (Fin n) R} :
    fromCMvPolynomial (toCMvPolynomial p) = p := by
  dsimp [fromCMvPolynomial, toCMvPolynomial, toCMvPolynomial, fromCMvPolynomial]
  ext m; simp [MvPolynomial.coeff]
  rcases p with ⟨s, f, hf⟩
  simp only [Finsupp.coe_mk]
  generalize eq : (ExtTreeMap.ofList _ _) = p
  by_cases eq₁ : CMvMonomial.ofFinsupp m ∈ p
  · obtain ⟨m', hm'₁, hm'₂⟩ : ∃ a ∈ s, CMvMonomial.ofFinsupp a = CMvMonomial.ofFinsupp m := by
      aesop
    have : f m' ≠ 0 := by grind
    obtain ⟨rfl⟩ : m' = m := CMvMonomial.injective_ofFinsupp hm'₂
    suffices p[CMvMonomial.ofFinsupp m] = f m by
      erw [show p[CMvMonomial.ofFinsupp m]? = some (f m) from
        ExtTreeMap.getElem?_eq_some_iff.mpr ⟨eq₁, this⟩]; rfl
    simp_rw [←eq]
    rw [ExtTreeMap.getElem_ofList_of_mem (k := CMvMonomial.ofFinsupp m) (k_eq := by simp)
                                         (mem := by simp; use m) (distinct := ?distinct)]
    case distinct =>
      simp only [Std.compare_eq_iff_eq, List.pairwise_map]
      exact List.distinct_of_inj_nodup CMvMonomial.injective_ofFinsupp (Finset.nodup_toList _)
  · have : ∀ x ∈ s, CMvMonomial.ofFinsupp x ≠ CMvMonomial.ofFinsupp m := by aesop
    grind

lemma fromCMvPolynomial_injective : Function.Injective (@fromCMvPolynomial n R _) := by
  rw [Function.injective_iff_hasLeftInverse]
  exists toCMvPolynomial
  apply toCMvPolynomial_fromCMvPolynomial

omit [BEq R] [LawfulBEq R] in
lemma coeff_eq {m} (a : CMvPolynomial n R) :
    MvPolynomial.coeff m (fromCMvPolynomial a) = a.coeff (CMvMonomial.ofFinsupp m) := rfl

@[aesop simp]
lemma eq_iff_fromCMvPolynomial {u v: CMvPolynomial n R} :
    u = v ↔ fromCMvPolynomial u = fromCMvPolynomial v := by
  constructor
  · intro h
    exact congrArg fromCMvPolynomial h
  · intro h
    exact (fromCMvPolynomial_injective (n := n) (R := R)) h

noncomputable def polyEquiv :
    Equiv (CMvPolynomial n R) (MvPolynomial (Fin n) R) where
  toFun := fromCMvPolynomial
  invFun := toCMvPolynomial
  left_inv := fun _ ↦ toCMvPolynomial_fromCMvPolynomial
  right_inv := fun _ ↦ fromCMvPolynomial_toCMvPolynomial

end

end CPoly
