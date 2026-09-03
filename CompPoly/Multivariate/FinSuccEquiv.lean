/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin, Aristotle (Harmonic), Dimitris Mitsios, Julian Sutherland
-/
module

public import CompPoly.Multivariate.MvPolyEquiv
public import CompPoly.Multivariate.Operations
public import CompPoly.Univariate.ToPoly
public import CompPoly.ToMathlib.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# `finSuccEquiv` for `CMvPolynomial`

This file defines the computable multivariate polynomial equivalence for
splitting off one variable, mirroring `MvPolynomial.finSuccEquiv` from Mathlib.

In Mathlib, `MvPolynomial` accepts a general type `σ` for the index set of the
variables. Then, `optionEquivLeft` provides the algebra isomorphism
`MvPolynomial (Option σ) R ≃ₐ[R] Polynomial (MvPolynomial σ R)`. Finally,
`finSuccEquiv` is defined as the composition of the rename step
(`Fin (n+1) ≃ Option (Fin n)`) with `optionEquivLeft`. There is no such
distinction in `CMvPolynomial` because the variables are of type `Fin n` by
definition. Therefore, only `CMvPolynomial.finSuccEquiv` applies.

## Main definitions

* `CMvPolynomial.finSuccEquiv` — `noncomputable` ring equivalence
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`,
    viewing a polynomial in `n+1` variables as a univariate polynomial over `n` variables.
* `CMvPolynomial.finSuccEquivNth p` — **computable** ring equivalence
    `CMvPolynomial (n+1) R ≃+* CompPoly.CPolynomial (CMvPolynomial n R)` for an *arbitrary* pivot
    `p`, splitting off variable `p`. Both directions are `eval₂` folds, so they compute; the
    ring-equivalence laws are proved by extensionality on the `C`/`X` generators.
* `CMvPolynomial.finSuccEquivNthHom p` / `finSuccEquivNthInvHom p` — its two directions as
    `RingHom`s.

## Implementation notes

`finSuccEquiv` is `noncomputable` because it goes through the `polyRingEquiv` bridge between
`CMvPolynomial` and `MvPolynomial`; its forward/inverse correctness is obtained structurally from
the underlying Mathlib `AlgEquiv` via `RingEquiv.trans`.

`finSuccEquivNth` avoids that bridge in its *definition* (staying inside the computable
`CMvPolynomial` / `CPolynomial` world), and only crosses to Mathlib in the *proof* of
`map_polyRingEquiv_toPoly_finSuccEquivNth`, which identifies it with
`MvPolynomial.finSuccEquivNth` after transport.
-/

@[expose] public section

open Std CPoly CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

namespace CPoly

/-! ### Polynomial-level ring equivalence -/

/-- `Polynomial.mapEquiv` through the CMvPolynomial ↔ MvPolynomial bridge. -/
noncomputable def polynomialCMvPolyEquiv :
    Polynomial (CMvPolynomial n R) ≃+* Polynomial (MvPolynomial (Fin n) R) :=
  Polynomial.mapEquiv polyRingEquiv

end CPoly

namespace CMvPolynomial

/-! ### `finSuccEquiv` -/

/-- Ring equivalence splitting off the first variable:
    `CMvPolynomial (n+1) R ≃+* Polynomial (CMvPolynomial n R)`.

    This mirrors `MvPolynomial.finSuccEquiv R n`. The 0-th variable becomes
    the univariate indeterminate `Polynomial.X`, and variables `1, …, n` become
    the multivariate variables of the coefficient ring `CMvPolynomial n R`. -/
noncomputable def finSuccEquiv :
    CMvPolynomial (n + 1) R ≃+* Polynomial (CMvPolynomial n R) :=
  (polyRingEquiv (n := n + 1)).trans <|
    (MvPolynomial.finSuccEquiv R n).toRingEquiv.trans polynomialCMvPolyEquiv.symm

/-- The equivalence is a left inverse: applying the inverse then forward is the identity. -/
@[simp]
theorem finSuccEquiv_symm_apply_apply (p : CMvPolynomial (n + 1) R) :
    finSuccEquiv.symm (finSuccEquiv p) = p :=
  finSuccEquiv.symm_apply_apply p

/-- The equivalence is a right inverse: applying forward then the inverse is the identity. -/
@[simp]
theorem finSuccEquiv_apply_symm_apply
    (q : Polynomial (CMvPolynomial n R)) :
    finSuccEquiv (finSuccEquiv.symm q) = q :=
  finSuccEquiv.apply_symm_apply q

/-- `finSuccEquiv` preserves addition. -/
theorem finSuccEquiv_add (p q : CMvPolynomial (n + 1) R) :
    finSuccEquiv (p + q) =
      finSuccEquiv p + finSuccEquiv q :=
  finSuccEquiv.map_add p q

/-- `finSuccEquiv` preserves multiplication. -/
theorem finSuccEquiv_mul (p q : CMvPolynomial (n + 1) R) :
    finSuccEquiv (p * q) =
      finSuccEquiv p * finSuccEquiv q :=
  finSuccEquiv.map_mul p q

/-- `finSuccEquiv` maps zero to zero. -/
@[simp]
theorem finSuccEquiv_zero :
    finSuccEquiv (0 : CMvPolynomial (n + 1) R) = 0 :=
  RingEquiv.map_zero (finSuccEquiv (n := n) (R := R))

/-- `finSuccEquiv` maps one to one. -/
@[simp]
theorem finSuccEquiv_one :
    finSuccEquiv (1 : CMvPolynomial (n + 1) R) = 1 :=
  RingEquiv.map_one (finSuccEquiv (n := n) (R := R))

end CMvPolynomial

/-! ### The computable `finSuccEquivNth` (arbitrary pivot)

Unlike `finSuccEquiv` above, this stays inside the computable `CMvPolynomial` / `CPolynomial`
world and works for an arbitrary pivot `p`. -/

namespace CPoly.CMvPolynomial

open CompPoly CompPoly.CPolynomial

variable [Nontrivial R]

/-- Assignment used by the forward direction: variable `p` goes to the univariate `X`, every
other variable `p.succAbove j` goes to the constant `C (X j)`. -/
def fseVars (p : Fin (n + 1)) : Fin (n + 1) → CPolynomial (CMvPolynomial n R) :=
  Fin.insertNth p CPolynomial.X (fun j => CPolynomial.C (CMvPolynomial.X j))

@[simp] theorem fseVars_same (p : Fin (n + 1)) :
    fseVars (R := R) p p = CPolynomial.X := by simp [fseVars]

@[simp] theorem fseVars_succAbove (p : Fin (n + 1)) (j : Fin n) :
    fseVars (R := R) p (p.succAbove j) = CPolynomial.C (CMvPolynomial.X j) := by simp [fseVars]

/-- Forward direction of `finSuccEquivNth`, as a `RingHom`.  Splits variable `p` off as the
univariate indeterminate over the other `n` variables.  Computable. -/
def finSuccEquivNthHom (p : Fin (n + 1)) :
    CMvPolynomial (n + 1) R →+* CPolynomial (CMvPolynomial n R) :=
  CMvPolynomial.eval₂Hom (CPolynomial.CHom.comp CMvPolynomial.CHom) (fseVars p)

/-- "Insert a dummy variable at position `p`": the embedding `CMvPolynomial n R →+* CMvPolynomial
(n+1) R` sending `X j` to `X (p.succAbove j)`.  Computable. -/
def insertVarHom (p : Fin (n + 1)) : CMvPolynomial n R →+* CMvPolynomial (n + 1) R :=
  CMvPolynomial.eval₂Hom CMvPolynomial.CHom (fun j => CMvPolynomial.X (p.succAbove j))

/-- Inverse direction of `finSuccEquivNth`, as a `RingHom`.  Computable. -/
def finSuccEquivNthInvHom (p : Fin (n + 1)) :
    CPolynomial (CMvPolynomial n R) →+* CMvPolynomial (n + 1) R :=
  CPolynomial.eval₂Hom (insertVarHom p) (CMvPolynomial.X p)

@[simp] theorem finSuccEquivNthHom_C (p : Fin (n + 1)) (c : R) :
    finSuccEquivNthHom (R := R) p (CMvPolynomial.C c) = CPolynomial.C (CMvPolynomial.C c) := by
  simp [finSuccEquivNthHom]

@[simp] theorem finSuccEquivNthHom_X_same (p : Fin (n + 1)) :
    finSuccEquivNthHom (R := R) p (CMvPolynomial.X p) = CPolynomial.X := by
  simp [finSuccEquivNthHom]

@[simp] theorem finSuccEquivNthHom_X_succAbove (p : Fin (n + 1)) (j : Fin n) :
    finSuccEquivNthHom (R := R) p (CMvPolynomial.X (p.succAbove j))
      = CPolynomial.C (CMvPolynomial.X j) := by
  simp [finSuccEquivNthHom]

omit [Nontrivial R] in
@[simp] theorem insertVarHom_C (p : Fin (n + 1)) (c : R) :
    insertVarHom (R := R) p (CMvPolynomial.C c) = CMvPolynomial.C c := by
  simp [insertVarHom, CMvPolynomial.CHom]

omit [Nontrivial R] in
@[simp] theorem insertVarHom_X (p : Fin (n + 1)) (j : Fin n) :
    insertVarHom (R := R) p (CMvPolynomial.X j) = CMvPolynomial.X (p.succAbove j) := by
  simp [insertVarHom]

@[simp] theorem finSuccEquivNthInvHom_C (p : Fin (n + 1)) (q : CMvPolynomial n R) :
    finSuccEquivNthInvHom (R := R) p (CPolynomial.C q) = insertVarHom p q := by
  rw [finSuccEquivNthInvHom, CPolynomial.eval₂Hom_C]

@[simp] theorem finSuccEquivNthInvHom_X (p : Fin (n + 1)) :
    finSuccEquivNthInvHom (R := R) p (CPolynomial.X) = CMvPolynomial.X p := by
  rw [finSuccEquivNthInvHom, CPolynomial.eval₂Hom_X]

/-- `finSuccEquivNthHom` composed with `insertVarHom` is the constant embedding
`CMvPolynomial n R →+* CPolynomial (CMvPolynomial n R)`. -/
theorem finSuccEquivNthHom_comp_insertVarHom (p : Fin (n + 1)) :
    (finSuccEquivNthHom (R := R) p).comp (insertVarHom p) = CPolynomial.CHom := by
  refine CMvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, insertVarHom_C, finSuccEquivNthHom_C, CPolynomial.CHom_apply]
  · rw [RingHom.comp_apply, insertVarHom_X, finSuccEquivNthHom_X_succAbove,
      CPolynomial.CHom_apply]

theorem finSuccEquivNthHom_comp_inv (p : Fin (n + 1)) :
    (finSuccEquivNthHom (R := R) p).comp (finSuccEquivNthInvHom p)
      = RingHom.id (CPolynomial (CMvPolynomial n R)) := by
  refine CPolynomial.ringHom_ext (fun q => ?_) ?_
  · rw [RingHom.comp_apply, finSuccEquivNthInvHom_C, RingHom.id_apply,
      ← RingHom.comp_apply, finSuccEquivNthHom_comp_insertVarHom, CPolynomial.CHom_apply]
  · rw [RingHom.comp_apply, finSuccEquivNthInvHom_X, finSuccEquivNthHom_X_same, RingHom.id_apply]

theorem finSuccEquivNthInvHom_comp_fwd (p : Fin (n + 1)) :
    (finSuccEquivNthInvHom (R := R) p).comp (finSuccEquivNthHom p)
      = RingHom.id (CMvPolynomial (n + 1) R) := by
  refine CMvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, finSuccEquivNthHom_C, finSuccEquivNthInvHom_C, insertVarHom_C,
      RingHom.id_apply]
  · refine Fin.succAboveCases p ?_ ?_ i
    · rw [RingHom.comp_apply, finSuccEquivNthHom_X_same, finSuccEquivNthInvHom_X, RingHom.id_apply]
    · intro j
      rw [RingHom.comp_apply, finSuccEquivNthHom_X_succAbove, finSuccEquivNthInvHom_C,
        insertVarHom_X, RingHom.id_apply]

/-- **The computable `finSuccEquivNth`**: a ring equivalence
`CMvPolynomial (n+1) R ≃+* CompPoly.CPolynomial (CMvPolynomial n R)` for an arbitrary pivot `p`.
Both directions compute. -/
def finSuccEquivNth (p : Fin (n + 1)) :
    CMvPolynomial (n + 1) R ≃+* CPolynomial (CMvPolynomial n R) :=
  RingEquiv.ofRingHom (finSuccEquivNthHom p) (finSuccEquivNthInvHom p)
    (finSuccEquivNthHom_comp_inv p) (finSuccEquivNthInvHom_comp_fwd p)

@[simp] theorem finSuccEquivNth_apply (p : Fin (n + 1)) (P : CMvPolynomial (n + 1) R) :
    finSuccEquivNth p P = finSuccEquivNthHom p P := rfl

@[simp] theorem finSuccEquivNth_symm_apply (p : Fin (n + 1))
    (Q : CPolynomial (CMvPolynomial n R)) :
    (finSuccEquivNth p).symm Q = finSuccEquivNthInvHom p Q := rfl

/-! ### Compatibility with Mathlib's `MvPolynomial.finSuccEquivNth` -/

/-- The computable `finSuccEquivNth`, transported to Mathlib's `MvPolynomial`/`Polynomial` world
along `polyRingEquiv` and `CPolynomial.toPoly`, is Mathlib's `MvPolynomial.finSuccEquivNth`. -/
theorem map_polyRingEquiv_toPoly_finSuccEquivNth (p : Fin (n + 1)) (P : CMvPolynomial (n + 1) R) :
    Polynomial.map (CPoly.polyRingEquiv (n := n) (R := R)).toRingHom
        (CPolynomial.toPoly (finSuccEquivNthHom p P))
      = MvPolynomial.finSuccEquivNth R p (CPoly.fromCMvPolynomial P) := by
  have key :
      (Polynomial.mapRingHom (CPoly.polyRingEquiv (n := n) (R := R)).toRingHom).comp
          ((CPolynomial.ringEquiv (R := CMvPolynomial n R)).toRingHom.comp (finSuccEquivNthHom p))
        = (MvPolynomial.finSuccEquivNth R p :
            MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)).comp
            (CPoly.polyRingEquiv (n := n + 1) (R := R)).toRingHom := by
    have hfse : ∀ f : MvPolynomial (Fin (n + 1)) R,
        (MvPolynomial.finSuccEquivNth R p :
            MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) f
          = MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
              (Fin.insertNth p Polynomial.X (Polynomial.C ∘ MvPolynomial.X)) f := fun f => by
      rw [MvPolynomial.finSuccEquivNth_eq]
    refine CMvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, finSuccEquivNthHom_C,
        CPolynomial.ringEquiv_apply, CPolynomial.C_toPoly, Polynomial.coe_mapRingHom,
        Polynomial.map_C, CPoly.coe_polyRingEquiv, CMvPolynomial.fromCMvPolynomial_C, hfse,
        MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
    · refine Fin.succAboveCases p ?_ ?_ k
      · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, finSuccEquivNthHom_X_same,
          CPolynomial.ringEquiv_apply, CPolynomial.X_toPoly, Polynomial.coe_mapRingHom,
          Polynomial.map_X, CPoly.coe_polyRingEquiv, CMvPolynomial.fromCMvPolynomial_X, hfse,
          MvPolynomial.eval₂Hom_X', Fin.insertNth_apply_same]
      · intro j
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, finSuccEquivNthHom_X_succAbove,
          CPolynomial.ringEquiv_apply, CPolynomial.C_toPoly, Polynomial.coe_mapRingHom,
          Polynomial.map_C, CPoly.coe_polyRingEquiv, CMvPolynomial.fromCMvPolynomial_X, hfse,
          MvPolynomial.eval₂Hom_X', Fin.insertNth_apply_succAbove, Function.comp_apply]
  have := congrFun (congrArg (·.toFun) key) P
  simpa [CPolynomial.ringEquiv_apply, Polynomial.coe_mapRingHom, CPoly.coe_polyRingEquiv] using this

/-- The univariate degree of `finSuccEquivNth p P` is the degree of variable `p` in `P`. -/
theorem natDegree_finSuccEquivNthHom (p : Fin (n + 1)) (P : CMvPolynomial (n + 1) R) :
    (finSuccEquivNthHom p P).natDegree = P.degreeOf p := by
  have hinj : Function.Injective
      ⇑(CPoly.polyRingEquiv (n := n) (R := R)).toRingHom :=
    (CPoly.polyRingEquiv (n := n) (R := R)).injective
  rw [CompPoly.CPolynomial.natDegree_toPoly,
    ← Polynomial.natDegree_map_eq_of_injective hinj,
    map_polyRingEquiv_toPoly_finSuccEquivNth, MvPolynomial.natDegree_finSuccEquivNth]
  exact (congrFun (CPoly.degreeOf_equiv (S := R) (p := P)) p).symm

/-- `finSuccEquivNth p P` has univariate degree at most `d` whenever `P` has per-variable
degree at most `d`. -/
theorem natDegree_finSuccEquivNthHom_le {d : ℕ} (p : Fin (n + 1)) (P : CMvPolynomial (n + 1) R)
    (hP : ∀ k, P.degreeOf k ≤ d) : (finSuccEquivNthHom p P).natDegree ≤ d := by
  rw [natDegree_finSuccEquivNthHom]; exact hP p

end CPoly.CMvPolynomial
