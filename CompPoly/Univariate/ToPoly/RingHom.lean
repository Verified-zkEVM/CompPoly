/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Julian Sutherland
-/
module

import all CompPoly.Univariate.ToPoly.Impl
public import CompPoly.Univariate.ToPoly.Impl

/-!
# `C`, `eval₂`, and coefficient-mapping as ring homomorphisms

`CPolynomial.C`, `CPolynomial.eval₂` and coefficient-mapping bundled as `RingHom`s, plus a
ring-hom extensionality principle transported from Mathlib's `Polynomial.ringHom_ext`.

`CHom` and `eval₂Hom` are computable; `toPolyRingHom` is the noncomputable bundling of
`toPoly` (it is `CPolynomial.ringEquiv`), used in proofs only.  These are the bundled-map
building blocks behind the computable `finSuccEquivNth` construction for `CMvPolynomial`.
-/

@[expose] public section

namespace CompPoly

namespace CPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

open Polynomial

/-- `toPoly` is injective — it is the forward map of `CPolynomial.ringEquiv`. -/
theorem toPoly_injective : Function.Injective (CPolynomial.toPoly (R := R)) :=
  fun _ _ h => CPolynomial.ringEquiv.injective h

omit [Nontrivial R] in
/-- `CPolynomial.eval` is the identity-coefficient case of `eval₂`. -/
theorem eval_eq_eval₂ (x : R) (p : CPolynomial R) :
    CPolynomial.eval x p = p.eval₂ (RingHom.id R) x := by
  rw [eval_toPoly, ← Polynomial.eval₂_id, ← eval₂_toPoly]

/-- `CPolynomial.C` bundled as a ring homomorphism.  Computable. -/
def CHom : R →+* CPolynomial R where
  toFun := CPolynomial.C
  map_one' := toPoly_injective (by rw [C_toPoly, toPoly_one, Polynomial.C_1])
  map_mul' _ _ := toPoly_injective (by
    rw [C_toPoly, toPoly_mul, C_toPoly, C_toPoly, Polynomial.C_mul])
  map_zero' := toPoly_injective (by rw [C_toPoly, toPoly_zero, Polynomial.C_0])
  map_add' _ _ := toPoly_injective (by
    rw [C_toPoly, toPoly_add, C_toPoly, C_toPoly, Polynomial.C_add])

@[simp] theorem CHom_apply (r : R) : CHom r = CPolynomial.C r := rfl

/-- `toPoly` bundled as a ring homomorphism (it is `CPolynomial.ringEquiv`).  Noncomputable;
used in proofs only, e.g. to bring `MvPolynomial.eval₂_comp_left` to bear. -/
noncomputable def toPolyRingHom : CPolynomial R →+* Polynomial R :=
  (CPolynomial.ringEquiv (R := R)).toRingHom

@[simp] theorem toPolyRingHom_apply (p : CPolynomial R) : toPolyRingHom p = p.toPoly := by
  rw [toPolyRingHom, RingEquiv.toRingHom_eq_coe]
  exact ringEquiv_apply p

/-- Two ring homomorphisms out of `CPolynomial R` are equal once they agree on the constants and
on `X`. -/
theorem ringHom_ext {S : Type*} [Semiring S] {f g : CPolynomial R →+* S}
    (hC : ∀ r, f (CPolynomial.C r) = g (CPolynomial.C r)) (hX : f CPolynomial.X = g CPolynomial.X) :
    f = g := by
  have hcomp : f.comp (CPolynomial.ringEquiv (R := R)).symm.toRingHom
      = g.comp (CPolynomial.ringEquiv (R := R)).symm.toRingHom := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · have : (CPolynomial.ringEquiv (R := R)).symm (Polynomial.C r) = CPolynomial.C r :=
        (CPolynomial.ringEquiv (R := R)).injective (by
          rw [RingEquiv.apply_symm_apply,
            show CPolynomial.ringEquiv (CPolynomial.C r) = (CPolynomial.C r).toPoly from rfl,
            C_toPoly])
      simpa [this] using hC r
    · have : (CPolynomial.ringEquiv (R := R)).symm Polynomial.X = CPolynomial.X :=
        (CPolynomial.ringEquiv (R := R)).injective (by
          rw [RingEquiv.apply_symm_apply,
            show CPolynomial.ringEquiv (CPolynomial.X) = (CPolynomial.X (R := R)).toPoly from rfl,
            X_toPoly])
      simpa [this] using hX
  refine RingHom.ext (fun p => ?_)
  obtain ⟨q, rfl⟩ := (CPolynomial.ringEquiv (R := R)).symm.surjective p
  exact congrFun (congrArg (·.toFun) hcomp) q

variable {S : Type*} [CommSemiring S]

/-- `CPolynomial.eval₂` bundled as a ring homomorphism (the coefficient map `f` and the point `x`
are fixed).  Computable when `S`'s ring operations are. -/
def eval₂Hom (f : R →+* S) (x : S) : CPolynomial R →+* S where
  toFun p := p.eval₂ f x
  map_zero' := by rw [eval₂_toPoly, toPoly_zero, Polynomial.eval₂_zero]
  map_one' := by rw [eval₂_toPoly, toPoly_one, Polynomial.eval₂_one]
  map_add' p q := by
    rw [eval₂_toPoly, toPoly_add, Polynomial.eval₂_add, ← eval₂_toPoly, ← eval₂_toPoly]
  map_mul' p q := by
    rw [eval₂_toPoly, toPoly_mul, Polynomial.eval₂_mul, ← eval₂_toPoly, ← eval₂_toPoly]

@[simp] theorem eval₂Hom_apply (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂Hom f x p = p.eval₂ f x := rfl

@[simp] theorem eval₂Hom_C (f : R →+* S) (x : S) (r : R) :
    eval₂Hom f x (CPolynomial.C r) = f r := by
  rw [eval₂Hom_apply, eval₂_toPoly, C_toPoly, Polynomial.eval₂_C]

@[simp] theorem eval₂Hom_X (f : R →+* S) (x : S) :
    eval₂Hom f x (CPolynomial.X) = x := by
  rw [eval₂Hom_apply, eval₂_toPoly, X_toPoly, Polynomial.eval₂_X]

section Map

variable [BEq S] [LawfulBEq S] [Nontrivial S]

/-- Map the coefficients of a computable univariate polynomial along a ring homomorphism.
Computable. -/
def mapRingHom (f : R →+* S) : CPolynomial R →+* CPolynomial S :=
  eval₂Hom (CHom.comp f) CPolynomial.X

@[simp] theorem mapRingHom_C (f : R →+* S) (r : R) :
    mapRingHom f (CPolynomial.C r) = CPolynomial.C (f r) := by
  rw [mapRingHom, eval₂Hom_C]; rfl

@[simp] theorem mapRingHom_X (f : R →+* S) :
    mapRingHom f (CPolynomial.X) = CPolynomial.X := by
  rw [mapRingHom, eval₂Hom_X]

/-- Evaluating a coefficient-mapped polynomial: `eval x (mapRingHom f p) = eval₂ f x p`. -/
theorem eval_mapRingHom (f : R →+* S) (x : S) (p : CPolynomial R) :
    CPolynomial.eval x (mapRingHom f p) = p.eval₂ f x := by
  have hcomp : (eval₂Hom (RingHom.id S) x).comp (mapRingHom f) = eval₂Hom f x :=
    ringHom_ext
      (fun r => by rw [RingHom.comp_apply, mapRingHom_C, eval₂Hom_C, eval₂Hom_C, RingHom.id_apply])
      (by rw [RingHom.comp_apply, mapRingHom_X, eval₂Hom_X, eval₂Hom_X])
  rw [eval_eq_eval₂]
  exact congrFun (congrArg (·.toFun) hcomp) p

/-- `toPoly` commutes with coefficient-mapping. -/
theorem toPoly_mapRingHom (f : R →+* S) (p : CPolynomial R) :
    (mapRingHom f p).toPoly = Polynomial.map f p.toPoly := by
  have hcomp : ((CPolynomial.ringEquiv (R := S)).toRingHom).comp (mapRingHom f)
      = (Polynomial.mapRingHom f).comp (CPolynomial.ringEquiv (R := R)).toRingHom := by
    refine ringHom_ext (fun r => ?_) ?_
    · rw [RingHom.comp_apply, mapRingHom_C, RingHom.comp_apply]
      change (CPolynomial.C (f r)).toPoly = Polynomial.map f (CPolynomial.C r).toPoly
      rw [C_toPoly, C_toPoly, Polynomial.map_C]
    · rw [RingHom.comp_apply, mapRingHom_X, RingHom.comp_apply]
      change (CPolynomial.X (R := S)).toPoly = Polynomial.map f (CPolynomial.X (R := R)).toPoly
      rw [X_toPoly, X_toPoly, Polynomial.map_X]
  have := congrFun (congrArg (·.toFun) hcomp) p
  simpa [CPolynomial.ringEquiv_apply] using this

/-- Coefficient-mapping does not increase the degree. -/
theorem natDegree_mapRingHom_le (f : R →+* S) (p : CPolynomial R) :
    (mapRingHom f p).natDegree ≤ p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_mapRingHom]
  exact Polynomial.natDegree_map_le

end Map

end CPolynomial

end CompPoly
