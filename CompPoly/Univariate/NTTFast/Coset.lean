/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Univariate.NTT.Coset
public import CompPoly.Univariate.NTTFast.Evaluation
public import CompPoly.Univariate.NTTFast.Interpolation

/-!
# Planned Coset NTT

The coset transforms of `NTT/Coset.lean` over a reusable `NTTFast.Plan`, with the shift
powers `gⁱ` and `g⁻ⁱ` computed once per plan rather than once per coefficient. As with
`Plan.forwardImpl`, the forward transform returns values in bit-reversed order and the
inverse transform consumes them in that order.

## Main definitions

* `NTTFast.powers g m`: the array `#[1, g, …, g^(m-1)]` by a running product.
* `NTTFast.CosetPlan`: a plan together with a shift `g` and its cached powers.
* `CosetPlan.forwardImpl`, `CosetPlan.inverseImpl`, `CosetPlan.interpolate`.

## Main results

* `powers_eq_ofFn`: the running product computes the powers.
* `CosetPlan.forwardImpl_eq_bitRevPermute_evalOnCoset`: the planned forward transform
  evaluates on the coset, in bit-reversed order.
* `CosetPlan.inverseImpl_correct`: the planned inverse agrees with `NTT.Coset.inverseImpl`.
* `CosetPlan.interpolate_eq_interpolate`: planned coset interpolation is Lagrange
  interpolation on the nodes `g·ωᵏ`.
-/

@[expose] public section

namespace CompPoly
namespace CPolynomial
namespace NTTFast

variable {R : Type*} [Field R]

/-- Tail-recursive running product appending `w, w·g, …, w·g^(k-1)` to `acc`. -/
def powersAux (g : R) : Nat → R → Array R → Array R
  | 0, _, acc => acc
  | k + 1, w, acc => powersAux g k (w * g) (acc.push w)

/-- The powers `#[1, g, …, g^(m-1)]`, by a running product. -/
def powers (g : R) (m : Nat) : Array R :=
  powersAux g m 1 (Array.mkEmpty m)

private theorem toList_powersAux (g : R) :
    ∀ (k : Nat) (w : R) (acc : Array R),
      (powersAux g k w acc).toList = acc.toList ++ List.ofFn (fun i : Fin k => w * g ^ (i : Nat))
  | 0, _, acc => by simp [powersAux]
  | k + 1, w, acc => by
      rw [powersAux, toList_powersAux g k (w * g) (acc.push w), List.ofFn_succ]
      simp [pow_succ', mul_assoc]

/-- The running product computes the powers of `g`. -/
theorem powers_eq_ofFn (g : R) (m : Nat) :
    powers g m = Array.ofFn (fun i : Fin m => g ^ (i : Nat)) := by
  apply Array.toList_inj.mp
  simp [powers, toList_powersAux]

/-- Scale the first `m` coefficients by a cached power table. -/
def scaleWith (pows : Array R) (m : Nat) (a : Array R) : CPolynomial.Raw R :=
  Array.ofFn (fun j : Fin m => pows.getD j 0 * a.getD j 0)

/-- Scaling with the cached powers of `g` is `NTT.Coset.scale g`. -/
theorem scaleWith_powers (g : R) (m : Nat) (a : Array R) :
    scaleWith (powers g m) m a = NTT.Coset.scale g m a := by
  apply Array.ext
  · simp [scaleWith, NTT.Coset.scale]
  · intro i _ _
    simp [scaleWith, NTT.Coset.scale, powers_eq_ofFn]

/-- A reusable plan for transforms on the coset `g·⟨ω⟩` of the plan's domain. -/
structure CosetPlan (R : Type*) [Field R] where
  plan : Plan R
  shift : R
  shiftPowers : Array R
  shiftInvPowers : Array R

namespace CosetPlan

/-- Build a coset plan from a domain plan and a shift `g`. -/
def ofPlan (P : Plan R) (g : R) : CosetPlan R :=
  { plan := P
    shift := g
    shiftPowers := powers g P.domain.n
    shiftInvPowers := powers g⁻¹ P.domain.n }

/-- A coset plan is well formed when its domain plan is and its power tables are exact. -/
def WellFormed (C : CosetPlan R) : Prop :=
  Plan.WellFormed C.plan ∧ C.shiftPowers = powers C.shift C.plan.domain.n ∧
    C.shiftInvPowers = powers C.shift⁻¹ C.plan.domain.n

theorem ofPlan_wellFormed (P : Plan R) (hP : Plan.WellFormed P) (g : R) :
    WellFormed (ofPlan P g) :=
  ⟨hP, rfl, rfl⟩

/-- Forward transform on the coset, returning values in bit-reversed order. -/
@[inline] def forwardImpl (C : CosetPlan R) (p : CPolynomial.Raw R) : Array R :=
  Plan.forwardImpl C.plan (scaleWith C.shiftPowers C.plan.domain.n p)

/-- Inverse transform on the coset, from values in bit-reversed order. -/
@[inline] def inverseImpl (C : CosetPlan R) (v : Array R) : CPolynomial.Raw R :=
  scaleWith C.shiftInvPowers C.plan.domain.n (Plan.inverseImpl C.plan v)

/-- The planned coset forward transform evaluates on the coset, in bit-reversed order. -/
theorem forwardImpl_eq_bitRevPermute_evalOnCoset (C : CosetPlan R) (hC : WellFormed C)
    (p : CPolynomial.Raw R) (hdeg : p.toPoly.natDegree < C.plan.domain.n) :
    forwardImpl C p =
      NTT.Transform.bitRevPermute C.plan.domain
        (NTT.evalOnCoset C.plan.domain C.shift p) := by
  obtain ⟨hP, hpow, _⟩ := hC
  have hscale : (NTT.Coset.scale C.shift C.plan.domain.n p).toPoly.natDegree <
      C.plan.domain.n :=
    NTT.Coset.natDegree_lt_of_size_le _ C.plan.domain.n_pos (by simp)
  rw [forwardImpl, hpow, scaleWith_powers, Plan.forwardImpl_eq_bitRevPermute_evalOnDomain
    C.plan hP _ hscale, ← NTT.Forward.forwardImpl_eq_evalOnDomain _ _ hscale]
  exact congrArg _ (NTT.Coset.forwardImpl_eq_evalOnCoset _ _ p hdeg)

/-- The planned coset inverse agrees with `NTT.Coset.inverseImpl` on bit-reversed input. -/
theorem inverseImpl_correct (C : CosetPlan R) (hC : WellFormed C) (v : Array R) :
    inverseImpl C (NTT.Transform.bitRevPermute C.plan.domain v) =
      NTT.Coset.inverseImpl C.plan.domain C.shift v := by
  obtain ⟨hP, _, hinv⟩ := hC
  rw [inverseImpl, hinv, scaleWith_powers, Plan.inverseImpl_correct C.plan hP,
    ← NTT.Inverse.inverseImpl_correct]
  rfl

/-- Interpolate natural-order values on the coset through the cached plan. -/
def interpolate [BEq R] [LawfulBEq R] (C : CosetPlan R) (values : Vector R C.plan.domain.n) :
    CPolynomial R :=
  let raw := inverseImpl C (NTT.Transform.bitRevPermute C.plan.domain values.toArray)
  ⟨raw.trim, CPolynomial.Raw.Trim.isCanonical_trim raw⟩

/-- A well-formed coset plan interpolates as `NTT.Coset.interpolate`. -/
theorem interpolate_eq_coset_interpolate [BEq R] [LawfulBEq R] (C : CosetPlan R)
    (hC : WellFormed C) (values : Vector R C.plan.domain.n) :
    interpolate C values = NTT.Coset.interpolate C.plan.domain C.shift values := by
  apply Subtype.ext
  simp only [interpolate, NTT.Coset.interpolate, inverseImpl_correct C hC]

/-- Planned coset interpolation is Lagrange interpolation on the nodes `g·ωᵏ`. -/
theorem interpolate_eq_interpolate [BEq R] [LawfulBEq R] (C : CosetPlan R)
    (hC : WellFormed C) (hg : C.shift ≠ 0) (values : Vector R C.plan.domain.n) :
    interpolate C values =
      CLagrange.interpolate Finset.univ
        (fun k : C.plan.domain.Idx => C.shift * C.plan.domain.node k) values.get := by
  rw [interpolate_eq_coset_interpolate C hC, NTT.Coset.interpolate_eq_interpolate _ _ hg]

end CosetPlan
end NTTFast
end CPolynomial
end CompPoly
