/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.RootProduct
import CompPoly.Univariate.Roots.SmoothSubgroup

/-!
# Smooth Multiplicative-Subgroup Splitter Correctness

Proof surface for the smooth cyclic splitter. The executable refactor lands the
contracts now; the detailed coset-partition and field-specific proofs can be
filled in incrementally.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Field-root products satisfy the generic smooth-splitter input predicate. -/
theorem finiteFieldRootProductWith_smoothSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (generator : F) (schedule : Array Nat)
    {p : CPolynomial F} (hp : p ≠ 0) :
    smoothSplitterInput ctx.q generator schedule
      (finiteFieldRootProductWith M D ctx p) := by
  sorry

/-- Soundness theorem for a smooth context adapted to the splitter interface. -/
theorem smoothLinearFactorProductSplitterWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmoothCyclicRootContext F) {q : Nat} {p factor : CPolynomial F}
    (h : factor ∈
      ((smoothLinearFactorProductSplitterWith M D ctx).splitLinearFactors q p).toList) :
    IsLinearFactor factor := by
  exact (smoothLinearFactorProductSplitterWith M D ctx).sound q p factor h

/-- Completeness theorem for a smooth context adapted to the splitter interface. -/
theorem smoothLinearFactorProductSplitterWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : SmoothCyclicRootContext F) {q : Nat} {p : CPolynomial F} {a : F}
    (hvalid : (smoothLinearFactorProductSplitterWith M D ctx).validInput q p)
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          ((smoothLinearFactorProductSplitterWith M D ctx).splitLinearFactors q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  exact (smoothLinearFactorProductSplitterWith M D ctx).complete q p a hvalid hp hroot

/-- Zero-root extraction is sound for the emitted `X` factor. -/
theorem smooth_zero_root_factor_sound {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    IsLinearRootFactorCandidate (CPolynomial.linearFactor (0 : F)) (0 : F) := by
  sorry

/-- A smooth coset split partitions roots according to the child-coset equation. -/
theorem smooth_coset_split_root_partition {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {alpha gamma x : F} {order ell : Nat}
    (hgamma_order : orderOf gamma = order)
    (hell_dvd : ell ∣ order) (hell_pos : 0 < ell)
    (hx : ∃ k : Nat, k < order ∧ x = alpha * gamma ^ k) :
    ∃ j : Nat, j < ell ∧
      x ^ (order / ell) = alpha ^ (order / ell) * (gamma ^ (order / ell)) ^ j := by
  sorry

/-- Roots of `p` are contained in the explicit coset `alpha * <gamma>` of order `order`. -/
def SmoothCosetInvariant {F : Type*} [Field F]
    (alpha gamma : F) (order : Nat) (p : CPolynomial F) : Prop :=
  alpha ≠ 0 ∧
    0 < order ∧
      orderOf gamma = order ∧
        ∀ x : F, CPolynomial.eval x p = 0 →
          ∃ k : Nat, k < order ∧ x = alpha * gamma ^ k

/-- Schedule recursion preserves the smooth coset invariant. -/
theorem smooth_schedule_recursion_preserves_coset_invariant {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    {order ell j : Nat} {alpha gamma : F} {p : CPolynomial F}
    (hparent : SmoothCosetInvariant alpha gamma order p)
    (hell_dvd : ell ∣ order) (hell_gt_one : 1 < ell) (hj : j < ell) :
    SmoothCosetInvariant
      (alpha * gamma ^ j)
      (gamma ^ ell)
      (order / ell)
      (CPolynomial.monicNormalize
        (CPolynomial.gcdMonic p
          (xPowModWith M D p (order / ell) -
            CPolynomial.C (alpha ^ (order / ell) * (gamma ^ (order / ell)) ^ j)))) := by
  sorry

/-- The declared smooth schedule reaches singleton cosets. -/
theorem smooth_schedule_reaches_singleton {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : SmoothCyclicRootContext F) :
    ctx.schedule.toList.foldl (fun order ell => order / ell) (ctx.q - 1) = 1 :=
  ctx.schedule_complete

end FiniteField

end Roots

end CPolynomial

end CompPoly
