/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.LasVegas.Basic

/-!
# Correctness Surface for Las Vegas Splitting

Phase-1 theorem surfaces for the bounded Las Vegas splitter. The executable
backend is deterministic for every fixed `ProbeFamily`; the hard split
preservation and root-product divisibility proofs are intentionally explicit
`sorry`s here and are phase-3 proof debt.
-/

namespace CompPoly

namespace CPolynomial

namespace Roots

namespace FiniteField

/-- Field-root products satisfy the Las Vegas splitter input predicate. -/
theorem finiteFieldRootProductWith_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    lasVegasSplitterInput ctx.q (finiteFieldRootProductWith M D ctx p) := by
  sorry

/-- Default-backend field-root products satisfy the Las Vegas splitter input predicate. -/
theorem finiteFieldRootProduct_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : FiniteFieldContext F) {p : CPolynomial F} (hp : p ≠ 0) :
    lasVegasSplitterInput ctx.q (finiteFieldRootProduct ctx p) := by
  exact finiteFieldRootProductWith_lasVegasSplitterInput
    CPolynomial.Raw.MulContext.naive CPolynomial.Raw.ModContext.naive ctx hp

/-- Completeness surface for bounded Las Vegas splitting plus enumeration fallback. -/
theorem lasVegasSplitLinearFactorsWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (enumeration : FieldEnumeration F) (cfg : LasVegasConfig)
    (probes : ProbeFamily F) (q : Nat)
    {p : CPolynomial F} {a : F}
    (hvalid : lasVegasSplitterInput q p) (hp : p ≠ 0)
    (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈
          (lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  sorry

/-- Package bounded Las Vegas splitting as a finite-field linear-factor splitter. -/
def lasVegasLinearFactorProductSplitterWith {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (_ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := fun q p ↦
    lasVegasSplitLinearFactorsWith M D enumeration cfg probes q p
  validInput := fun q p ↦ lasVegasSplitterInput q p
  sound := by
    intro q p factor h
    exact lasVegasSplitLinearFactorsWith_sound M D enumeration cfg probes q h
  complete := by
    intro q p a hvalid hp hroot
    exact lasVegasSplitLinearFactorsWith_complete
      M D enumeration cfg probes q hvalid hp hroot

/-- Alias emphasizing the root-product precondition used by Las Vegas completeness. -/
theorem rootProduct_satisfies_lasVegasSplitterInput {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : FiniteFieldContext F) (enumeration : FieldEnumeration F)
    (cfg : LasVegasConfig) (probes : ProbeFamily F)
    {p : CPolynomial F} (hp : p ≠ 0) :
    (lasVegasLinearFactorProductSplitterWith M D ctx enumeration cfg probes).validInput ctx.q
      (finiteFieldRootProductWith M D ctx p) := by
  exact finiteFieldRootProductWith_lasVegasSplitterInput M D ctx hp

end FiniteField

end Roots

end CPolynomial

end CompPoly
