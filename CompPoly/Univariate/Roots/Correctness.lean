/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Univariate.Roots.Backend

/-!
# Finite-Field Root Correctness

Theorem statements and certified context constructors for the executable
finite-field root backend.
-/

namespace CompPoly

namespace CPolynomial

/-- Monic normalization preserves roots of nonzero polynomials. -/
theorem monicNormalize_root_iff {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {a : F} (hp : p ≠ 0) :
    CPolynomial.eval a (monicNormalize p) = 0 ↔ CPolynomial.eval a p = 0 := by
  sorry

/-- The monic gcd contains every common root. -/
theorem gcdMonic_root_of_left_right {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {p q : CPolynomial F} {a : F}
    (hp : CPolynomial.eval a p = 0) (hq : CPolynomial.eval a q = 0) :
    CPolynomial.eval a (gcdMonic p q) = 0 := by
  sorry

/-- Roots extracted from a linear factor satisfy that factor. -/
theorem linearRootOfFactor?_sound {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    {factor : CPolynomial F} {a : F}
    (h : linearRootOfFactor? factor = some a) :
    CPolynomial.eval a factor = 0 := by
  sorry

/-- Validation makes returned candidates sound for the original polynomial. -/
theorem mem_validateRootCandidates_eval_eq_zero {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {p : CPolynomial F} {candidates : Array F} {a : F}
    (h : a ∈ (validateRootCandidates p candidates).toList) :
    CPolynomial.eval a p = 0 := by
  sorry

namespace Roots

namespace FiniteField

/-- Every root of `p` is a root of the finite-field root product. -/
theorem finiteFieldRootProduct_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.eval a (finiteFieldRootProduct ctx p) = 0 := by
  sorry

/-- Every validated root extracted from the root product is a root of `p`. -/
theorem finiteFieldRootProduct_validated_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (_ctx : OddFiniteFieldContext F) {p : CPolynomial F}
    {candidates : Array F} {a : F}
    (h : a ∈ (CPolynomial.validateRootCandidates p candidates).toList) :
    CPolynomial.eval a p = 0 := by
  exact CPolynomial.mem_validateRootCandidates_eval_eq_zero h

/-- Soundness of factors returned by the fuel-bounded splitter. -/
theorem cantorZassenhausLinearFactorsWithFuel_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {q fuel : Nat} {probes : Array (CPolynomial F)} {p factor : CPolynomial F}
    (h : factor ∈ (cantorZassenhausLinearFactorsWithFuel q probes fuel p).toList) :
    IsLinearFactor factor := by
  sorry

/-- Completeness statement for a probe stream that splits every reached product. -/
theorem deterministicLinearFactors_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    {q : Nat} {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    ∃ factor,
      factor ∈ (deterministicLinearFactors q p).toList ∧
        IsLinearRootFactorCandidate factor a := by
  sorry

/-- Default deterministic splitter for odd finite fields. -/
def deterministicLinearFactorProductSplitterWith (F : Type*)
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F) :
    LinearFactorProductSplitter F where
  splitLinearFactors := deterministicLinearFactorsWith M D
  sound := by
    intro q p factor h
    sorry
  complete := by
    intro q p a hp hroot
    sorry

/-- Default deterministic splitter for odd finite fields with the default raw backends. -/
def deterministicLinearFactorProductSplitter (F : Type*)
    [Field F] [BEq F] [LawfulBEq F] : LinearFactorProductSplitter F :=
  deterministicLinearFactorProductSplitterWith F CPolynomial.Raw.MulContext.naive
    CPolynomial.Raw.ModContext.naive

/-- Returned finite-field roots are roots of the original polynomial. -/
theorem rootsInOddFiniteFieldWith_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F}
    (h : a ∈ (rootsInOddFiniteFieldWith M D ctx splitter p).toList) :
    CPolynomial.eval a p = 0 := by
  sorry

/-- Returned finite-field roots are roots of the original polynomial. -/
theorem rootsInOddFiniteField_sound {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F}
    (h : a ∈ (rootsInOddFiniteField ctx splitter p).toList) :
    CPolynomial.eval a p = 0 := by
  exact rootsInOddFiniteFieldWith_sound
    (M := CPolynomial.Raw.MulContext.naive) (D := CPolynomial.Raw.ModContext.naive)
    ctx splitter h

/-- Every root of a nonzero polynomial is returned by the finite-field backend. -/
theorem rootsInOddFiniteFieldWith_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (M : CPolynomial.Raw.MulContext F) (D : CPolynomial.Raw.ModContext F)
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    a ∈ (rootsInOddFiniteFieldWith M D ctx splitter p).toList := by
  sorry

/-- Every root of a nonzero polynomial is returned by the finite-field backend. -/
theorem rootsInOddFiniteField_complete {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F}
    (hp : p ≠ 0) (hroot : CPolynomial.eval a p = 0) :
    a ∈ (rootsInOddFiniteField ctx splitter p).toList := by
  exact rootsInOddFiniteFieldWith_complete
    (M := CPolynomial.Raw.MulContext.naive) (D := CPolynomial.Raw.ModContext.naive)
    ctx splitter hp hroot

/-- The complete executable finite-field root pipeline is sound and complete
for nonzero inputs under the odd finite-field and splitter contracts. -/
theorem rootsInOddFiniteField_spec {F : Type*}
    [Field F] [BEq F] [LawfulBEq F]
    (ctx : OddFiniteFieldContext F) (splitter : LinearFactorProductSplitter F)
    {p : CPolynomial F} {a : F} (hp : p ≠ 0) :
    a ∈ (rootsInOddFiniteField ctx splitter p).toList ↔
      CPolynomial.eval a p = 0 := by
  constructor
  · intro h
    exact rootsInOddFiniteField_sound ctx splitter h
  · intro h
    exact rootsInOddFiniteField_complete ctx splitter hp h

end FiniteField

end Roots

end CPolynomial

end CompPoly
