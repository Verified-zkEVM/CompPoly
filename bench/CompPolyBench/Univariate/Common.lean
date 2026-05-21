/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
import CompPoly.Univariate.NTT.BabyBear
import CompPoly.Univariate.NTT.KoalaBear

/-!
# Shared Univariate Benchmark Helpers
-/

open CompPoly

namespace CompPolyBench

/-- Number of coefficient slots used by univariate batch-evaluation benchmarks. -/
def univariateBatchCoeffSlots : Nat := 128

/-- Number of points used by univariate batch-evaluation benchmarks. -/
def univariateBatchPointCount : Nat := 16

/-- Number of coefficient slots used by medium-shape univariate batch-evaluation benchmarks. -/
def mediumUnivariateBatchCoeffSlots : Nat := 8192

/-- Number of points used by medium-shape univariate batch-evaluation benchmarks. -/
def mediumUnivariateBatchPointCount : Nat := 1024

/-- Number of coefficient slots used by large-shape univariate batch-evaluation benchmarks. -/
def largeUnivariateBatchCoeffSlots : Nat := 65536

/-- Number of points used by large-shape univariate batch-evaluation benchmarks. -/
def largeUnivariateBatchPointCount : Nat := 8192

/-- Number of linear factors in the direct monic-remainder benchmark divisor. -/
def univariateModDivisorPointCount : Nat := 16

/-- Number of coefficient slots used by direct univariate multiplication benchmarks. -/
def univariateMulCoeffSlots : Nat := 1024

/-- Number of coefficient slots used by low-product benchmarks. -/
def univariateMulLowCoeffSlots : Nat := 512

/-- Number of low coefficients kept by low-product benchmarks. -/
def univariateMulLowOutputCoeffSlots : Nat := 512

/-- Radix-2 domain exponent used by direct univariate multiplication benchmarks. -/
def univariateMulLogN : Nat := 11

/-- Domain size used by direct univariate multiplication benchmarks. -/
def univariateMulDomainSize : Nat := 2 ^ univariateMulLogN

/-- Input-shape label for univariate batch-evaluation benchmarks. -/
def univariateBatchShape : String :=
  s!"degree<{univariateBatchCoeffSlots}, dense, {univariateBatchPointCount} points"

/-- Input-shape label for medium-shape univariate batch-evaluation benchmarks. -/
def mediumUnivariateBatchShape : String :=
  s!"degree<{mediumUnivariateBatchCoeffSlots}, dense, " ++
    s!"{mediumUnivariateBatchPointCount} points"

/-- Input-shape label for large-shape univariate batch-evaluation benchmarks. -/
def largeUnivariateBatchShape : String :=
  s!"degree<{largeUnivariateBatchCoeffSlots}, dense, " ++
    s!"{largeUnivariateBatchPointCount} points"

/-- Input-shape label for direct univariate monic-remainder benchmarks. -/
def univariateModShape : String :=
  s!"degree<{univariateBatchCoeffSlots} dividend, degree={univariateModDivisorPointCount} " ++
    "monic divisor"

/-- Input-shape label for medium-shape direct univariate monic-remainder benchmarks. -/
def mediumUnivariateModShape : String :=
  s!"degree<{mediumUnivariateBatchCoeffSlots} dividend, " ++
    s!"degree={mediumUnivariateBatchPointCount} monic divisor"

/-- Input-shape label for direct univariate multiplication benchmarks. -/
def univariateMulShape : String :=
  s!"degree<{univariateMulCoeffSlots} dense lhs/rhs"

/-- Input-shape label for direct univariate low-product benchmarks. -/
def univariateMulLowShape : String :=
  s!"degree<{univariateMulLowCoeffSlots} dense lhs/rhs, low<{univariateMulLowOutputCoeffSlots}"

/-- Method label for direct univariate multiplication NTT benchmarks. -/
def univariateMulNttMethod (name : String) : String :=
  s!"{name}, domain n={univariateMulDomainSize}"

/-- NTT domain for direct univariate BabyBear multiplication benchmarks. -/
def babyBearMulNttDomain : CPolynomial.NTT.Domain BabyBear.Field :=
  CPolynomial.NTT.BabyBear.domainOfLogN univariateMulLogN (by decide)

/-- BabyBear NTT domain lookup for dynamic multiplication contexts. -/
def babyBearBestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain BabyBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? BabyBear.twoAdicity
    CPolynomial.NTT.BabyBear.domainOfLogN (by intro _ _; rfl) requiredLen

/-- Ring equivalence from fast BabyBear elements to the canonical `ZMod` model. -/
noncomputable def babyBearFastRingEquiv : BabyBear.Fast.Element ≃+* BabyBear.Field where
  toFun := BabyBear.Fast.toField
  invFun := BabyBear.Fast.ofField
  left_inv := BabyBear.Fast.ofField_toField
  right_inv := BabyBear.Fast.toField_ofField
  map_mul' := BabyBear.Fast.toField_mul
  map_add' := BabyBear.Fast.toField_add

/-- Fast BabyBear two-adic generators are primitive roots of the same orders. -/
theorem babyBearFast_isPrimitiveRoot_twoAdicGenerator
    (bits : Fin (BabyBear.twoAdicity + 1)) :
    IsPrimitiveRoot (BabyBear.Fast.ofField BabyBear.twoAdicGenerators[bits])
      (2 ^ (bits : Nat)) := by
  have hbasic : IsPrimitiveRoot BabyBear.twoAdicGenerators[bits] (2 ^ (bits : Nat)) :=
    BabyBear.isPrimitiveRoot_twoAdicGenerator bits
  have hfast :
      IsPrimitiveRoot (babyBearFastRingEquiv.symm BabyBear.twoAdicGenerators[bits])
        (2 ^ (bits : Nat)) := by
    exact hbasic.map_of_injective babyBearFastRingEquiv.symm.injective
  simpa [babyBearFastRingEquiv] using hfast

/-- The fast BabyBear NTT domain size is nonzero for supported two-adic sizes. -/
theorem babyBearFast_twoPowNatCast_ne_zero
    (logN : Nat) (hlogN : logN ≤ BabyBear.twoAdicity) :
    (((2 ^ logN : Nat) : BabyBear.Fast.Element) ≠ 0) := by
  intro hzero
  exact CPolynomial.NTT.BabyBear.twoPowNatCast_ne_zero logN hlogN (by
    calc
      (((2 ^ logN : Nat) : BabyBear.Field)) =
          BabyBear.Fast.toField (((2 ^ logN : Nat) : BabyBear.Fast.Element)) := by
        rw [BabyBear.Fast.toField_natCast]
      _ = BabyBear.Fast.toField 0 := congrArg BabyBear.Fast.toField hzero
      _ = 0 := BabyBear.Fast.toField_zero)

/-- Fast BabyBear radix-2 NTT domain for a supported two-adic size. -/
def babyBearFastDomainOfLogN (logN : Nat) (hlogN : logN ≤ BabyBear.twoAdicity) :
    CPolynomial.NTT.Domain BabyBear.Fast.Element where
  logN := logN
  omega := BabyBear.Fast.ofField
    BabyBear.twoAdicGenerators[(⟨logN, Nat.lt_succ_of_le hlogN⟩ :
      Fin (BabyBear.twoAdicity + 1))]
  primitive := by
    simpa using babyBearFast_isPrimitiveRoot_twoAdicGenerator
      (⟨logN, Nat.lt_succ_of_le hlogN⟩ : Fin (BabyBear.twoAdicity + 1))
  natCast_ne_zero := babyBearFast_twoPowNatCast_ne_zero logN hlogN

/-- NTT domain for direct univariate fast BabyBear multiplication benchmarks. -/
def babyBearFastMulNttDomain : CPolynomial.NTT.Domain BabyBear.Fast.Element :=
  babyBearFastDomainOfLogN univariateMulLogN (by decide)

/-- Fast BabyBear NTT domain lookup for dynamic multiplication contexts. -/
def babyBearFastBestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain BabyBear.Fast.Element requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? BabyBear.twoAdicity
    babyBearFastDomainOfLogN (by intro _ _; rfl) requiredLen

/-- NTT domain for direct univariate KoalaBear multiplication benchmarks. -/
def koalaBearMulNttDomain : CPolynomial.NTT.Domain KoalaBear.Field :=
  CPolynomial.NTT.KoalaBear.domainOfLogN univariateMulLogN (by decide)

end CompPolyBench
