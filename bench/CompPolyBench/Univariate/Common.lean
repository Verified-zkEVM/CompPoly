/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyBench.Common
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

/-- NTT domain for direct univariate KoalaBear multiplication benchmarks. -/
def koalaBearMulNttDomain : CPolynomial.NTT.Domain KoalaBear.Field :=
  CPolynomial.NTT.KoalaBear.domainOfLogN univariateMulLogN (by decide)

/-- KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def koalaBearBestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain KoalaBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    CPolynomial.NTT.KoalaBear.domainOfLogN (by intro _ _; rfl) requiredLen

/-- Ring equivalence from fast KoalaBear elements to the canonical `ZMod` model. -/
noncomputable def koalaBearFastRingEquiv : KoalaBear.Fast.Element ≃+* KoalaBear.Field where
  toFun := KoalaBear.Fast.toField
  invFun := KoalaBear.Fast.ofField
  left_inv := KoalaBear.Fast.ofField_toField
  right_inv := KoalaBear.Fast.toField_ofField
  map_mul' := KoalaBear.Fast.toField_mul
  map_add' := KoalaBear.Fast.toField_add

/-- Fast KoalaBear two-adic generators are primitive roots of the same orders. -/
theorem koalaBearFast_isPrimitiveRoot_twoAdicGenerator
    (bits : Fin (KoalaBear.twoAdicity + 1)) :
    IsPrimitiveRoot (KoalaBear.Fast.ofField KoalaBear.twoAdicGenerators[bits])
      (2 ^ (bits : Nat)) := by
  have hbasic : IsPrimitiveRoot KoalaBear.twoAdicGenerators[bits] (2 ^ (bits : Nat)) :=
    KoalaBear.isPrimitiveRoot_twoAdicGenerator bits
  have hfast :
      IsPrimitiveRoot (koalaBearFastRingEquiv.symm KoalaBear.twoAdicGenerators[bits])
        (2 ^ (bits : Nat)) := by
    exact hbasic.map_of_injective koalaBearFastRingEquiv.symm.injective
  simpa [koalaBearFastRingEquiv] using hfast

/-- The fast KoalaBear NTT domain size is nonzero for supported two-adic sizes. -/
theorem koalaBearFast_twoPowNatCast_ne_zero
    (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    (((2 ^ logN : Nat) : KoalaBear.Fast.Element) ≠ 0) := by
  intro hzero
  exact CPolynomial.NTT.KoalaBear.twoPowNatCast_ne_zero logN hlogN (by
    calc
      (((2 ^ logN : Nat) : KoalaBear.Field)) =
          KoalaBear.Fast.toField (((2 ^ logN : Nat) : KoalaBear.Fast.Element)) := by
        rw [KoalaBear.Fast.toField_natCast]
      _ = KoalaBear.Fast.toField 0 := congrArg KoalaBear.Fast.toField hzero
      _ = 0 := KoalaBear.Fast.toField_zero)

/-- Fast KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def koalaBearFastDomainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    CPolynomial.NTT.Domain KoalaBear.Fast.Element where
  logN := logN
  omega := KoalaBear.Fast.ofField
    KoalaBear.twoAdicGenerators[(⟨logN, Nat.lt_succ_of_le hlogN⟩ :
      Fin (KoalaBear.twoAdicity + 1))]
  primitive := by
    simpa using koalaBearFast_isPrimitiveRoot_twoAdicGenerator
      (⟨logN, Nat.lt_succ_of_le hlogN⟩ : Fin (KoalaBear.twoAdicity + 1))
  natCast_ne_zero := koalaBearFast_twoPowNatCast_ne_zero logN hlogN

/-- NTT domain for direct univariate fast KoalaBear multiplication benchmarks. -/
def koalaBearFastMulNttDomain : CPolynomial.NTT.Domain KoalaBear.Fast.Element :=
  koalaBearFastDomainOfLogN univariateMulLogN (by decide)

/-- Fast KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def koalaBearFastBestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain KoalaBear.Fast.Element requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? KoalaBear.twoAdicity
    koalaBearFastDomainOfLogN (by intro _ _; rfl) requiredLen

end CompPolyBench
