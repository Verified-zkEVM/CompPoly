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
  CPolynomial.NTT.KoalaBear.bestDomainForLength? requiredLen

/-- Fast KoalaBear radix-2 NTT domain for a supported two-adic size. -/
def koalaBearFastDomainOfLogN (logN : Nat) (hlogN : logN ≤ KoalaBear.twoAdicity) :
    CPolynomial.NTT.Domain KoalaBear.Fast.Field :=
  CPolynomial.NTT.KoalaBear.fastDomainOfLogN logN hlogN

/-- NTT domain for direct univariate fast KoalaBear multiplication benchmarks. -/
def koalaBearFastMulNttDomain : CPolynomial.NTT.Domain KoalaBear.Fast.Field :=
  koalaBearFastDomainOfLogN univariateMulLogN (by decide)

/-- Fast KoalaBear NTT domain lookup for dynamic multiplication contexts. -/
def koalaBearFastBestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain KoalaBear.Fast.Field requiredLen) :=
  CPolynomial.NTT.KoalaBear.fastBestDomainForLength? requiredLen

end CompPolyBench
