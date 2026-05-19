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

/-- Number of coefficient slots used by medium univariate batch-evaluation benchmarks. -/
def mediumUnivariateBatchCoeffSlots : Nat := 8192

/-- Number of points used by medium univariate batch-evaluation benchmarks. -/
def mediumUnivariateBatchPointCount : Nat := 1024

/-- Number of coefficient slots used by large univariate batch-evaluation benchmarks. -/
def largeUnivariateBatchCoeffSlots : Nat := 65536

/-- Number of points used by large univariate batch-evaluation benchmarks. -/
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

/-- Input-shape label for medium univariate batch-evaluation benchmarks. -/
def mediumUnivariateBatchShape : String :=
  s!"degree<{mediumUnivariateBatchCoeffSlots}, dense, " ++
    s!"{mediumUnivariateBatchPointCount} points"

/-- Input-shape label for large univariate batch-evaluation benchmarks. -/
def largeUnivariateBatchShape : String :=
  s!"degree<{largeUnivariateBatchCoeffSlots}, dense, " ++
    s!"{largeUnivariateBatchPointCount} points"

/-- Input-shape label for direct univariate monic-remainder benchmarks. -/
def univariateModShape : String :=
  s!"degree<{univariateBatchCoeffSlots} dividend, degree={univariateModDivisorPointCount} " ++
    "monic divisor"

/-- Input-shape label for medium direct univariate monic-remainder benchmarks. -/
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

/-- NTT domain large enough for direct univariate BabyBear multiplication benchmarks. -/
def babyBearMulNttDomain : CPolynomial.NTT.Domain BabyBear.Field :=
  CPolynomial.NTT.BabyBear.domainOfLogN univariateMulLogN (by decide)

/-- Best-fitting BabyBear NTT domain lookup for dynamic multiplication contexts. -/
def babyBearBestDomainForLength? (requiredLen : Nat) :
    Option (CPolynomial.NTT.FittingDomain BabyBear.Field requiredLen) :=
  CPolynomial.NTT.bestDomainForLength? BabyBear.twoAdicity
    CPolynomial.NTT.BabyBear.domainOfLogN (by intro _ _; rfl) requiredLen

/-- NTT domain large enough for direct univariate KoalaBear multiplication benchmarks. -/
def koalaBearMulNttDomain : CPolynomial.NTT.Domain KoalaBear.Field :=
  CPolynomial.NTT.KoalaBear.domainOfLogN univariateMulLogN (by decide)

end CompPolyBench
