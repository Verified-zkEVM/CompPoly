/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPoly.Bivariate.GuruswamiSudan.Context
import CompPoly.Bivariate.GuruswamiSudan.Core
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import CompPoly.Bivariate.GuruswamiSudan.Executable
import CompPoly.Bivariate.GuruswamiSudan.Filter
import CompPoly.Bivariate.GuruswamiSudan.FilterCorrectness
import CompPoly.Bivariate.GuruswamiSudan.Implementations
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Basic
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Polynomial
import CompPoly.Bivariate.GuruswamiSudan.PolynomialCorrectness
import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Root.Alekhnovich.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Root.Common
import CompPoly.Bivariate.GuruswamiSudan.Root.Common.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.FiniteField
import CompPoly.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Algorithm
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Root.RothRuckenstein.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Root.ShiftedSubstitution
import CompPoly.Bivariate.GuruswamiSudan.Root.ShiftedSubstitution.Lemmas
import CompPoly.Bivariate.GuruswamiSudan.Util

/-!
# Guruswami-Sudan Polynomial Kernels

Facade module re-exporting the executable CompPoly Guruswami-Sudan polynomial
core, backend contexts, and supporting interpolation/root modules.
-/
