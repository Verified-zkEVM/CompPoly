/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import CompPolyTests.Bivariate.Basic
import CompPolyTests.Bivariate.Degree
import CompPolyTests.Bivariate.Factor
import CompPolyTests.Bivariate.Kronecker
import CompPolyTests.Bivariate.Deriv
import CompPolyTests.Bivariate.GuruswamiSudan.Compose
import CompPolyTests.Bivariate.GuruswamiSudan.Core
import CompPolyTests.Bivariate.GuruswamiSudan.Filter
import CompPolyTests.Bivariate.GuruswamiSudan.Hasse
import CompPolyTests.Bivariate.GuruswamiSudan.Interpolation.Dense
import CompPolyTests.Bivariate.GuruswamiSudan.Interpolation.LeeOSullivan
import CompPolyTests.Bivariate.GuruswamiSudan.Root.Alekhnovich
import CompPolyTests.Bivariate.GuruswamiSudan.Root.FieldRoots.KoalaBear
import CompPolyTests.Bivariate.GuruswamiSudan.Root.RothRuckenstein
import CompPolyTests.Bivariate.Multiplicity
import CompPolyTests.Bivariate.WeightedDegree
import CompPolyTests.Data.MvPolynomial.Notation
import CompPolyTests.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
import CompPolyTests.Fields.Binary.BF128Ghash.Prelude
import CompPolyTests.Fields.KoalaBear.Fast
import CompPolyTests.Fields.Mersenne31
import CompPolyTests.Fields.PrattCertificate
import CompPolyTests.LinearAlgebra.Dense
import CompPolyTests.Multilinear.Equiv
import CompPolyTests.Multivariate.CMvMonomial
import CompPolyTests.Multivariate.Restrict
import CompPolyTests.Multivariate.TypeclassMinimization
import CompPolyTests.Multivariate.VarsDegrees
import CompPolyTests.Univariate.Barycentric
import CompPolyTests.Univariate.Basic
import CompPolyTests.Univariate.EuclideanAlgorithm
import CompPolyTests.Univariate.Linear
import CompPolyTests.Univariate.NTT.FastMul
import CompPolyTests.Univariate.NTT.Forward
import CompPolyTests.Univariate.NTT.Inverse
import CompPolyTests.Univariate.Raw
import CompPolyTests.Univariate.Roots.Enumeration
import CompPolyTests.Univariate.Roots.FiniteField
import CompPolyTests.Univariate.ToPoly
