import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.30.0-rc2"

@[default_target]
lean_lib CompPoly

lean_lib CompPolyTests where
  srcDir := "tests"

lean_lib CompPolyBenchSupport where
  srcDir := "bench"
  roots := #[
    `CompPolyBench.Bivariate.Basic,
    `CompPolyBench.Common,
    `CompPolyBench.Fields.Binary.AdditiveNTT.Impl,
    `CompPolyBench.Multilinear.Basic,
    `CompPolyBench.Multivariate.CMvPolynomial,
    `CompPolyBench.Setup,
    `CompPolyBench.Univariate,
    `CompPolyBench.Univariate.Basic,
    `CompPolyBench.Univariate.BatchEval,
    `CompPolyBench.Univariate.Common,
    `CompPolyBench.Univariate.NTT.FastMul,
    `CompPolyBench.Univariate.NTT.FastMulLow
  ]

lean_exe CompPolyBench where
  srcDir := "bench"
