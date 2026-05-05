import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.29.1"

require ExtTreeMapLemmas from git "https://github.com/Verified-zkEVM/ExtTreeMapLemmas"@"v4.29.1"

@[default_target]
lean_lib CompPoly

lean_lib CompPolyTests where
  srcDir := "tests"
