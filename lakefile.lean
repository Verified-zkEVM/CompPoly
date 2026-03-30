import Lake

open System Lake DSL

package CompPoly where
  version := v!"0.1.0"
  testDriver := "CompPolyTests"

require "leanprover-community" / mathlib @ git "v4.28.0"

require ExtTreeMapLemmas from git "https://github.com/quangvdao/ExtTreeMapLemmas"@"ed753cfcaa1ad3699e204899a0136ffa2383526c"

@[default_target]
lean_lib CompPoly

lean_lib CompPolyTests where
  srcDir := "tests"
