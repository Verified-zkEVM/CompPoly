import Lake

open System Lake DSL

package CompPoly where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.27.0"

require ExtTreeMapLemmas from git "https://github.com/Verified-zkEVM/ExtTreeMapLemmas"@"v4.27.0"

@[default_target]
lean_lib CompPoly
