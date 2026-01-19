import Lake

open System Lake DSL

package CompPoly where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.26.0"

require ExtTreeMapLemmas from git "https://github.com/Verified-zkEVM/ExtTreeMapLemmas"

@[default_target]
lean_lib CompPoly
