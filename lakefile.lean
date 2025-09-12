import Lake

open System Lake DSL

package CompPoly where version := v!"0.1.0"

require "leanprover-community" / mathlib @ git "v4.22.0-rc2"

require ExtTreeMapLemmas from git "https://github.com/NethermindEth/ExtTreeMapLemmas" @ "Ferinko/cleanup"

@[default_target]
lean_lib CompPoly
