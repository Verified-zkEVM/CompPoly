/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

/-!
# Guruswami-Sudan Shared Utilities

Small helpers shared by the interpolation and root-finding implementation
modules.
-/

namespace CompPoly

namespace GuruswamiSudan

/-- Count nonzero entries in a dense coefficient vector. -/
def nonzeroEntryCount {F : Type _} [Zero F] [BEq F] (v : Array F) : Nat :=
  v.foldl (fun count x ↦ if x == 0 then count else count + 1) 0

end GuruswamiSudan

end CompPoly
