/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

/-!
# Single-limb add-with-carry (`addc`)

The 64-bit add-with-carry primitive of the proof-free binary-GCD engine.
-/

namespace Montgomery.Native256

/-- One limb of add-with-carry: `(dᵢ, carry')`, with `carry' ∈ {0,1}` when `c ∈ {0,1}`. -/
@[inline] def addc (a b c : UInt64) : UInt64 × UInt64 :=
  let s1 := a + b
  let c1 := if s1 < a then 1 else 0
  let s2 := s1 + c
  let c2 := if s2 < s1 then 1 else 0
  (s2, c1 + c2)

end Montgomery.Native256
