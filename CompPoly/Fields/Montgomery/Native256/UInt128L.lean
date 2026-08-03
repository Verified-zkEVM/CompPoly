/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256.Limb

/-!
# 128-bit limb word (`UInt128L`)

A two-`UInt64`-limb word holding the 64×64→128 partial products of the schoolbook
multiplication.
-/

namespace Montgomery.Native256

/-- A 128-bit value as two 64-bit limbs. -/
structure UInt128L where
  /-- Limb of weight `2 ^ 0`. -/
  lo : UInt64
  /-- Limb of weight `2 ^ 64`. -/
  hi : UInt64
deriving DecidableEq

/-- Two-limb ripple-carry addition, discarding the carry out of the top limb. -/
@[inline] def UInt128L.add (a b : UInt128L) : UInt128L :=
  let (lo, c0) := addc a.lo b.lo 0
  let (hi, _) := addc a.hi b.hi c0
  ⟨lo, hi⟩

instance : Add UInt128L := ⟨UInt128L.add⟩

end Montgomery.Native256
