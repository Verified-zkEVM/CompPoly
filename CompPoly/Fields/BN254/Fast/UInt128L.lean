/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Fast.Limb

namespace BN254.Fast

structure UInt128L where
  lo : UInt64
  hi : UInt64
deriving DecidableEq

def UInt128L.toNat (x : UInt128L) : Nat :=
  x.lo.toNat + (x.hi.toNat <<< 64)


@[inline] def UInt128L.add (a b : UInt128L) : UInt128L :=
  let (lo, c0) := addc a.lo b.lo 0
  let (hi, _) := addc a.hi b.hi c0
  ⟨ lo, hi ⟩

instance : Add UInt128L := ⟨ UInt128L.add ⟩


end BN254.Fast
