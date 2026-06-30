/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.BN254.Basic
import CompPoly.Fields.BN254.Fast.UInt256L

/-!
# Fast BN254 Scalar Field — Basics

The native-word modulus constant and the `ScalarField` carrier type (a `UInt256L` below the
prime) for the fast BN254 scalar field, plus the `decide`-checked numeric facts that the
Montgomery layer builds on.
-/

namespace BN254
namespace Fast


def modulus: UInt256L :=
  { l0 := 0x43e1f593f0000001,
    l1 := 0x2833e84879b97091,
    l2 := 0xb85045b68181585d,
    l3 := 0x30644e72e131a029 }

abbrev ScalarField : Type := {x : UInt256L // x.toNat < modulus.toNat}

instance : DecidableEq ScalarField := inferInstance

/-- The raw Montgomery word backing a fast BN254 scalar-field element. -/
@[inline]
def raw (x : ScalarField) : UInt256L := x.val

@[simp] theorem modulus_toNat : modulus.toNat = BN254.scalarFieldSize := by
  decide

/-- Twice the scalar-field modulus still fits in 256 bits, so a sum of two reduced
residues never overflows the limb word and a single conditional subtract reduces it. -/
theorem two_mul_scalarFieldSize_lt_two256 : 2 * BN254.scalarFieldSize < 2 ^ 256 := by
  decide



end Fast
end BN254
