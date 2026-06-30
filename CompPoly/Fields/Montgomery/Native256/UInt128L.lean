/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native256.Limb
import Mathlib.Tactic.Ring

/-!
# 128-bit limb word (`UInt128L`)

A two-`UInt64`-limb word used to hold the 64×64→128 partial products of the BN254 fast
field's schoolbook multiplication, with ripple-carry addition and its `Nat` contract.
-/

namespace Montgomery.Native256

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

/-- The two-limb ripple-carry addition agrees with `Nat` addition modulo `2 ^ 128`
(the 128-bit analogue of `UInt64.toNat_add`). -/
theorem UInt128L.toNat_add (a b : UInt128L) :
    (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 128 := by
  obtain ⟨e0, c0, hb0⟩ := addc_spec a.lo b.lo 0 (by decide)
  obtain ⟨e1, c1, hb1⟩ := addc_spec a.hi b.hi (addc a.lo b.lo 0).2 c0
  have hlo : (a + b).lo = (addc a.lo b.lo 0).1 := rfl
  have hhi : (a + b).hi = (addc a.hi b.hi (addc a.lo b.lo 0).2).1 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  -- A mod-free "key" identity (omega handles the `addc` carry chain only without `% 2^128`),
  -- then the modulus is discharged structurally to avoid an omega blow-up.
  have key : (addc a.lo b.lo 0).1.toNat
      + (addc a.hi b.hi (addc a.lo b.lo 0).2).1.toNat * 2 ^ 64
      + (addc a.hi b.hi (addc a.lo b.lo 0).2).2.toNat * 2 ^ 128
      = a.lo.toNat + b.lo.toNat + (a.hi.toNat + b.hi.toNat) * 2 ^ 64 := by omega
  have hbnd : (addc a.lo b.lo 0).1.toNat
      + (addc a.hi b.hi (addc a.lo b.lo 0).2).1.toNat * 2 ^ 64 < 2 ^ 128 := by omega
  simp only [UInt128L.toNat, Nat.shiftLeft_eq, hlo, hhi]
  rw [show a.lo.toNat + a.hi.toNat * 2 ^ 64 + (b.lo.toNat + b.hi.toNat * 2 ^ 64)
        = a.lo.toNat + b.lo.toNat + (a.hi.toNat + b.hi.toNat) * 2 ^ 64 from by ring,
      ← key, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbnd]

end Montgomery.Native256
