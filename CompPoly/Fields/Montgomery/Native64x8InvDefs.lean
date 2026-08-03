/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/

import CompPoly.Fields.Montgomery.Native64x8Defs
import CompPoly.Fields.Montgomery.Native256Gcd

/-!
# Eight-limb inversion: runtime definitions (Mathlib-free)

The checked binary-GCD inverse over raw `Limbs8`, completing the Mathlib-free defs
surface of `Montgomery/Native64x8Defs`. Runtime definitions only; the proof-carrying
path is `Montgomery.Native64x8.FastField.invGcd`.
-/

namespace Montgomery.Native64x8

/-! ## Limb conversions -/

/-- Pack eight 32-bit limbs into four 64-bit limbs (canonical inputs: high halves zero). -/
@[inline] def Limbs8.toUInt256L (x : Limbs8) : Native256.UInt256L :=
  ⟨x.l0 ||| (x.l1 <<< 32), x.l2 ||| (x.l3 <<< 32),
   x.l4 ||| (x.l5 <<< 32), x.l6 ||| (x.l7 <<< 32)⟩

/-- Split four 64-bit limbs into eight 32-bit limbs. -/
@[inline] def Limbs8.ofUInt256L (x : Native256.UInt256L) : Limbs8 :=
  ⟨x.l0 &&& 0xffffffff, x.l0 >>> 32, x.l1 &&& 0xffffffff, x.l1 >>> 32,
   x.l2 &&& 0xffffffff, x.l2 >>> 32, x.l3 &&& 0xffffffff, x.l3 >>> 32⟩

/-! ## Inversion -/

/-- `x^n` in Montgomery form by binary powering; `rMod` is the Montgomery one. -/
def montPow (q : Limbs8) (negInv : UInt64) (rMod : Limbs8) (x : Limbs8) (n : Nat) :
    Limbs8 := Id.run do
  let mut acc := rMod
  let mut base := x
  let mut e := n
  for _ in [0:256] do
    if e == 0 then return acc
    if e % 2 == 1 then acc := mul q negInv acc base
    base := mul q negInv base base
    e := e >>> 1
  return acc

/-- The shared 64-bit GCD candidate, accepted only if it verifies (`z · x = 1`); else
Fermat `montPow`. -/
def invGcdRaw (modulus : Nat) [Native256.Mont256Field modulus] (q : Limbs8) (negInv : UInt64)
    (rMod : Limbs8) (x : Limbs8) : Limbs8 :=
  let cand := Limbs8.ofUInt256L (Native256.gcdInvCandidate (modulus := modulus) x.toUInt256L)
  if cand.Bounded ∧ subBorrow cand q = 1 ∧ mul q negInv cand x = rMod then cand
  else montPow q negInv rMod x (modulus - 2)

end Montgomery.Native64x8
