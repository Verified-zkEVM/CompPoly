/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Raikos
-/
module

/-!
# Word-sized divsteps: runtime definitions (zero-import)

The word-sized divstep loop of the Pornin binary-GCD inversion
([eprint 2020/972](https://eprint.iacr.org/2020/972)) and its bit-length helper. Both act on
single `UInt64` words, so they do not depend on the limb count of a Montgomery carrier. The
multi-limb inversion runtimes call them on one-word approximations of their operands.

This module has zero imports, for `precompileModules` consumers. The proof side is
`Montgomery/Divstep`.
-/

@[expose] public section

namespace Montgomery

/-- Bit length of a word. -/
@[inline] def gcdBitLen (x : UInt64) : Nat := Id.run do
  if x == 0 then return 0
  let mut v := x
  let mut r : Nat := 1
  if v >>> (32 : UInt64) != 0 then v := v >>> (32 : UInt64); r := r + 32
  if v >>> (16 : UInt64) != 0 then v := v >>> (16 : UInt64); r := r + 16
  if v >>> (8 : UInt64) != 0 then v := v >>> (8 : UInt64); r := r + 8
  if v >>> (4 : UInt64) != 0 then v := v >>> (4 : UInt64); r := r + 4
  if v >>> (2 : UInt64) != 0 then v := v >>> (2 : UInt64); r := r + 2
  if v >>> (1 : UInt64) != 0 then r := r + 1
  return r

/-- The word-sized divstep loop, accumulating the transition matrix; `b` must be odd. -/
def gcdInner (rounds : Nat) (a b : UInt64) (f0 g0 f1 g1 : Int) :
    UInt64 × UInt64 × Int × Int × Int × Int :=
  match rounds with
  | 0 => (a, b, f0, g0, f1, g1)
  | n + 1 =>
    let (a, b, f0, g0, f1, g1) :=
      if a &&& 1 == 0 then
        (a, b, f0, g0, f1, g1)
      else
        let (a, b, f0, g0, f1, g1) :=
          if a < b then (b, a, f1, g1, f0, g0) else (a, b, f0, g0, f1, g1)
        (a - b, b, f0 - f1, g0 - g1, f1, g1)
    gcdInner n (a >>> 1) b f0 g0 (f1 * 2) (g1 * 2)

end Montgomery
