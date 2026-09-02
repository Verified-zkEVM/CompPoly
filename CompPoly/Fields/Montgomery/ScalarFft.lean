/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.Montgomery.Native64x8Defs

/-!
# Radix-2 DIT FFT over eight-limb Montgomery elements (zero-import)

An in-place radix-2 decimation-in-time FFT over `Limbs8` Montgomery residues: a bit-reversal
permutation followed by `logN` rounds of butterflies against a precomputed Montgomery-form
twiddle table.  Like the arithmetic in `CompPoly.Fields.Montgomery.Native64x8Defs`, the loop
nest is generic over the modulus, taking `q` and `negInv` explicitly.

As explained in `CompPoly.Fields.Montgomery.Native64x8Defs`, this module deliberately imports
nothing beyond that (itself zero-import) module: downstream consumers put it into
`precompileModules` native-compilation lanes, and `precompileModules` compiles the
entire import closure — so the runtime definitions must not pull in mathlib.

This module contains runtime definitions only; correctness specifications live downstream
for now.
-/

@[expose] public section

namespace Montgomery
namespace ScalarFft

open Native64x8 (Limbs8 add sub mul)

/-- Bit-reversal permutation index. -/
def bitreverse (n l : Nat) : Nat := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- In-place radix-2 DIT FFT over eight-limb Montgomery residues modulo `q`: bit-reversal
permutation, then `logN` rounds of butterflies against the Montgomery-form twiddles `tw`. -/
def fft (q : Limbs8) (negInv : UInt64) (a0 : Array Limbs8) (tw : Array Limbs8)
    (logN : Nat) : Array Limbs8 := Id.run do
  let n := a0.size
  let mut a := a0
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := mul q negInv twdl a[bIdx]!
        a := a.set! aIdx (add q aOld t)
        a := a.set! bIdx (sub q aOld t)
    half := chunk
  return a

end ScalarFft
end Montgomery
