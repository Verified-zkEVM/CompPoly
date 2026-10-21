/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.FastExt4
public import CompPoly.Fields.Montgomery.InterpolateCosetPacked

/-!
# Compiled packed coset interpolation over KoalaBear

The `PackedInterpolation` instance for KoalaBear's quartic extension. Its `run` applies the generic
`InterpolatePacked.run` at KoalaBear's modulus, so the compiler specializes the loops here, in the
CPU-targeted `CompPolyInterpolateNative` library.
-/

@[expose] public section

namespace KoalaBear.Fast

open Montgomery.Native32

set_option maxHeartbeats 1000000 in
/-- Packed coset interpolation specialized to KoalaBear. -/
def interpolateCosetRun (logN : ℕ) (ω s : Field) (width : ℕ) (evals : ByteArray) (z : Ext4)
    (logTasks : ℕ) : Array Ext4 :=
  InterpolatePacked.run logN ω s width evals z logTasks

instance : PackedInterpolation KoalaBear.fieldSize := ⟨interpolateCosetRun, rfl⟩

end KoalaBear.Fast
