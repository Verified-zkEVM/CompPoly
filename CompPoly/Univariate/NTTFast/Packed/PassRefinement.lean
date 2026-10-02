/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Correctness.Radix4DIF
public import CompPoly.Univariate.NTTFast.Packed.LoopRefinement
public import CompPoly.Univariate.NTTFast.Packed.Folds

/-! # Packed radix-four pass refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed

/-- All vectorized blocks of one pass agree with the ordinary radix-four block loop. -/
theorem Native.fold_inner16_packFields (th tl : Array KoalaBear.Fast.Field)
    (q blocks : Nat) (a : Array KoalaBear.Fast.Field)
    (ha : (packFields a).size < USize.size)
    (hth : (packFields th).size < USize.size) (htl : (packFields tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size)
    (hbound : blocks * (4 * q) ≤ a.size) :
    (List.range blocks).foldl (fun acc block ↦
      Native.inner16 (packFields th) (packFields tl) q 0 (block * (4 * q))
        (block * (4 * q) + q) (block * (4 * q) + 2 * q) (block * (4 * q) + 3 * q) acc)
      (packFields a) =
      packFields (Plan.butterflyDIFRadix4Blocks th tl (4 * q) q blocks 0 a) := by
  rw [Plan.butterflyDIFRadix4Blocks_eq_foldl_inner th tl (4 * q) q blocks blocks 0 a (by omega),
    ← List.range_eq_range']
  apply foldl_packFields (List.range blocks) (fun b ↦ b.size = a.size)
  · intro block hb b hbs
    have hb' : block < blocks := List.mem_range.mp hb
    have hbase : block * (4 * q) + 4 * q ≤ a.size := by
      calc
        _ = (block + 1) * (4 * q) := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ blocks * (4 * q) := Nat.mul_le_mul_right (4 * q) (by omega)
        _ ≤ a.size := hbound
    exact Native.inner16_packFields th tl q 0 _ _ _ _ b
      (by simpa only [size_packFields, hbs] using ha) hth htl hthi htli
      (by omega) (by omega) (by omega) (by omega)
  · intro block hb b hbs
    simpa only [Plan.size_butterflyDIFRadix4Inner] using hbs
  · rfl

end CompPoly.CPolynomial.NTTFast.Packed
