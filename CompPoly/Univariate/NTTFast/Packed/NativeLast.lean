/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.NativeOrder

/-! # Fused final leaf layers and leaf reversal

The last four DIF layers of a leaf act inside sixteen-word blocks, and the leaf reversal then
reads one word from each of sixteen blocks `L` words apart, `L = 2 ^ (m - 4)`. `lastHalf` runs
both for eight such blocks at once, one block per vector lane, and writes eight words of each of
sixteen natural-order lines; two calls per batch of sixteen block columns complete the lines.
This replaces the scalar in-block kernel `leaf16` and the separate `leafRev` pass for even
leaves of at least `2 ^ 8` words.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed.Native

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The last four DIF layers of the eight blocks at `i0, …, i7`, written to `out` as
half `half` of the natural-order lines `bitrev (16 c + t)`: lane `k` supplies word
`8 half + k` of each line, optionally scaled. The lanes are independent, so the compiler
runs them as vector lanes. -/
@[noinline] def lastHalf (t3 t2 t1 b : @& ByteArray) (i0 i1 i2 i3 i4 i5 i6 i7 c : USize)
    (shift : UInt32) (half : USize) (factor : UInt32) (scale : Bool) (out : ByteArray)
    (h : 4 * (i0.toNat + 15) + 3 < b.size ∧
      4 * (i1.toNat + 15) + 3 < b.size ∧
      4 * (i2.toNat + 15) + 3 < b.size ∧
      4 * (i3.toNat + 15) + 3 < b.size ∧
      4 * (i4.toNat + 15) + 3 < b.size ∧
      4 * (i5.toNat + 15) + 3 < b.size ∧
      4 * (i6.toNat + 15) + 3 < b.size ∧
      4 * (i7.toNat + 15) + 3 < b.size ∧
      b.size < USize.size ∧
      31 < t3.size ∧
      t3.size < USize.size ∧
      15 < t2.size ∧
      t2.size < USize.size ∧
      7 < t1.size ∧
      t1.size < USize.size) :
    ByteArray :=
  let w0_1 := readUOffset t3 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let w0_2 := readUOffset t3 0 2 (by
      rw [usize_numeral 0 (by decide), usize_numeral 2 (by decide)]
      omega)
  let w0_3 := readUOffset t3 0 3 (by
      rw [usize_numeral 0 (by decide), usize_numeral 3 (by decide)]
      omega)
  let w0_4 := readUOffset t3 0 4 (by
      rw [usize_numeral 0 (by decide), usize_numeral 4 (by decide)]
      omega)
  let w0_5 := readUOffset t3 0 5 (by
      rw [usize_numeral 0 (by decide), usize_numeral 5 (by decide)]
      omega)
  let w0_6 := readUOffset t3 0 6 (by
      rw [usize_numeral 0 (by decide), usize_numeral 6 (by decide)]
      omega)
  let w0_7 := readUOffset t3 0 7 (by
      rw [usize_numeral 0 (by decide), usize_numeral 7 (by decide)]
      omega)
  let w1_1 := readUOffset t2 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let w1_2 := readUOffset t2 0 2 (by
      rw [usize_numeral 0 (by decide), usize_numeral 2 (by decide)]
      omega)
  let w1_3 := readUOffset t2 0 3 (by
      rw [usize_numeral 0 (by decide), usize_numeral 3 (by decide)]
      omega)
  let w2_1 := readUOffset t1 0 1 (by
      rw [usize_numeral 0 (by decide), usize_numeral 1 (by decide)]
      omega)
  let x0_0_0 := readUOffset b i0 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x0_0_1 := readUOffset b i0 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x0_0_2 := readUOffset b i0 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x0_0_3 := readUOffset b i0 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x0_0_4 := readUOffset b i0 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x0_0_5 := readUOffset b i0 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x0_0_6 := readUOffset b i0 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x0_0_7 := readUOffset b i0 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x0_0_8 := readUOffset b i0 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x0_0_9 := readUOffset b i0 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x0_0_10 := readUOffset b i0 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x0_0_11 := readUOffset b i0 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x0_0_12 := readUOffset b i0 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x0_0_13 := readUOffset b i0 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x0_0_14 := readUOffset b i0 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x0_0_15 := readUOffset b i0 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x0_1_0 := add x0_0_0 x0_0_8
  let x0_1_8 := sub x0_0_0 x0_0_8
  let x0_1_1 := add x0_0_1 x0_0_9
  let x0_1_9 := mul w0_1 (sub x0_0_1 x0_0_9)
  let x0_1_2 := add x0_0_2 x0_0_10
  let x0_1_10 := mul w0_2 (sub x0_0_2 x0_0_10)
  let x0_1_3 := add x0_0_3 x0_0_11
  let x0_1_11 := mul w0_3 (sub x0_0_3 x0_0_11)
  let x0_1_4 := add x0_0_4 x0_0_12
  let x0_1_12 := mul w0_4 (sub x0_0_4 x0_0_12)
  let x0_1_5 := add x0_0_5 x0_0_13
  let x0_1_13 := mul w0_5 (sub x0_0_5 x0_0_13)
  let x0_1_6 := add x0_0_6 x0_0_14
  let x0_1_14 := mul w0_6 (sub x0_0_6 x0_0_14)
  let x0_1_7 := add x0_0_7 x0_0_15
  let x0_1_15 := mul w0_7 (sub x0_0_7 x0_0_15)
  let x0_2_0 := add x0_1_0 x0_1_4
  let x0_2_4 := sub x0_1_0 x0_1_4
  let x0_2_1 := add x0_1_1 x0_1_5
  let x0_2_5 := mul w1_1 (sub x0_1_1 x0_1_5)
  let x0_2_2 := add x0_1_2 x0_1_6
  let x0_2_6 := mul w1_2 (sub x0_1_2 x0_1_6)
  let x0_2_3 := add x0_1_3 x0_1_7
  let x0_2_7 := mul w1_3 (sub x0_1_3 x0_1_7)
  let x0_2_8 := add x0_1_8 x0_1_12
  let x0_2_12 := sub x0_1_8 x0_1_12
  let x0_2_9 := add x0_1_9 x0_1_13
  let x0_2_13 := mul w1_1 (sub x0_1_9 x0_1_13)
  let x0_2_10 := add x0_1_10 x0_1_14
  let x0_2_14 := mul w1_2 (sub x0_1_10 x0_1_14)
  let x0_2_11 := add x0_1_11 x0_1_15
  let x0_2_15 := mul w1_3 (sub x0_1_11 x0_1_15)
  let x0_3_0 := add x0_2_0 x0_2_2
  let x0_3_2 := sub x0_2_0 x0_2_2
  let x0_3_1 := add x0_2_1 x0_2_3
  let x0_3_3 := mul w2_1 (sub x0_2_1 x0_2_3)
  let x0_3_4 := add x0_2_4 x0_2_6
  let x0_3_6 := sub x0_2_4 x0_2_6
  let x0_3_5 := add x0_2_5 x0_2_7
  let x0_3_7 := mul w2_1 (sub x0_2_5 x0_2_7)
  let x0_3_8 := add x0_2_8 x0_2_10
  let x0_3_10 := sub x0_2_8 x0_2_10
  let x0_3_9 := add x0_2_9 x0_2_11
  let x0_3_11 := mul w2_1 (sub x0_2_9 x0_2_11)
  let x0_3_12 := add x0_2_12 x0_2_14
  let x0_3_14 := sub x0_2_12 x0_2_14
  let x0_3_13 := add x0_2_13 x0_2_15
  let x0_3_15 := mul w2_1 (sub x0_2_13 x0_2_15)
  let x0_4_0 := add x0_3_0 x0_3_1
  let x0_4_1 := sub x0_3_0 x0_3_1
  let x0_4_2 := add x0_3_2 x0_3_3
  let x0_4_3 := sub x0_3_2 x0_3_3
  let x0_4_4 := add x0_3_4 x0_3_5
  let x0_4_5 := sub x0_3_4 x0_3_5
  let x0_4_6 := add x0_3_6 x0_3_7
  let x0_4_7 := sub x0_3_6 x0_3_7
  let x0_4_8 := add x0_3_8 x0_3_9
  let x0_4_9 := sub x0_3_8 x0_3_9
  let x0_4_10 := add x0_3_10 x0_3_11
  let x0_4_11 := sub x0_3_10 x0_3_11
  let x0_4_12 := add x0_3_12 x0_3_13
  let x0_4_13 := sub x0_3_12 x0_3_13
  let x0_4_14 := add x0_3_14 x0_3_15
  let x0_4_15 := sub x0_3_14 x0_3_15
  let x1_0_0 := readUOffset b i1 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x1_0_1 := readUOffset b i1 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x1_0_2 := readUOffset b i1 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x1_0_3 := readUOffset b i1 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x1_0_4 := readUOffset b i1 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x1_0_5 := readUOffset b i1 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x1_0_6 := readUOffset b i1 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x1_0_7 := readUOffset b i1 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x1_0_8 := readUOffset b i1 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x1_0_9 := readUOffset b i1 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x1_0_10 := readUOffset b i1 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x1_0_11 := readUOffset b i1 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x1_0_12 := readUOffset b i1 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x1_0_13 := readUOffset b i1 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x1_0_14 := readUOffset b i1 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x1_0_15 := readUOffset b i1 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x1_1_0 := add x1_0_0 x1_0_8
  let x1_1_8 := sub x1_0_0 x1_0_8
  let x1_1_1 := add x1_0_1 x1_0_9
  let x1_1_9 := mul w0_1 (sub x1_0_1 x1_0_9)
  let x1_1_2 := add x1_0_2 x1_0_10
  let x1_1_10 := mul w0_2 (sub x1_0_2 x1_0_10)
  let x1_1_3 := add x1_0_3 x1_0_11
  let x1_1_11 := mul w0_3 (sub x1_0_3 x1_0_11)
  let x1_1_4 := add x1_0_4 x1_0_12
  let x1_1_12 := mul w0_4 (sub x1_0_4 x1_0_12)
  let x1_1_5 := add x1_0_5 x1_0_13
  let x1_1_13 := mul w0_5 (sub x1_0_5 x1_0_13)
  let x1_1_6 := add x1_0_6 x1_0_14
  let x1_1_14 := mul w0_6 (sub x1_0_6 x1_0_14)
  let x1_1_7 := add x1_0_7 x1_0_15
  let x1_1_15 := mul w0_7 (sub x1_0_7 x1_0_15)
  let x1_2_0 := add x1_1_0 x1_1_4
  let x1_2_4 := sub x1_1_0 x1_1_4
  let x1_2_1 := add x1_1_1 x1_1_5
  let x1_2_5 := mul w1_1 (sub x1_1_1 x1_1_5)
  let x1_2_2 := add x1_1_2 x1_1_6
  let x1_2_6 := mul w1_2 (sub x1_1_2 x1_1_6)
  let x1_2_3 := add x1_1_3 x1_1_7
  let x1_2_7 := mul w1_3 (sub x1_1_3 x1_1_7)
  let x1_2_8 := add x1_1_8 x1_1_12
  let x1_2_12 := sub x1_1_8 x1_1_12
  let x1_2_9 := add x1_1_9 x1_1_13
  let x1_2_13 := mul w1_1 (sub x1_1_9 x1_1_13)
  let x1_2_10 := add x1_1_10 x1_1_14
  let x1_2_14 := mul w1_2 (sub x1_1_10 x1_1_14)
  let x1_2_11 := add x1_1_11 x1_1_15
  let x1_2_15 := mul w1_3 (sub x1_1_11 x1_1_15)
  let x1_3_0 := add x1_2_0 x1_2_2
  let x1_3_2 := sub x1_2_0 x1_2_2
  let x1_3_1 := add x1_2_1 x1_2_3
  let x1_3_3 := mul w2_1 (sub x1_2_1 x1_2_3)
  let x1_3_4 := add x1_2_4 x1_2_6
  let x1_3_6 := sub x1_2_4 x1_2_6
  let x1_3_5 := add x1_2_5 x1_2_7
  let x1_3_7 := mul w2_1 (sub x1_2_5 x1_2_7)
  let x1_3_8 := add x1_2_8 x1_2_10
  let x1_3_10 := sub x1_2_8 x1_2_10
  let x1_3_9 := add x1_2_9 x1_2_11
  let x1_3_11 := mul w2_1 (sub x1_2_9 x1_2_11)
  let x1_3_12 := add x1_2_12 x1_2_14
  let x1_3_14 := sub x1_2_12 x1_2_14
  let x1_3_13 := add x1_2_13 x1_2_15
  let x1_3_15 := mul w2_1 (sub x1_2_13 x1_2_15)
  let x1_4_0 := add x1_3_0 x1_3_1
  let x1_4_1 := sub x1_3_0 x1_3_1
  let x1_4_2 := add x1_3_2 x1_3_3
  let x1_4_3 := sub x1_3_2 x1_3_3
  let x1_4_4 := add x1_3_4 x1_3_5
  let x1_4_5 := sub x1_3_4 x1_3_5
  let x1_4_6 := add x1_3_6 x1_3_7
  let x1_4_7 := sub x1_3_6 x1_3_7
  let x1_4_8 := add x1_3_8 x1_3_9
  let x1_4_9 := sub x1_3_8 x1_3_9
  let x1_4_10 := add x1_3_10 x1_3_11
  let x1_4_11 := sub x1_3_10 x1_3_11
  let x1_4_12 := add x1_3_12 x1_3_13
  let x1_4_13 := sub x1_3_12 x1_3_13
  let x1_4_14 := add x1_3_14 x1_3_15
  let x1_4_15 := sub x1_3_14 x1_3_15
  let x2_0_0 := readUOffset b i2 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x2_0_1 := readUOffset b i2 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x2_0_2 := readUOffset b i2 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x2_0_3 := readUOffset b i2 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x2_0_4 := readUOffset b i2 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x2_0_5 := readUOffset b i2 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x2_0_6 := readUOffset b i2 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x2_0_7 := readUOffset b i2 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x2_0_8 := readUOffset b i2 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x2_0_9 := readUOffset b i2 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x2_0_10 := readUOffset b i2 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x2_0_11 := readUOffset b i2 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x2_0_12 := readUOffset b i2 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x2_0_13 := readUOffset b i2 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x2_0_14 := readUOffset b i2 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x2_0_15 := readUOffset b i2 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x2_1_0 := add x2_0_0 x2_0_8
  let x2_1_8 := sub x2_0_0 x2_0_8
  let x2_1_1 := add x2_0_1 x2_0_9
  let x2_1_9 := mul w0_1 (sub x2_0_1 x2_0_9)
  let x2_1_2 := add x2_0_2 x2_0_10
  let x2_1_10 := mul w0_2 (sub x2_0_2 x2_0_10)
  let x2_1_3 := add x2_0_3 x2_0_11
  let x2_1_11 := mul w0_3 (sub x2_0_3 x2_0_11)
  let x2_1_4 := add x2_0_4 x2_0_12
  let x2_1_12 := mul w0_4 (sub x2_0_4 x2_0_12)
  let x2_1_5 := add x2_0_5 x2_0_13
  let x2_1_13 := mul w0_5 (sub x2_0_5 x2_0_13)
  let x2_1_6 := add x2_0_6 x2_0_14
  let x2_1_14 := mul w0_6 (sub x2_0_6 x2_0_14)
  let x2_1_7 := add x2_0_7 x2_0_15
  let x2_1_15 := mul w0_7 (sub x2_0_7 x2_0_15)
  let x2_2_0 := add x2_1_0 x2_1_4
  let x2_2_4 := sub x2_1_0 x2_1_4
  let x2_2_1 := add x2_1_1 x2_1_5
  let x2_2_5 := mul w1_1 (sub x2_1_1 x2_1_5)
  let x2_2_2 := add x2_1_2 x2_1_6
  let x2_2_6 := mul w1_2 (sub x2_1_2 x2_1_6)
  let x2_2_3 := add x2_1_3 x2_1_7
  let x2_2_7 := mul w1_3 (sub x2_1_3 x2_1_7)
  let x2_2_8 := add x2_1_8 x2_1_12
  let x2_2_12 := sub x2_1_8 x2_1_12
  let x2_2_9 := add x2_1_9 x2_1_13
  let x2_2_13 := mul w1_1 (sub x2_1_9 x2_1_13)
  let x2_2_10 := add x2_1_10 x2_1_14
  let x2_2_14 := mul w1_2 (sub x2_1_10 x2_1_14)
  let x2_2_11 := add x2_1_11 x2_1_15
  let x2_2_15 := mul w1_3 (sub x2_1_11 x2_1_15)
  let x2_3_0 := add x2_2_0 x2_2_2
  let x2_3_2 := sub x2_2_0 x2_2_2
  let x2_3_1 := add x2_2_1 x2_2_3
  let x2_3_3 := mul w2_1 (sub x2_2_1 x2_2_3)
  let x2_3_4 := add x2_2_4 x2_2_6
  let x2_3_6 := sub x2_2_4 x2_2_6
  let x2_3_5 := add x2_2_5 x2_2_7
  let x2_3_7 := mul w2_1 (sub x2_2_5 x2_2_7)
  let x2_3_8 := add x2_2_8 x2_2_10
  let x2_3_10 := sub x2_2_8 x2_2_10
  let x2_3_9 := add x2_2_9 x2_2_11
  let x2_3_11 := mul w2_1 (sub x2_2_9 x2_2_11)
  let x2_3_12 := add x2_2_12 x2_2_14
  let x2_3_14 := sub x2_2_12 x2_2_14
  let x2_3_13 := add x2_2_13 x2_2_15
  let x2_3_15 := mul w2_1 (sub x2_2_13 x2_2_15)
  let x2_4_0 := add x2_3_0 x2_3_1
  let x2_4_1 := sub x2_3_0 x2_3_1
  let x2_4_2 := add x2_3_2 x2_3_3
  let x2_4_3 := sub x2_3_2 x2_3_3
  let x2_4_4 := add x2_3_4 x2_3_5
  let x2_4_5 := sub x2_3_4 x2_3_5
  let x2_4_6 := add x2_3_6 x2_3_7
  let x2_4_7 := sub x2_3_6 x2_3_7
  let x2_4_8 := add x2_3_8 x2_3_9
  let x2_4_9 := sub x2_3_8 x2_3_9
  let x2_4_10 := add x2_3_10 x2_3_11
  let x2_4_11 := sub x2_3_10 x2_3_11
  let x2_4_12 := add x2_3_12 x2_3_13
  let x2_4_13 := sub x2_3_12 x2_3_13
  let x2_4_14 := add x2_3_14 x2_3_15
  let x2_4_15 := sub x2_3_14 x2_3_15
  let x3_0_0 := readUOffset b i3 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x3_0_1 := readUOffset b i3 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x3_0_2 := readUOffset b i3 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x3_0_3 := readUOffset b i3 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x3_0_4 := readUOffset b i3 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x3_0_5 := readUOffset b i3 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x3_0_6 := readUOffset b i3 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x3_0_7 := readUOffset b i3 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x3_0_8 := readUOffset b i3 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x3_0_9 := readUOffset b i3 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x3_0_10 := readUOffset b i3 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x3_0_11 := readUOffset b i3 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x3_0_12 := readUOffset b i3 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x3_0_13 := readUOffset b i3 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x3_0_14 := readUOffset b i3 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x3_0_15 := readUOffset b i3 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x3_1_0 := add x3_0_0 x3_0_8
  let x3_1_8 := sub x3_0_0 x3_0_8
  let x3_1_1 := add x3_0_1 x3_0_9
  let x3_1_9 := mul w0_1 (sub x3_0_1 x3_0_9)
  let x3_1_2 := add x3_0_2 x3_0_10
  let x3_1_10 := mul w0_2 (sub x3_0_2 x3_0_10)
  let x3_1_3 := add x3_0_3 x3_0_11
  let x3_1_11 := mul w0_3 (sub x3_0_3 x3_0_11)
  let x3_1_4 := add x3_0_4 x3_0_12
  let x3_1_12 := mul w0_4 (sub x3_0_4 x3_0_12)
  let x3_1_5 := add x3_0_5 x3_0_13
  let x3_1_13 := mul w0_5 (sub x3_0_5 x3_0_13)
  let x3_1_6 := add x3_0_6 x3_0_14
  let x3_1_14 := mul w0_6 (sub x3_0_6 x3_0_14)
  let x3_1_7 := add x3_0_7 x3_0_15
  let x3_1_15 := mul w0_7 (sub x3_0_7 x3_0_15)
  let x3_2_0 := add x3_1_0 x3_1_4
  let x3_2_4 := sub x3_1_0 x3_1_4
  let x3_2_1 := add x3_1_1 x3_1_5
  let x3_2_5 := mul w1_1 (sub x3_1_1 x3_1_5)
  let x3_2_2 := add x3_1_2 x3_1_6
  let x3_2_6 := mul w1_2 (sub x3_1_2 x3_1_6)
  let x3_2_3 := add x3_1_3 x3_1_7
  let x3_2_7 := mul w1_3 (sub x3_1_3 x3_1_7)
  let x3_2_8 := add x3_1_8 x3_1_12
  let x3_2_12 := sub x3_1_8 x3_1_12
  let x3_2_9 := add x3_1_9 x3_1_13
  let x3_2_13 := mul w1_1 (sub x3_1_9 x3_1_13)
  let x3_2_10 := add x3_1_10 x3_1_14
  let x3_2_14 := mul w1_2 (sub x3_1_10 x3_1_14)
  let x3_2_11 := add x3_1_11 x3_1_15
  let x3_2_15 := mul w1_3 (sub x3_1_11 x3_1_15)
  let x3_3_0 := add x3_2_0 x3_2_2
  let x3_3_2 := sub x3_2_0 x3_2_2
  let x3_3_1 := add x3_2_1 x3_2_3
  let x3_3_3 := mul w2_1 (sub x3_2_1 x3_2_3)
  let x3_3_4 := add x3_2_4 x3_2_6
  let x3_3_6 := sub x3_2_4 x3_2_6
  let x3_3_5 := add x3_2_5 x3_2_7
  let x3_3_7 := mul w2_1 (sub x3_2_5 x3_2_7)
  let x3_3_8 := add x3_2_8 x3_2_10
  let x3_3_10 := sub x3_2_8 x3_2_10
  let x3_3_9 := add x3_2_9 x3_2_11
  let x3_3_11 := mul w2_1 (sub x3_2_9 x3_2_11)
  let x3_3_12 := add x3_2_12 x3_2_14
  let x3_3_14 := sub x3_2_12 x3_2_14
  let x3_3_13 := add x3_2_13 x3_2_15
  let x3_3_15 := mul w2_1 (sub x3_2_13 x3_2_15)
  let x3_4_0 := add x3_3_0 x3_3_1
  let x3_4_1 := sub x3_3_0 x3_3_1
  let x3_4_2 := add x3_3_2 x3_3_3
  let x3_4_3 := sub x3_3_2 x3_3_3
  let x3_4_4 := add x3_3_4 x3_3_5
  let x3_4_5 := sub x3_3_4 x3_3_5
  let x3_4_6 := add x3_3_6 x3_3_7
  let x3_4_7 := sub x3_3_6 x3_3_7
  let x3_4_8 := add x3_3_8 x3_3_9
  let x3_4_9 := sub x3_3_8 x3_3_9
  let x3_4_10 := add x3_3_10 x3_3_11
  let x3_4_11 := sub x3_3_10 x3_3_11
  let x3_4_12 := add x3_3_12 x3_3_13
  let x3_4_13 := sub x3_3_12 x3_3_13
  let x3_4_14 := add x3_3_14 x3_3_15
  let x3_4_15 := sub x3_3_14 x3_3_15
  let x4_0_0 := readUOffset b i4 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x4_0_1 := readUOffset b i4 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x4_0_2 := readUOffset b i4 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x4_0_3 := readUOffset b i4 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x4_0_4 := readUOffset b i4 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x4_0_5 := readUOffset b i4 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x4_0_6 := readUOffset b i4 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x4_0_7 := readUOffset b i4 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x4_0_8 := readUOffset b i4 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x4_0_9 := readUOffset b i4 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x4_0_10 := readUOffset b i4 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x4_0_11 := readUOffset b i4 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x4_0_12 := readUOffset b i4 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x4_0_13 := readUOffset b i4 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x4_0_14 := readUOffset b i4 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x4_0_15 := readUOffset b i4 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x4_1_0 := add x4_0_0 x4_0_8
  let x4_1_8 := sub x4_0_0 x4_0_8
  let x4_1_1 := add x4_0_1 x4_0_9
  let x4_1_9 := mul w0_1 (sub x4_0_1 x4_0_9)
  let x4_1_2 := add x4_0_2 x4_0_10
  let x4_1_10 := mul w0_2 (sub x4_0_2 x4_0_10)
  let x4_1_3 := add x4_0_3 x4_0_11
  let x4_1_11 := mul w0_3 (sub x4_0_3 x4_0_11)
  let x4_1_4 := add x4_0_4 x4_0_12
  let x4_1_12 := mul w0_4 (sub x4_0_4 x4_0_12)
  let x4_1_5 := add x4_0_5 x4_0_13
  let x4_1_13 := mul w0_5 (sub x4_0_5 x4_0_13)
  let x4_1_6 := add x4_0_6 x4_0_14
  let x4_1_14 := mul w0_6 (sub x4_0_6 x4_0_14)
  let x4_1_7 := add x4_0_7 x4_0_15
  let x4_1_15 := mul w0_7 (sub x4_0_7 x4_0_15)
  let x4_2_0 := add x4_1_0 x4_1_4
  let x4_2_4 := sub x4_1_0 x4_1_4
  let x4_2_1 := add x4_1_1 x4_1_5
  let x4_2_5 := mul w1_1 (sub x4_1_1 x4_1_5)
  let x4_2_2 := add x4_1_2 x4_1_6
  let x4_2_6 := mul w1_2 (sub x4_1_2 x4_1_6)
  let x4_2_3 := add x4_1_3 x4_1_7
  let x4_2_7 := mul w1_3 (sub x4_1_3 x4_1_7)
  let x4_2_8 := add x4_1_8 x4_1_12
  let x4_2_12 := sub x4_1_8 x4_1_12
  let x4_2_9 := add x4_1_9 x4_1_13
  let x4_2_13 := mul w1_1 (sub x4_1_9 x4_1_13)
  let x4_2_10 := add x4_1_10 x4_1_14
  let x4_2_14 := mul w1_2 (sub x4_1_10 x4_1_14)
  let x4_2_11 := add x4_1_11 x4_1_15
  let x4_2_15 := mul w1_3 (sub x4_1_11 x4_1_15)
  let x4_3_0 := add x4_2_0 x4_2_2
  let x4_3_2 := sub x4_2_0 x4_2_2
  let x4_3_1 := add x4_2_1 x4_2_3
  let x4_3_3 := mul w2_1 (sub x4_2_1 x4_2_3)
  let x4_3_4 := add x4_2_4 x4_2_6
  let x4_3_6 := sub x4_2_4 x4_2_6
  let x4_3_5 := add x4_2_5 x4_2_7
  let x4_3_7 := mul w2_1 (sub x4_2_5 x4_2_7)
  let x4_3_8 := add x4_2_8 x4_2_10
  let x4_3_10 := sub x4_2_8 x4_2_10
  let x4_3_9 := add x4_2_9 x4_2_11
  let x4_3_11 := mul w2_1 (sub x4_2_9 x4_2_11)
  let x4_3_12 := add x4_2_12 x4_2_14
  let x4_3_14 := sub x4_2_12 x4_2_14
  let x4_3_13 := add x4_2_13 x4_2_15
  let x4_3_15 := mul w2_1 (sub x4_2_13 x4_2_15)
  let x4_4_0 := add x4_3_0 x4_3_1
  let x4_4_1 := sub x4_3_0 x4_3_1
  let x4_4_2 := add x4_3_2 x4_3_3
  let x4_4_3 := sub x4_3_2 x4_3_3
  let x4_4_4 := add x4_3_4 x4_3_5
  let x4_4_5 := sub x4_3_4 x4_3_5
  let x4_4_6 := add x4_3_6 x4_3_7
  let x4_4_7 := sub x4_3_6 x4_3_7
  let x4_4_8 := add x4_3_8 x4_3_9
  let x4_4_9 := sub x4_3_8 x4_3_9
  let x4_4_10 := add x4_3_10 x4_3_11
  let x4_4_11 := sub x4_3_10 x4_3_11
  let x4_4_12 := add x4_3_12 x4_3_13
  let x4_4_13 := sub x4_3_12 x4_3_13
  let x4_4_14 := add x4_3_14 x4_3_15
  let x4_4_15 := sub x4_3_14 x4_3_15
  let x5_0_0 := readUOffset b i5 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x5_0_1 := readUOffset b i5 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x5_0_2 := readUOffset b i5 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x5_0_3 := readUOffset b i5 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x5_0_4 := readUOffset b i5 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x5_0_5 := readUOffset b i5 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x5_0_6 := readUOffset b i5 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x5_0_7 := readUOffset b i5 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x5_0_8 := readUOffset b i5 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x5_0_9 := readUOffset b i5 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x5_0_10 := readUOffset b i5 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x5_0_11 := readUOffset b i5 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x5_0_12 := readUOffset b i5 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x5_0_13 := readUOffset b i5 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x5_0_14 := readUOffset b i5 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x5_0_15 := readUOffset b i5 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x5_1_0 := add x5_0_0 x5_0_8
  let x5_1_8 := sub x5_0_0 x5_0_8
  let x5_1_1 := add x5_0_1 x5_0_9
  let x5_1_9 := mul w0_1 (sub x5_0_1 x5_0_9)
  let x5_1_2 := add x5_0_2 x5_0_10
  let x5_1_10 := mul w0_2 (sub x5_0_2 x5_0_10)
  let x5_1_3 := add x5_0_3 x5_0_11
  let x5_1_11 := mul w0_3 (sub x5_0_3 x5_0_11)
  let x5_1_4 := add x5_0_4 x5_0_12
  let x5_1_12 := mul w0_4 (sub x5_0_4 x5_0_12)
  let x5_1_5 := add x5_0_5 x5_0_13
  let x5_1_13 := mul w0_5 (sub x5_0_5 x5_0_13)
  let x5_1_6 := add x5_0_6 x5_0_14
  let x5_1_14 := mul w0_6 (sub x5_0_6 x5_0_14)
  let x5_1_7 := add x5_0_7 x5_0_15
  let x5_1_15 := mul w0_7 (sub x5_0_7 x5_0_15)
  let x5_2_0 := add x5_1_0 x5_1_4
  let x5_2_4 := sub x5_1_0 x5_1_4
  let x5_2_1 := add x5_1_1 x5_1_5
  let x5_2_5 := mul w1_1 (sub x5_1_1 x5_1_5)
  let x5_2_2 := add x5_1_2 x5_1_6
  let x5_2_6 := mul w1_2 (sub x5_1_2 x5_1_6)
  let x5_2_3 := add x5_1_3 x5_1_7
  let x5_2_7 := mul w1_3 (sub x5_1_3 x5_1_7)
  let x5_2_8 := add x5_1_8 x5_1_12
  let x5_2_12 := sub x5_1_8 x5_1_12
  let x5_2_9 := add x5_1_9 x5_1_13
  let x5_2_13 := mul w1_1 (sub x5_1_9 x5_1_13)
  let x5_2_10 := add x5_1_10 x5_1_14
  let x5_2_14 := mul w1_2 (sub x5_1_10 x5_1_14)
  let x5_2_11 := add x5_1_11 x5_1_15
  let x5_2_15 := mul w1_3 (sub x5_1_11 x5_1_15)
  let x5_3_0 := add x5_2_0 x5_2_2
  let x5_3_2 := sub x5_2_0 x5_2_2
  let x5_3_1 := add x5_2_1 x5_2_3
  let x5_3_3 := mul w2_1 (sub x5_2_1 x5_2_3)
  let x5_3_4 := add x5_2_4 x5_2_6
  let x5_3_6 := sub x5_2_4 x5_2_6
  let x5_3_5 := add x5_2_5 x5_2_7
  let x5_3_7 := mul w2_1 (sub x5_2_5 x5_2_7)
  let x5_3_8 := add x5_2_8 x5_2_10
  let x5_3_10 := sub x5_2_8 x5_2_10
  let x5_3_9 := add x5_2_9 x5_2_11
  let x5_3_11 := mul w2_1 (sub x5_2_9 x5_2_11)
  let x5_3_12 := add x5_2_12 x5_2_14
  let x5_3_14 := sub x5_2_12 x5_2_14
  let x5_3_13 := add x5_2_13 x5_2_15
  let x5_3_15 := mul w2_1 (sub x5_2_13 x5_2_15)
  let x5_4_0 := add x5_3_0 x5_3_1
  let x5_4_1 := sub x5_3_0 x5_3_1
  let x5_4_2 := add x5_3_2 x5_3_3
  let x5_4_3 := sub x5_3_2 x5_3_3
  let x5_4_4 := add x5_3_4 x5_3_5
  let x5_4_5 := sub x5_3_4 x5_3_5
  let x5_4_6 := add x5_3_6 x5_3_7
  let x5_4_7 := sub x5_3_6 x5_3_7
  let x5_4_8 := add x5_3_8 x5_3_9
  let x5_4_9 := sub x5_3_8 x5_3_9
  let x5_4_10 := add x5_3_10 x5_3_11
  let x5_4_11 := sub x5_3_10 x5_3_11
  let x5_4_12 := add x5_3_12 x5_3_13
  let x5_4_13 := sub x5_3_12 x5_3_13
  let x5_4_14 := add x5_3_14 x5_3_15
  let x5_4_15 := sub x5_3_14 x5_3_15
  let x6_0_0 := readUOffset b i6 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x6_0_1 := readUOffset b i6 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x6_0_2 := readUOffset b i6 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x6_0_3 := readUOffset b i6 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x6_0_4 := readUOffset b i6 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x6_0_5 := readUOffset b i6 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x6_0_6 := readUOffset b i6 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x6_0_7 := readUOffset b i6 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x6_0_8 := readUOffset b i6 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x6_0_9 := readUOffset b i6 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x6_0_10 := readUOffset b i6 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x6_0_11 := readUOffset b i6 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x6_0_12 := readUOffset b i6 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x6_0_13 := readUOffset b i6 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x6_0_14 := readUOffset b i6 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x6_0_15 := readUOffset b i6 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x6_1_0 := add x6_0_0 x6_0_8
  let x6_1_8 := sub x6_0_0 x6_0_8
  let x6_1_1 := add x6_0_1 x6_0_9
  let x6_1_9 := mul w0_1 (sub x6_0_1 x6_0_9)
  let x6_1_2 := add x6_0_2 x6_0_10
  let x6_1_10 := mul w0_2 (sub x6_0_2 x6_0_10)
  let x6_1_3 := add x6_0_3 x6_0_11
  let x6_1_11 := mul w0_3 (sub x6_0_3 x6_0_11)
  let x6_1_4 := add x6_0_4 x6_0_12
  let x6_1_12 := mul w0_4 (sub x6_0_4 x6_0_12)
  let x6_1_5 := add x6_0_5 x6_0_13
  let x6_1_13 := mul w0_5 (sub x6_0_5 x6_0_13)
  let x6_1_6 := add x6_0_6 x6_0_14
  let x6_1_14 := mul w0_6 (sub x6_0_6 x6_0_14)
  let x6_1_7 := add x6_0_7 x6_0_15
  let x6_1_15 := mul w0_7 (sub x6_0_7 x6_0_15)
  let x6_2_0 := add x6_1_0 x6_1_4
  let x6_2_4 := sub x6_1_0 x6_1_4
  let x6_2_1 := add x6_1_1 x6_1_5
  let x6_2_5 := mul w1_1 (sub x6_1_1 x6_1_5)
  let x6_2_2 := add x6_1_2 x6_1_6
  let x6_2_6 := mul w1_2 (sub x6_1_2 x6_1_6)
  let x6_2_3 := add x6_1_3 x6_1_7
  let x6_2_7 := mul w1_3 (sub x6_1_3 x6_1_7)
  let x6_2_8 := add x6_1_8 x6_1_12
  let x6_2_12 := sub x6_1_8 x6_1_12
  let x6_2_9 := add x6_1_9 x6_1_13
  let x6_2_13 := mul w1_1 (sub x6_1_9 x6_1_13)
  let x6_2_10 := add x6_1_10 x6_1_14
  let x6_2_14 := mul w1_2 (sub x6_1_10 x6_1_14)
  let x6_2_11 := add x6_1_11 x6_1_15
  let x6_2_15 := mul w1_3 (sub x6_1_11 x6_1_15)
  let x6_3_0 := add x6_2_0 x6_2_2
  let x6_3_2 := sub x6_2_0 x6_2_2
  let x6_3_1 := add x6_2_1 x6_2_3
  let x6_3_3 := mul w2_1 (sub x6_2_1 x6_2_3)
  let x6_3_4 := add x6_2_4 x6_2_6
  let x6_3_6 := sub x6_2_4 x6_2_6
  let x6_3_5 := add x6_2_5 x6_2_7
  let x6_3_7 := mul w2_1 (sub x6_2_5 x6_2_7)
  let x6_3_8 := add x6_2_8 x6_2_10
  let x6_3_10 := sub x6_2_8 x6_2_10
  let x6_3_9 := add x6_2_9 x6_2_11
  let x6_3_11 := mul w2_1 (sub x6_2_9 x6_2_11)
  let x6_3_12 := add x6_2_12 x6_2_14
  let x6_3_14 := sub x6_2_12 x6_2_14
  let x6_3_13 := add x6_2_13 x6_2_15
  let x6_3_15 := mul w2_1 (sub x6_2_13 x6_2_15)
  let x6_4_0 := add x6_3_0 x6_3_1
  let x6_4_1 := sub x6_3_0 x6_3_1
  let x6_4_2 := add x6_3_2 x6_3_3
  let x6_4_3 := sub x6_3_2 x6_3_3
  let x6_4_4 := add x6_3_4 x6_3_5
  let x6_4_5 := sub x6_3_4 x6_3_5
  let x6_4_6 := add x6_3_6 x6_3_7
  let x6_4_7 := sub x6_3_6 x6_3_7
  let x6_4_8 := add x6_3_8 x6_3_9
  let x6_4_9 := sub x6_3_8 x6_3_9
  let x6_4_10 := add x6_3_10 x6_3_11
  let x6_4_11 := sub x6_3_10 x6_3_11
  let x6_4_12 := add x6_3_12 x6_3_13
  let x6_4_13 := sub x6_3_12 x6_3_13
  let x6_4_14 := add x6_3_14 x6_3_15
  let x6_4_15 := sub x6_3_14 x6_3_15
  let x7_0_0 := readUOffset b i7 0 (by rw [usize_numeral 0 (by decide)]; omega)
  let x7_0_1 := readUOffset b i7 1 (by rw [usize_numeral 1 (by decide)]; omega)
  let x7_0_2 := readUOffset b i7 2 (by rw [usize_numeral 2 (by decide)]; omega)
  let x7_0_3 := readUOffset b i7 3 (by rw [usize_numeral 3 (by decide)]; omega)
  let x7_0_4 := readUOffset b i7 4 (by rw [usize_numeral 4 (by decide)]; omega)
  let x7_0_5 := readUOffset b i7 5 (by rw [usize_numeral 5 (by decide)]; omega)
  let x7_0_6 := readUOffset b i7 6 (by rw [usize_numeral 6 (by decide)]; omega)
  let x7_0_7 := readUOffset b i7 7 (by rw [usize_numeral 7 (by decide)]; omega)
  let x7_0_8 := readUOffset b i7 8 (by rw [usize_numeral 8 (by decide)]; omega)
  let x7_0_9 := readUOffset b i7 9 (by rw [usize_numeral 9 (by decide)]; omega)
  let x7_0_10 := readUOffset b i7 10 (by rw [usize_numeral 10 (by decide)]; omega)
  let x7_0_11 := readUOffset b i7 11 (by rw [usize_numeral 11 (by decide)]; omega)
  let x7_0_12 := readUOffset b i7 12 (by rw [usize_numeral 12 (by decide)]; omega)
  let x7_0_13 := readUOffset b i7 13 (by rw [usize_numeral 13 (by decide)]; omega)
  let x7_0_14 := readUOffset b i7 14 (by rw [usize_numeral 14 (by decide)]; omega)
  let x7_0_15 := readUOffset b i7 15 (by rw [usize_numeral 15 (by decide)]; omega)
  let x7_1_0 := add x7_0_0 x7_0_8
  let x7_1_8 := sub x7_0_0 x7_0_8
  let x7_1_1 := add x7_0_1 x7_0_9
  let x7_1_9 := mul w0_1 (sub x7_0_1 x7_0_9)
  let x7_1_2 := add x7_0_2 x7_0_10
  let x7_1_10 := mul w0_2 (sub x7_0_2 x7_0_10)
  let x7_1_3 := add x7_0_3 x7_0_11
  let x7_1_11 := mul w0_3 (sub x7_0_3 x7_0_11)
  let x7_1_4 := add x7_0_4 x7_0_12
  let x7_1_12 := mul w0_4 (sub x7_0_4 x7_0_12)
  let x7_1_5 := add x7_0_5 x7_0_13
  let x7_1_13 := mul w0_5 (sub x7_0_5 x7_0_13)
  let x7_1_6 := add x7_0_6 x7_0_14
  let x7_1_14 := mul w0_6 (sub x7_0_6 x7_0_14)
  let x7_1_7 := add x7_0_7 x7_0_15
  let x7_1_15 := mul w0_7 (sub x7_0_7 x7_0_15)
  let x7_2_0 := add x7_1_0 x7_1_4
  let x7_2_4 := sub x7_1_0 x7_1_4
  let x7_2_1 := add x7_1_1 x7_1_5
  let x7_2_5 := mul w1_1 (sub x7_1_1 x7_1_5)
  let x7_2_2 := add x7_1_2 x7_1_6
  let x7_2_6 := mul w1_2 (sub x7_1_2 x7_1_6)
  let x7_2_3 := add x7_1_3 x7_1_7
  let x7_2_7 := mul w1_3 (sub x7_1_3 x7_1_7)
  let x7_2_8 := add x7_1_8 x7_1_12
  let x7_2_12 := sub x7_1_8 x7_1_12
  let x7_2_9 := add x7_1_9 x7_1_13
  let x7_2_13 := mul w1_1 (sub x7_1_9 x7_1_13)
  let x7_2_10 := add x7_1_10 x7_1_14
  let x7_2_14 := mul w1_2 (sub x7_1_10 x7_1_14)
  let x7_2_11 := add x7_1_11 x7_1_15
  let x7_2_15 := mul w1_3 (sub x7_1_11 x7_1_15)
  let x7_3_0 := add x7_2_0 x7_2_2
  let x7_3_2 := sub x7_2_0 x7_2_2
  let x7_3_1 := add x7_2_1 x7_2_3
  let x7_3_3 := mul w2_1 (sub x7_2_1 x7_2_3)
  let x7_3_4 := add x7_2_4 x7_2_6
  let x7_3_6 := sub x7_2_4 x7_2_6
  let x7_3_5 := add x7_2_5 x7_2_7
  let x7_3_7 := mul w2_1 (sub x7_2_5 x7_2_7)
  let x7_3_8 := add x7_2_8 x7_2_10
  let x7_3_10 := sub x7_2_8 x7_2_10
  let x7_3_9 := add x7_2_9 x7_2_11
  let x7_3_11 := mul w2_1 (sub x7_2_9 x7_2_11)
  let x7_3_12 := add x7_2_12 x7_2_14
  let x7_3_14 := sub x7_2_12 x7_2_14
  let x7_3_13 := add x7_2_13 x7_2_15
  let x7_3_15 := mul w2_1 (sub x7_2_13 x7_2_15)
  let x7_4_0 := add x7_3_0 x7_3_1
  let x7_4_1 := sub x7_3_0 x7_3_1
  let x7_4_2 := add x7_3_2 x7_3_3
  let x7_4_3 := sub x7_3_2 x7_3_3
  let x7_4_4 := add x7_3_4 x7_3_5
  let x7_4_5 := sub x7_3_4 x7_3_5
  let x7_4_6 := add x7_3_6 x7_3_7
  let x7_4_7 := sub x7_3_6 x7_3_7
  let x7_4_8 := add x7_3_8 x7_3_9
  let x7_4_9 := sub x7_3_8 x7_3_9
  let x7_4_10 := add x7_3_10 x7_3_11
  let x7_4_11 := sub x7_3_10 x7_3_11
  let x7_4_12 := add x7_3_12 x7_3_13
  let x7_4_13 := sub x7_3_12 x7_3_13
  let x7_4_14 := add x7_3_14 x7_3_15
  let x7_4_15 := sub x7_3_14 x7_3_15
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 0).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_0) (scaleWord factor scale x1_4_0) (scaleWord factor scale x2_4_0)
    (scaleWord factor scale x3_4_0) (scaleWord factor scale x4_4_0) (scaleWord factor scale x5_4_0)
    (scaleWord factor scale x6_4_0) (scaleWord factor scale x7_4_0)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 1).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_1) (scaleWord factor scale x1_4_1) (scaleWord factor scale x2_4_1)
    (scaleWord factor scale x3_4_1) (scaleWord factor scale x4_4_1) (scaleWord factor scale x5_4_1)
    (scaleWord factor scale x6_4_1) (scaleWord factor scale x7_4_1)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 2).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_2) (scaleWord factor scale x1_4_2) (scaleWord factor scale x2_4_2)
    (scaleWord factor scale x3_4_2) (scaleWord factor scale x4_4_2) (scaleWord factor scale x5_4_2)
    (scaleWord factor scale x6_4_2) (scaleWord factor scale x7_4_2)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 3).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_3) (scaleWord factor scale x1_4_3) (scaleWord factor scale x2_4_3)
    (scaleWord factor scale x3_4_3) (scaleWord factor scale x4_4_3) (scaleWord factor scale x5_4_3)
    (scaleWord factor scale x6_4_3) (scaleWord factor scale x7_4_3)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 4).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_4) (scaleWord factor scale x1_4_4) (scaleWord factor scale x2_4_4)
    (scaleWord factor scale x3_4_4) (scaleWord factor scale x4_4_4) (scaleWord factor scale x5_4_4)
    (scaleWord factor scale x6_4_4) (scaleWord factor scale x7_4_4)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 5).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_5) (scaleWord factor scale x1_4_5) (scaleWord factor scale x2_4_5)
    (scaleWord factor scale x3_4_5) (scaleWord factor scale x4_4_5) (scaleWord factor scale x5_4_5)
    (scaleWord factor scale x6_4_5) (scaleWord factor scale x7_4_5)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 6).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_6) (scaleWord factor scale x1_4_6) (scaleWord factor scale x2_4_6)
    (scaleWord factor scale x3_4_6) (scaleWord factor scale x4_4_6) (scaleWord factor scale x5_4_6)
    (scaleWord factor scale x6_4_6) (scaleWord factor scale x7_4_6)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 7).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_7) (scaleWord factor scale x1_4_7) (scaleWord factor scale x2_4_7)
    (scaleWord factor scale x3_4_7) (scaleWord factor scale x4_4_7) (scaleWord factor scale x5_4_7)
    (scaleWord factor scale x6_4_7) (scaleWord factor scale x7_4_7)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 8).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_8) (scaleWord factor scale x1_4_8) (scaleWord factor scale x2_4_8)
    (scaleWord factor scale x3_4_8) (scaleWord factor scale x4_4_8) (scaleWord factor scale x5_4_8)
    (scaleWord factor scale x6_4_8) (scaleWord factor scale x7_4_8)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 9).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_9) (scaleWord factor scale x1_4_9) (scaleWord factor scale x2_4_9)
    (scaleWord factor scale x3_4_9) (scaleWord factor scale x4_4_9) (scaleWord factor scale x5_4_9)
    (scaleWord factor scale x6_4_9) (scaleWord factor scale x7_4_9)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 10).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_10) (scaleWord factor scale x1_4_10)
    (scaleWord factor scale x2_4_10) (scaleWord factor scale x3_4_10)
    (scaleWord factor scale x4_4_10) (scaleWord factor scale x5_4_10)
    (scaleWord factor scale x6_4_10) (scaleWord factor scale x7_4_10)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 11).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_11) (scaleWord factor scale x1_4_11)
    (scaleWord factor scale x2_4_11) (scaleWord factor scale x3_4_11)
    (scaleWord factor scale x4_4_11) (scaleWord factor scale x5_4_11)
    (scaleWord factor scale x6_4_11) (scaleWord factor scale x7_4_11)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 12).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_12) (scaleWord factor scale x1_4_12)
    (scaleWord factor scale x2_4_12) (scaleWord factor scale x3_4_12)
    (scaleWord factor scale x4_4_12) (scaleWord factor scale x5_4_12)
    (scaleWord factor scale x6_4_12) (scaleWord factor scale x7_4_12)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 13).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_13) (scaleWord factor scale x1_4_13)
    (scaleWord factor scale x2_4_13) (scaleWord factor scale x3_4_13)
    (scaleWord factor scale x4_4_13) (scaleWord factor scale x5_4_13)
    (scaleWord factor scale x6_4_13) (scaleWord factor scale x7_4_13)
    0 0 0 0 0 0 0 0
  let out := storeWords out
    (4 * (16 * (reverse32 (16 * c + 14).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_14) (scaleWord factor scale x1_4_14)
    (scaleWord factor scale x2_4_14) (scaleWord factor scale x3_4_14)
    (scaleWord factor scale x4_4_14) (scaleWord factor scale x5_4_14)
    (scaleWord factor scale x6_4_14) (scaleWord factor scale x7_4_14)
    0 0 0 0 0 0 0 0
  storeWords out
    (4 * (16 * (reverse32 (16 * c + 15).toUInt32 >>> shift).toUSize + 8 * half)) 8
    (scaleWord factor scale x0_4_15) (scaleWord factor scale x1_4_15)
    (scaleWord factor scale x2_4_15) (scaleWord factor scale x3_4_15)
    (scaleWord factor scale x4_4_15) (scaleWord factor scale x5_4_15)
    (scaleWord factor scale x6_4_15) (scaleWord factor scale x7_4_15)
    0 0 0 0 0 0 0 0

/-- Block `v`'s word index at batch `c` stays in range. -/
theorem laneBound (v : USize) (hv : v.toNat < 16) (Lw c : USize) (b : ByteArray)
    (hL : 64 * Lw.toNat ≤ b.size) (hb : b.size < USize.size)
    (hc : 16 * c.toNat + 16 ≤ Lw.toNat) : 4 * ((v * Lw + 16 * c).toNat + 15) + 3 < b.size := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hvL : v.toNat * Lw.toNat ≤ 15 * Lw.toNat := Nat.mul_le_mul_right _ (by omega)
  simp only [USize.toNat_add, USize.toNat_mul, USize.reduceToNat, hsize]
  rw [Nat.mod_eq_of_lt (show v.toNat * Lw.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show 16 * c.toNat < USize.size by omega),
    Nat.mod_eq_of_lt (show v.toNat * Lw.toNat + 16 * c.toNat < USize.size by omega)]
  omega

/-- Batches `c, …, c + n - 1` of sixteen block columns, both halves each. -/
def lastRevGo (t3 t2 t1 b : @& ByteArray) (Lw : USize) (shift factor : UInt32) (scale : Bool)
    (hb : 64 * Lw.toNat ≤ b.size ∧ b.size < USize.size ∧ 31 < t3.size ∧ t3.size < USize.size ∧
      15 < t2.size ∧ t2.size < USize.size ∧ 7 < t1.size ∧ t1.size < USize.size) :
    Nat → USize → ByteArray → ByteArray
  | 0, _, out => out
  | n + 1, c, out =>
    if hc : 16 * c.toNat + 16 ≤ Lw.toNat then
      let out := lastHalf t3 t2 t1 b (0 * Lw + 16 * c) (8 * Lw + 16 * c) (4 * Lw + 16 * c)
          (12 * Lw + 16 * c)
        (2 * Lw + 16 * c) (10 * Lw + 16 * c) (6 * Lw + 16 * c) (14 * Lw + 16 * c)
        c shift 0 factor scale out
        ⟨laneBound 0 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 8 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 4 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 12 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 2 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 10 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 6 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 14 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          hb.2.1, hb.2.2⟩
      let out := lastHalf t3 t2 t1 b (1 * Lw + 16 * c) (9 * Lw + 16 * c) (5 * Lw + 16 * c)
          (13 * Lw + 16 * c)
        (3 * Lw + 16 * c) (11 * Lw + 16 * c) (7 * Lw + 16 * c) (15 * Lw + 16 * c)
        c shift 1 factor scale out
        ⟨laneBound 1 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 9 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 5 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 13 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 3 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 11 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 7 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          laneBound 15 (by simp only [USize.reduceToNat]; omega) Lw c b hb.1 hb.2.1 hc,
          hb.2.1, hb.2.2⟩
      lastRevGo t3 t2 t1 b Lw shift factor scale hb n (c + 1) out
    else out

/-- The last four DIF layers of a `2 ^ m`-word leaf whose earlier layers are done, in natural
order, optionally scaled. The output starts as a copy of the input, which the first store makes
because the input stays borrowed; every word is then overwritten. -/
def lastRev (t3 t2 t1 b : @& ByteArray) (m : Nat) (factor : UInt32) (scale : Bool) :
    ByteArray :=
  if h : 2 ^ (m - 4) < USize.size ∧ 64 * 2 ^ (m - 4) ≤ b.size ∧ b.size < USize.size ∧
      31 < t3.size ∧ t3.size < USize.size ∧ 15 < t2.size ∧ t2.size < USize.size ∧
      7 < t1.size ∧ t1.size < USize.size then
    lastRevGo t3 t2 t1 b (USize.ofNatLT (2 ^ (m - 4)) h.1) (32 - (m - 4)).toUInt32 factor scale
      (by simpa only [USize.toNat_ofNatLT] using h.2) (2 ^ (m - 4) / 16) 0 b
  else b

/-- The radix-four passes of `stages` before its fused final layers. -/
def upperStages (logN : Nat) (tw : Array ByteArray) (a : ByteArray) : ByteArray := Id.run do
  let mut a := a
  for pass in [:logN / 2 - 2] do
    let high := logN - 1 - 2 * pass
    let low := high - 1
    let q := 2 ^ low
    for block in [:2 ^ logN / (4 * q)] do
      let base := block * (4 * q)
      a := inner16 (tw.getD high ByteArray.empty) (tw.getD low ByteArray.empty)
        q 0 base (base + q) (base + 2 * q) (base + 3 * q) a
  return a

/-- A complete `2 ^ m`-word leaf in natural order, optionally scaled: even leaves of at least
`2 ^ 8` words use the fused final layers, others `stages` and `leafRev`, and leaves of fewer than
sixteen words a scalar reversal. -/
def leafNatural (tw : Array ByteArray) (m : Nat) (factor : UInt32) (scale : Bool)
    (a : ByteArray) : ByteArray :=
  if m % 2 = 0 ∧ 8 ≤ m then
    lastRev (tw.getD 3 .empty) (tw.getD 2 .empty) (tw.getD 1 .empty) (upperStages m tw a) m
      factor scale
  else if 4 ≤ m then leafRev (stages m tw a) m factor scale
  else encodeFields (decode m (stages m tw a) factor scale)

end CompPoly.CPolynomial.NTTFast.Packed.Native
