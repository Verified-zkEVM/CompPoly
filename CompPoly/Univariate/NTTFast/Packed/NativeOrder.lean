/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Native
import CompPoly.Univariate.NTTFast.Packed.Unrolled

/-! # Parallel natural-order output for the packed FFT

The sixteen task leaves of the packed FFT hold a bit-reversed transform. Each leaf is
first reversed locally, in parallel. Natural order is then a sixteen-way interleave of
the reversed leaves, which parallel tasks compute as cache-line `16 × 16` transposes.
The task outputs are packed buffers, so joining them is a byte copy.
-/

@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed.Native
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

/-- Apply the optional inverse normalization to one Montgomery word. -/
@[inline]
def scaleWord (p : ℕ) [Mont32Field p] (factor : UInt32) (scale : Bool) (x : UInt32) : UInt32 :=
  if scale then mul p factor x else x

/-- Sixteen consecutive words of one buffer. -/
structure Line where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  w8 : UInt32
  w9 : UInt32
  w10 : UInt32
  w11 : UInt32
  w12 : UInt32
  w13 : UInt32
  w14 : UInt32
  w15 : UInt32

/-- Words `q, …, q + 15` fit in `b`, checked on machine words. -/
abbrev LineFits (b : ByteArray) (q : USize) : Prop := 16 ≤ b.usize / 4 ∧ q ≤ b.usize / 4 - 16

theorem lineFits_toNat {b : ByteArray} {q : USize} (h : LineFits b q) (k : Nat) (hk : k < 16) :
    ((q + OfNat.ofNat k) * 4).toNat = 4 * (q.toNat + k) ∧ 4 * (q.toNat + k) + 4 ≤ b.size := by
  have hsize : (2 : Nat) ^ System.Platform.numBits = USize.size := rfl
  have hb := toNat_usize_le b
  have hu := b.usize.toNat_lt_size
  have h16 : (16 : USize).toNat = 16 := usize_numeral 16 (by decide)
  have h4 : (4 : USize).toNat = 4 := usize_numeral 4 (by decide)
  obtain ⟨h1, h2⟩ := h
  rw [USize.le_iff_toNat_le, USize.toNat_div, h4, h16] at h1
  rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ (by
    rw [USize.le_iff_toNat_le, USize.toNat_div, h4, h16]; exact h1), USize.toNat_div, h4, h16]
    at h2
  have hk' : (OfNat.ofNat k : USize).toNat = k := usize_numeral k (by omega)
  have hadd : (q + OfNat.ofNat k).toNat = q.toNat + k := by
    rw [USize.toNat_add, hk', hsize, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, by omega⟩
  rw [USize.toNat_mul, hadd, h4, hsize, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Read one aligned line of sixteen words, whose range was checked; inlining removes the
record. -/
@[inline] def line (b : @& ByteArray) (q : USize) (h : LineFits b q) : Line :=
  line_words%

/-- Append the transpose of one `16 × 16` tile: word `u` of every stream, for each `u`.
Reading whole lines first keeps sixteen equally aligned streams from evicting each other. -/
@[noinline] def transposeStep (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 :
    @& ByteArray) (q : USize) (out : ByteArray) (p : USize) : ByteArray :=
  transposeStep_words%

/-- Store `count` transposed tiles, starting at stream word `q` and output word `p`, the end of
`out`. Each tile first extends `out` by one zero block, which the tile then overwrites while it
is in cache. -/
def transposeGo (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : @& ByteArray) :
    Nat → USize → USize → ByteArray → ByteArray
  | 0, _, _, out => out
  | count + 1, q, p, out =>
    let n := out.size
    let out := ByteArray.zeroBlock.copySlice 0 out n 1024 false
    transposeGo s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 count (q + 16) (p + 256)
      (transposeStep s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 q out p)

/-- Natural-order words `16 * q` up to `16 * (q + 16 * count)` from reversed leaves `r`.
Output word `16 * j + c` is word `j` of leaf `bitrev₄ c`. -/
def interleaveRange (r : @& Array ByteArray) (q count : Nat) : ByteArray :=
  transposeGo (r.getD 0 .empty) (r.getD 8 .empty) (r.getD 4 .empty) (r.getD 12 .empty)
    (r.getD 2 .empty) (r.getD 10 .empty) (r.getD 6 .empty) (r.getD 14 .empty)
    (r.getD 1 .empty) (r.getD 9 .empty) (r.getD 5 .empty) (r.getD 13 .empty)
    (r.getD 3 .empty) (r.getD 11 .empty) (r.getD 7 .empty) (r.getD 15 .empty)
    count q.toUSize 0 (ByteArray.emptyWithCapacity (1024 * count))

/-- Natural-order packed words from sixteen locally reversed leaves of `2 ^ (logN - 4)` words,
`12 ≤ logN`. Sixteen interleave tasks run in parallel; the join copies bytes. -/
def naturalLeaves (r : Array ByteArray) (logN : Nat) : ByteArray :=
  let count := 2 ^ (logN - 4) / 256
  let blocks := (Array.range 16).map fun t ↦ Task.spawn fun _ ↦
    interleaveRange r (16 * count * t) count
  blocks.foldl (fun acc t ↦ acc ++ t.get) (ByteArray.emptyWithCapacity (4 * 2 ^ logN))

end CompPoly.CPolynomial.NTTFast.Packed.Native
