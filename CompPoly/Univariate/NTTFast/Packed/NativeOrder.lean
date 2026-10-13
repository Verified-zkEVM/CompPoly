/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Univariate.NTTFast.Packed.Native

/-! # Parallel natural-order output for the packed FFT

The sixteen task leaves of the packed FFT hold a bit-reversed transform. Each leaf is
first reversed locally, in parallel. Natural order is then a sixteen-way interleave of
the reversed leaves, which parallel tasks compute as cache-line `16 × 16` transposes.
The task outputs are packed buffers, so joining them is a byte copy.
-/

@[expose] public section
open CompPoly
namespace CompPoly.CPolynomial.NTTFast.Packed.Native

/-- Apply the optional inverse normalization to one Montgomery word. -/
@[inline] def scaleWord (factor : UInt32) (scale : Bool) (x : UInt32) : UInt32 :=
  if scale then mul factor x else x

/-- Word offset `k * st`. -/
@[inline] def strideOff (k : Nat) (st : USize) : USize := k.toUSize * st

/-- Store sixteen consecutive locally reversed words at local index `q`, a multiple of sixteen:
their positions are `bitrev q + bitrev₄ u * st` with one reversal per batch. -/
@[noinline] def leafRevStep (b : @& ByteArray) (shift factor : UInt32) (scale : Bool)
    (st q : USize) (out : ByteArray) : ByteArray :=
  let r := (reverse32 q.toUInt32 >>> shift).toUSize
  write16U out q (scaleWord factor scale (readWord b (r + strideOff 0 st)))
    (scaleWord factor scale (readWord b (r + strideOff 8 st)))
    (scaleWord factor scale (readWord b (r + strideOff 4 st)))
    (scaleWord factor scale (readWord b (r + strideOff 12 st)))
    (scaleWord factor scale (readWord b (r + strideOff 2 st)))
    (scaleWord factor scale (readWord b (r + strideOff 10 st)))
    (scaleWord factor scale (readWord b (r + strideOff 6 st)))
    (scaleWord factor scale (readWord b (r + strideOff 14 st)))
    (scaleWord factor scale (readWord b (r + strideOff 1 st)))
    (scaleWord factor scale (readWord b (r + strideOff 9 st)))
    (scaleWord factor scale (readWord b (r + strideOff 5 st)))
    (scaleWord factor scale (readWord b (r + strideOff 13 st)))
    (scaleWord factor scale (readWord b (r + strideOff 3 st)))
    (scaleWord factor scale (readWord b (r + strideOff 11 st)))
    (scaleWord factor scale (readWord b (r + strideOff 7 st)))
    (scaleWord factor scale (readWord b (r + strideOff 15 st)))

/-- Store `count` batches of sixteen locally reversed words, starting at local index `q`. -/
def leafRevGo (b : @& ByteArray) (shift factor : UInt32) (scale : Bool) (st : USize) :
    Nat → USize → ByteArray → ByteArray
  | 0, _, out => out
  | count + 1, q, out =>
    leafRevGo b shift factor scale st count (q + 16) (leafRevStep b shift factor scale st q out)

/-- A `2 ^ logM`-word leaf in locally bit-reversed order, optionally scaled, `4 ≤ logM`. -/
def leafRev (b : @& ByteArray) (logM : Nat) (factor : UInt32) (scale : Bool) : ByteArray :=
  leafRevGo b (32 - logM).toUInt32 factor scale (2 ^ (logM - 4)).toUSize (2 ^ logM / 16) 0
    (zeroWords (2 ^ logM))

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
  ⟨b.ugetUInt32LE ((q + 0) * 4)
      (by rw [(lineFits_toNat h 0 (by decide)).1]
          exact (lineFits_toNat h 0 (by decide)).2),
    b.ugetUInt32LE ((q + 1) * 4)
      (by rw [(lineFits_toNat h 1 (by decide)).1]
          exact (lineFits_toNat h 1 (by decide)).2),
    b.ugetUInt32LE ((q + 2) * 4)
      (by rw [(lineFits_toNat h 2 (by decide)).1]
          exact (lineFits_toNat h 2 (by decide)).2),
    b.ugetUInt32LE ((q + 3) * 4)
      (by rw [(lineFits_toNat h 3 (by decide)).1]
          exact (lineFits_toNat h 3 (by decide)).2),
    b.ugetUInt32LE ((q + 4) * 4)
      (by rw [(lineFits_toNat h 4 (by decide)).1]
          exact (lineFits_toNat h 4 (by decide)).2),
    b.ugetUInt32LE ((q + 5) * 4)
      (by rw [(lineFits_toNat h 5 (by decide)).1]
          exact (lineFits_toNat h 5 (by decide)).2),
    b.ugetUInt32LE ((q + 6) * 4)
      (by rw [(lineFits_toNat h 6 (by decide)).1]
          exact (lineFits_toNat h 6 (by decide)).2),
    b.ugetUInt32LE ((q + 7) * 4)
      (by rw [(lineFits_toNat h 7 (by decide)).1]
          exact (lineFits_toNat h 7 (by decide)).2),
    b.ugetUInt32LE ((q + 8) * 4)
      (by rw [(lineFits_toNat h 8 (by decide)).1]
          exact (lineFits_toNat h 8 (by decide)).2),
    b.ugetUInt32LE ((q + 9) * 4)
      (by rw [(lineFits_toNat h 9 (by decide)).1]
          exact (lineFits_toNat h 9 (by decide)).2),
    b.ugetUInt32LE ((q + 10) * 4)
      (by rw [(lineFits_toNat h 10 (by decide)).1]
          exact (lineFits_toNat h 10 (by decide)).2),
    b.ugetUInt32LE ((q + 11) * 4)
      (by rw [(lineFits_toNat h 11 (by decide)).1]
          exact (lineFits_toNat h 11 (by decide)).2),
    b.ugetUInt32LE ((q + 12) * 4)
      (by rw [(lineFits_toNat h 12 (by decide)).1]
          exact (lineFits_toNat h 12 (by decide)).2),
    b.ugetUInt32LE ((q + 13) * 4)
      (by rw [(lineFits_toNat h 13 (by decide)).1]
          exact (lineFits_toNat h 13 (by decide)).2),
    b.ugetUInt32LE ((q + 14) * 4)
      (by rw [(lineFits_toNat h 14 (by decide)).1]
          exact (lineFits_toNat h 14 (by decide)).2),
    b.ugetUInt32LE ((q + 15) * 4)
      (by rw [(lineFits_toNat h 15 (by decide)).1]
          exact (lineFits_toNat h 15 (by decide)).2)⟩

/-- Append the transpose of one `16 × 16` tile: word `u` of every stream, for each `u`.
Reading whole lines first keeps sixteen equally aligned streams from evicting each other. -/
@[noinline] def transposeStep (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 :
    @& ByteArray) (q : USize) (out : ByteArray) (p : USize) : ByteArray :=
  if h : LineFits s0 q ∧ LineFits s1 q ∧ LineFits s2 q ∧ LineFits s3 q ∧ LineFits s4 q ∧
      LineFits s5 q ∧ LineFits s6 q ∧ LineFits s7 q ∧ LineFits s8 q ∧ LineFits s9 q ∧
      LineFits s10 q ∧ LineFits s11 q ∧ LineFits s12 q ∧ LineFits s13 q ∧ LineFits s14 q ∧
      LineFits s15 q then
  let x0 := line s0 q h.1
  let x1 := line s1 q h.2.1
  let x2 := line s2 q h.2.2.1
  let x3 := line s3 q h.2.2.2.1
  let x4 := line s4 q h.2.2.2.2.1
  let x5 := line s5 q h.2.2.2.2.2.1
  let x6 := line s6 q h.2.2.2.2.2.2.1
  let x7 := line s7 q h.2.2.2.2.2.2.2.1
  let x8 := line s8 q h.2.2.2.2.2.2.2.2.1
  let x9 := line s9 q h.2.2.2.2.2.2.2.2.2.1
  let x10 := line s10 q h.2.2.2.2.2.2.2.2.2.2.1
  let x11 := line s11 q h.2.2.2.2.2.2.2.2.2.2.2.1
  let x12 := line s12 q h.2.2.2.2.2.2.2.2.2.2.2.2.1
  let x13 := line s13 q h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let x14 := line s14 q h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let x15 := line s15 q h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  let out := write16U out p x0.w0 x1.w0 x2.w0 x3.w0 x4.w0 x5.w0 x6.w0 x7.w0 x8.w0
    x9.w0 x10.w0 x11.w0 x12.w0 x13.w0 x14.w0 x15.w0
  let out := write16U out (p + 16) x0.w1 x1.w1 x2.w1 x3.w1 x4.w1 x5.w1 x6.w1 x7.w1 x8.w1
    x9.w1 x10.w1 x11.w1 x12.w1 x13.w1 x14.w1 x15.w1
  let out := write16U out (p + 32) x0.w2 x1.w2 x2.w2 x3.w2 x4.w2 x5.w2 x6.w2 x7.w2 x8.w2
    x9.w2 x10.w2 x11.w2 x12.w2 x13.w2 x14.w2 x15.w2
  let out := write16U out (p + 48) x0.w3 x1.w3 x2.w3 x3.w3 x4.w3 x5.w3 x6.w3 x7.w3 x8.w3
    x9.w3 x10.w3 x11.w3 x12.w3 x13.w3 x14.w3 x15.w3
  let out := write16U out (p + 64) x0.w4 x1.w4 x2.w4 x3.w4 x4.w4 x5.w4 x6.w4 x7.w4 x8.w4
    x9.w4 x10.w4 x11.w4 x12.w4 x13.w4 x14.w4 x15.w4
  let out := write16U out (p + 80) x0.w5 x1.w5 x2.w5 x3.w5 x4.w5 x5.w5 x6.w5 x7.w5 x8.w5
    x9.w5 x10.w5 x11.w5 x12.w5 x13.w5 x14.w5 x15.w5
  let out := write16U out (p + 96) x0.w6 x1.w6 x2.w6 x3.w6 x4.w6 x5.w6 x6.w6 x7.w6 x8.w6
    x9.w6 x10.w6 x11.w6 x12.w6 x13.w6 x14.w6 x15.w6
  let out := write16U out (p + 112) x0.w7 x1.w7 x2.w7 x3.w7 x4.w7 x5.w7 x6.w7 x7.w7 x8.w7
    x9.w7 x10.w7 x11.w7 x12.w7 x13.w7 x14.w7 x15.w7
  let out := write16U out (p + 128) x0.w8 x1.w8 x2.w8 x3.w8 x4.w8 x5.w8 x6.w8 x7.w8 x8.w8
    x9.w8 x10.w8 x11.w8 x12.w8 x13.w8 x14.w8 x15.w8
  let out := write16U out (p + 144) x0.w9 x1.w9 x2.w9 x3.w9 x4.w9 x5.w9 x6.w9 x7.w9 x8.w9
    x9.w9 x10.w9 x11.w9 x12.w9 x13.w9 x14.w9 x15.w9
  let out := write16U out (p + 160) x0.w10 x1.w10 x2.w10 x3.w10 x4.w10 x5.w10 x6.w10 x7.w10
    x8.w10 x9.w10 x10.w10 x11.w10 x12.w10 x13.w10 x14.w10 x15.w10
  let out := write16U out (p + 176) x0.w11 x1.w11 x2.w11 x3.w11 x4.w11 x5.w11 x6.w11 x7.w11
    x8.w11 x9.w11 x10.w11 x11.w11 x12.w11 x13.w11 x14.w11 x15.w11
  let out := write16U out (p + 192) x0.w12 x1.w12 x2.w12 x3.w12 x4.w12 x5.w12 x6.w12 x7.w12
    x8.w12 x9.w12 x10.w12 x11.w12 x12.w12 x13.w12 x14.w12 x15.w12
  let out := write16U out (p + 208) x0.w13 x1.w13 x2.w13 x3.w13 x4.w13 x5.w13 x6.w13 x7.w13
    x8.w13 x9.w13 x10.w13 x11.w13 x12.w13 x13.w13 x14.w13 x15.w13
  let out := write16U out (p + 224) x0.w14 x1.w14 x2.w14 x3.w14 x4.w14 x5.w14 x6.w14 x7.w14
    x8.w14 x9.w14 x10.w14 x11.w14 x12.w14 x13.w14 x14.w14 x15.w14
  write16U out (p + 240) x0.w15 x1.w15 x2.w15 x3.w15 x4.w15 x5.w15 x6.w15 x7.w15
    x8.w15 x9.w15 x10.w15 x11.w15 x12.w15 x13.w15 x14.w15 x15.w15
  else out

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
