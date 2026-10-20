/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.InterpolateCoset
public import CompPoly.Univariate.NTTFast.Packed.StorageLemmas

/-!
# Coset interpolation over packed words

`KoalaBear.Fast.interpolateCosetPacked` is `interpolateCoset` on a row-major matrix of Montgomery
words in a `ByteArray`, Plonky3's layout.

* **Base-field weights.** For `t = z₀ - x`, the inverse of `z - x` is `(b₀ + t b₁ + t² b₂ + t³) / N`
  with extension constants `bₖ` that depend on `z` only and the norm `N = N(t)` of `z - x`. So the
  weight `x / (z - x)` is `∑ₖ vₖ bₖ` for the base-field values `vₖ = x tᵏ / N`, and every column
  sum is `∑ₖ Sₖ bₖ` for the base-field sums `Sₖ = ∑ᵢ eᵢ vᵢₖ`.
* **Blocks.** Rows are processed in blocks: one pass stores each row's node, `t²`, norm and
  prefix product of norms, one base-field inversion inverts the block's product, and a backward
  pass overwrites each row with its four weights. The column sums then read the block back.
* **Lazy sums.** A column sum accumulates unreduced 64-bit products, with one conditional
  subtraction per product and one Montgomery reduction per block; four columns share each row's
  weights.
* **Tasks.** Row ranges run on parallel tasks, the caller taking the lowest.

`interpolateCosetPacked_eq` proves the result equal to `interpolateCoset` on the decoded words for
every point off the coset.
-/

@[expose] public section

namespace KoalaBear.Fast

open CompPoly Montgomery.Native32
open CompPoly.CPolynomial.NTTFast.Packed

namespace Ext4

/-- `3 z₂² - 6 z₁ z₃`: `g₀(z - x) = t² + k₀` for `t = z₀ - x`. -/
@[inline] def normK0 (z : Ext4) : Field :=
  triple (z.c2 * z.c2) - triple (z.c1 * z.c3 + z.c1 * z.c3)

/-- `-z₁² - 3 z₃²`: `g₁(z - x) = 2 z₂ t + k₁` for `t = z₀ - x`. -/
@[inline] def normK1 (z : Ext4) : Field := -(z.c1 * z.c1) - triple (z.c3 * z.c3)

/-- The norm `g₀² - 3 g₁²` of `z - x` from `t = z₀ - x`, `t2 = t²` and the constants `k₀`, `k₁`
and `2 z₂`. -/
@[inline] def normAt (k0 k1 z2x2 t t2 : Field) : Field :=
  let g0 := t2 + k0
  let g1 := z2x2 * t + k1
  g0 * g0 - triple (g1 * g1)

/-- `6 a`. -/
@[inline] def six (a : Field) : Field := triple (a + a)

/-- `b₀` in `σ(z - x) (g₀ - g₁ X²) = b₀ + t b₁ + t² b₂ + t³`. -/
def adj0 (z : Ext4) : Ext4 :=
  ⟨-triple (z.c2 * normK1 z), triple (z.c3 * normK1 z) - z.c1 * normK0 z, z.c2 * normK0 z,
    z.c1 * normK1 z - z.c3 * normK0 z⟩

/-- `b₁` in `σ(z - x) (g₀ - g₁ X²) = b₀ + t b₁ + t² b₂ + t³`. -/
def adj1 (z : Ext4) : Ext4 :=
  ⟨normK0 z - six (z.c2 * z.c2), six (z.c2 * z.c3), -normK1 z, z.c1 * z.c2 + z.c1 * z.c2⟩

/-- `b₂` in `σ(z - x) (g₀ - g₁ X²) = b₀ + t b₁ + t² b₂ + t³`. -/
def adj2 (z : Ext4) : Ext4 := ⟨0, -z.c1, -z.c2, -z.c3⟩

end Ext4

/-- Four base-field sums: a column sum's coordinates over `b₀, b₁, b₂, 1`. -/
structure Quad where
  s0 : Field
  s1 : Field
  s2 : Field
  s3 : Field

namespace Quad

instance : Zero Quad := ⟨⟨0, 0, 0, 0⟩⟩
instance : Inhabited Quad := ⟨0⟩
instance : Add Quad := ⟨fun a b ↦ ⟨a.s0 + b.s0, a.s1 + b.s1, a.s2 + b.s2, a.s3 + b.s3⟩⟩

/-- `s₀ b₀ + s₁ b₁ + s₂ b₂ + s₃` for the point `z`. -/
def combine (z : Ext4) (q : Quad) : Ext4 :=
  Ext4.smul q.s0 (Ext4.adj0 z) + Ext4.smul q.s1 (Ext4.adj1 z) + Ext4.smul q.s2 (Ext4.adj2 z) +
    Ext4.ofBase q.s3

end Quad

/-- The words of a byte array, as residues. -/
def decodeWords (b : ByteArray) : Array Field :=
  Array.ofFn (n := b.size / 4) fun k ↦ ofWordMod (b.getUInt32LE! (4 * k.val))

namespace InterpolatePacked

/-- A lazy column-sum accumulator. -/
abbrev Acc : Type := LazyAcc KoalaBear.fieldSize

/-- Rows per block. -/
def blockRows : ℕ := 512

/-- A stored residue; a word from the modulus up reads as zero. -/
@[inline] def wordField (x : UInt32) : Field :=
  if h : x < 2130706433 then ⟨x, by rw [UInt32.lt_iff_toNat_lt] at h; exact h⟩ else 0

theorem wordField_val (x : Field) : wordField x.val = x := by
  have hx : x.val < 2130706433 := by rw [UInt32.lt_iff_toNat_lt]; exact x.property
  simp only [wordField, hx, ↓reduceDIte]; rfl

/-- Word `i + o` of a buffer of residues. -/
@[inline] def readField (b : @& ByteArray) (i o : USize)
    (h : 4 * (i.toNat + o.toNat) + 3 < b.size ∧ b.size < USize.size) : Field :=
  wordField (Native.readUOffset b i o h)

/-- `n` rows from row `i` of a block, from node `x`: store `x`, `t²`, the norm `N` of `z - x` and
the product `acc` of the norms before it at words `4 i, …, 4 i + 3`. Returns the buffer, the
product of all norms and the next node. -/
def forward (ω z0 k0 k1 z2x2 : Field) : ℕ → USize → Field → Field → ByteArray →
    ByteArray × Field × Field
  | 0, _, x, acc, buf => (buf, acc, x)
  | n + 1, i, x, acc, buf =>
    let t := z0 - x
    let t2 := t * t
    let nm := Ext4.normAt k0 k1 z2x2 t t2
    forward ω z0 k0 k1 z2x2 n (i + 1) (x * ω) (acc * nm)
      (Native.storeWords buf (16 * i) 4 x.val t2.val nm.val acc.val 0 0 0 0 0 0 0 0 0 0 0 0)

theorem size_forward (ω z0 k0 k1 z2x2 : Field) (n : ℕ) (i : USize) (x acc : Field)
    (buf : ByteArray) : (forward ω z0 k0 k1 z2x2 n i x acc buf).1.size = buf.size := by
  induction n generalizing i x acc buf with
  | zero => rfl
  | succ n ih => rw [forward, ih, Native.size_storeWords]

theorem usize_four_mul (j : USize) (n : ℕ) (h : 16 * j.toNat ≤ n) (hn : n < USize.size) :
    (4 * j).toNat = 4 * j.toNat := by
  have hsize : (2 : ℕ) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_mul, Native.usize_numeral 4 (by decide), hsize]
  exact Nat.mod_eq_of_lt (by omega)

theorem usize_add_lt (a b : USize) (h : a.toNat + b.toNat < USize.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  have hsize : (2 : ℕ) ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, hsize, Nat.mod_eq_of_lt h]

/-- `n` rows back from row `i` of a block: `inv` inverts the product of the norms before row `i`.
Row `i - 1`'s norm inverse is `inv` times its prefix product; its words become its weights
`u, u t, u t², u t³` for `u = x / N`, and `inv` times its norm inverts the earlier prefix. -/
def backward (z0 : Field) : (n : ℕ) → (i : USize) → Field → (buf : ByteArray) →
    16 * i.toNat ≤ buf.size ∧ buf.size < USize.size ∧ n ≤ i.toNat → ByteArray
  | 0, _, _, buf, _ => buf
  | n + 1, i, inv, buf, h =>
    have hj : (i - 1).toNat = i.toNat - 1 := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; simp; omega)]; simp
    have h4 := usize_four_mul (i - 1) buf.size (by omega) h.2.1
    let x := readField buf (4 * (i - 1)) 0 (by
      rw [h4, Native.usize_numeral 0 (by decide)]; exact ⟨by omega, h.2.1⟩)
    let t2 := readField buf (4 * (i - 1)) 1 (by
      rw [h4, Native.usize_numeral 1 (by decide)]; exact ⟨by omega, h.2.1⟩)
    let nm := readField buf (4 * (i - 1)) 2 (by
      rw [h4, Native.usize_numeral 2 (by decide)]; exact ⟨by omega, h.2.1⟩)
    let pre := readField buf (4 * (i - 1)) 3 (by
      rw [h4, Native.usize_numeral 3 (by decide)]; exact ⟨by omega, h.2.1⟩)
    let u := x * (inv * pre)
    let v1 := u * (z0 - x)
    backward z0 n (i - 1) (inv * nm)
      (Native.storeWords buf (16 * (i - 1)) 4 u.val v1.val (u * t2).val (v1 * t2).val
        0 0 0 0 0 0 0 0 0 0 0 0)
      (by rw [Native.size_storeWords]; omega)

theorem size_backward (z0 : Field) (n : ℕ) (i : USize) (inv : Field) (buf : ByteArray) (h) :
    (backward z0 n i inv buf h).size = buf.size := by
  induction n generalizing i inv buf with
  | zero => rfl
  | succ n ih => rw [backward, ih, Native.size_storeWords]

/-- One column of `n` block rows: `e` steps through the column's words by `width`, `w` through
the rows' weights. -/
def dot1 (evals buf : @& ByteArray) (width : USize) : (n : ℕ) → (e w : USize) →
    (a0 a1 a2 a3 : Acc) →
    (∀ r < n, 4 * (e.toNat + r * width.toNat) + 3 < evals.size) ∧ evals.size < USize.size ∧
      4 * (w.toNat + 4 * n) ≤ buf.size ∧ buf.size < USize.size → Quad
  | 0, _, _, a0, a1, a2, a3, _ => ⟨a0.result, a1.result, a2.result, a3.result⟩
  | n + 1, e, w, a0, a1, a2, a3, h =>
    have h0 := Native.usize_numeral 0 (by decide)
    have h1 := Native.usize_numeral 1 (by decide)
    have h2 := Native.usize_numeral 2 (by decide)
    have h3 := Native.usize_numeral 3 (by decide)
    have he := h.1 0 (by omega)
    let v := Native.readUOffset evals e 0 (by rw [h0]; simp at he; exact ⟨by omega, h.2.1⟩)
    let w0 := readField buf w 0 (by rw [h0]; exact ⟨by omega, h.2.2.2⟩)
    let w1 := readField buf w 1 (by rw [h1]; exact ⟨by omega, h.2.2.2⟩)
    let w2 := readField buf w 2 (by rw [h2]; exact ⟨by omega, h.2.2.2⟩)
    let w3 := readField buf w 3 (by rw [h3]; exact ⟨by omega, h.2.2.2⟩)
    dot1 evals buf width n (e + width) (w + 4) (a0.add v w0) (a1.add v w1) (a2.add v w2)
      (a3.add v w3) (by
        refine ⟨fun r hr ↦ ?_, h.2.1, ?_, h.2.2.2⟩
        · have := h.1 (r + 1) (by omega)
          have h1' := h.1 1 (by omega)
          rw [Nat.one_mul] at h1'
          rw [usize_add_lt _ _ (by have := h.2.1; omega)]
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        · have hb := h.2.2.2
          have h4 : (4 : USize).toNat = 4 := Native.usize_numeral 4 (by decide)
          rw [usize_add_lt _ _ (by rw [h4]; omega), h4]
          omega)

/-- Four adjacent columns of `n` block rows, sharing each row's weights. -/
def dot4 (evals buf : @& ByteArray) (width : USize) : (n : ℕ) → (e w : USize) →
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Acc) →
    (∀ r < n, 4 * (e.toNat + r * width.toNat + 3) + 3 < evals.size) ∧
      evals.size < USize.size ∧ 4 * (w.toNat + 4 * n) ≤ buf.size ∧ buf.size < USize.size →
    Quad × Quad × Quad × Quad
  | 0, _, _, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3, _ =>
    (⟨a0.result, a1.result, a2.result, a3.result⟩, ⟨b0.result, b1.result, b2.result, b3.result⟩,
      ⟨c0.result, c1.result, c2.result, c3.result⟩, ⟨d0.result, d1.result, d2.result, d3.result⟩)
  | n + 1, e, w, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3, h =>
    have h0 := Native.usize_numeral 0 (by decide)
    have h1 := Native.usize_numeral 1 (by decide)
    have h2 := Native.usize_numeral 2 (by decide)
    have h3 := Native.usize_numeral 3 (by decide)
    have he := h.1 0 (by omega)
    let v0 := Native.readUOffset evals e 0 (by rw [h0]; simp at he; exact ⟨by omega, h.2.1⟩)
    let v1 := Native.readUOffset evals e 1 (by rw [h1]; simp at he; exact ⟨by omega, h.2.1⟩)
    let v2 := Native.readUOffset evals e 2 (by rw [h2]; simp at he; exact ⟨by omega, h.2.1⟩)
    let v3 := Native.readUOffset evals e 3 (by rw [h3]; simp at he; exact ⟨by omega, h.2.1⟩)
    let w0 := readField buf w 0 (by rw [h0]; exact ⟨by omega, h.2.2.2⟩)
    let w1 := readField buf w 1 (by rw [h1]; exact ⟨by omega, h.2.2.2⟩)
    let w2 := readField buf w 2 (by rw [h2]; exact ⟨by omega, h.2.2.2⟩)
    let w3 := readField buf w 3 (by rw [h3]; exact ⟨by omega, h.2.2.2⟩)
    dot4 evals buf width n (e + width) (w + 4)
      (a0.add v0 w0) (a1.add v0 w1) (a2.add v0 w2) (a3.add v0 w3)
      (b0.add v1 w0) (b1.add v1 w1) (b2.add v1 w2) (b3.add v1 w3)
      (c0.add v2 w0) (c1.add v2 w1) (c2.add v2 w2) (c3.add v2 w3)
      (d0.add v3 w0) (d1.add v3 w1) (d2.add v3 w2) (d3.add v3 w3) (by
        refine ⟨fun r hr ↦ ?_, h.2.1, ?_, h.2.2.2⟩
        · have := h.1 (r + 1) (by omega)
          have h1' := h.1 1 (by omega)
          rw [Nat.one_mul] at h1'
          rw [usize_add_lt _ _ (by have := h.2.1; omega)]
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        · have hb := h.2.2.2
          have h4 : (4 : USize).toNat = 4 := Native.usize_numeral 4 (by decide)
          rw [usize_add_lt _ _ (by rw [h4]; omega), h4]
          omega)

theorem dot_bound (row b width c r k : ℕ) (hr : r < b) (hc : c + k + 1 ≤ width) :
    row * width + c + r * width + k < (row + b) * width := by
  have := Nat.mul_le_mul_right width (show r + 1 ≤ b from hr)
  rw [Nat.add_mul, Nat.one_mul] at this
  rw [Nat.add_mul]
  omega

theorem toUSize_toNat_of_lt (a n : ℕ) (h : a < n) (hn : n < USize.size) : a.toUSize.toNat = a :=
  USize.toNat_ofNat_of_lt' (by omega)

/-- The block's evaluation words and weights fit: rows `row, …, row + b - 1` of a
`width`-column matrix in `evals`, and `b` rows of weights in `buf`. -/
def BlockFits (evals buf : ByteArray) (width row b : ℕ) : Prop :=
  4 * ((row + b) * width) ≤ evals.size ∧ evals.size < USize.size ∧ 16 * b ≤ buf.size ∧
    buf.size < USize.size

theorem blockFits_dot {evals buf : ByteArray} {width row b : ℕ}
    (h : BlockFits evals buf width row b) (c k : ℕ) (hc : c + k + 1 ≤ width) :
    (∀ r < b, 4 * ((row * width + c).toUSize.toNat + r * width.toUSize.toNat + k) + 3 <
      evals.size) ∧ evals.size < USize.size ∧ 4 * ((0 : USize).toNat + 4 * b) ≤ buf.size ∧
      buf.size < USize.size := by
  obtain ⟨he, hes, hb, hbs⟩ := h
  refine ⟨fun r hr ↦ ?_, hes, by simp only [USize.toNat_zero]; omega, hbs⟩
  have hd := dot_bound row b width c r k hr hc
  have hw := dot_bound row b width c 0 k (by omega) hc
  rw [Nat.zero_mul, Nat.add_zero] at hw
  have hw' : width ≤ (row + b) * width := Nat.le_mul_of_pos_left _ (by omega)
  rw [toUSize_toNat_of_lt _ ((row + b) * width) (by omega) (by omega),
    toUSize_toNat_of_lt _ ((row + b) * width + 1) (by omega) (by omega)]
  omega

/-- Add the block's sums of the four columns from `c` into `sums`. -/
def addColumns4 (evals buf : @& ByteArray) (width row b : ℕ)
    (hfit : BlockFits evals buf width row b) (c : ℕ) (hc : c + 4 ≤ width) (sums : Array Quad) :
    Array Quad :=
  let a : Acc := LazyAcc.zero
  let q := dot4 evals buf width.toUSize b (row * width + c).toUSize 0 a a a a a a a a a a a a
    a a a a (blockFits_dot hfit c 3 (by omega))
  (((sums.modify c (· + q.1)).modify (c + 1) (· + q.2.1)).modify (c + 2) (· + q.2.2.1)).modify
    (c + 3) (· + q.2.2.2)

/-- Add the block's sums of `g` groups of four columns from column `c` into `sums`. -/
def columns4 (evals buf : @& ByteArray) (width row b : ℕ) (hfit : BlockFits evals buf width row b) :
    (g c : ℕ) → c + 4 * g ≤ width → Array Quad → Array Quad
  | 0, _, _, sums => sums
  | g + 1, c, hc, sums =>
    columns4 evals buf width row b hfit g (c + 4) (by omega)
      (addColumns4 evals buf width row b hfit c (by omega) sums)

/-- Add the block's sum of column `c` into `sums`. -/
def addColumn (evals buf : @& ByteArray) (width row b : ℕ)
    (hfit : BlockFits evals buf width row b) (c : ℕ) (hc : c + 1 ≤ width) (sums : Array Quad) :
    Array Quad :=
  let a : Acc := LazyAcc.zero
  sums.modify c (· + dot1 evals buf width.toUSize b (row * width + c).toUSize 0 a a a a (by
    have := blockFits_dot hfit c 0 (by omega)
    simp only [Nat.add_zero] at this
    exact this))

/-- Add the block's sums of `k` single columns from column `c` into `sums`. -/
def columns1 (evals buf : @& ByteArray) (width row b : ℕ) (hfit : BlockFits evals buf width row b) :
    (k c : ℕ) → c + k ≤ width → Array Quad → Array Quad
  | 0, _, _, sums => sums
  | k + 1, c, hc, sums =>
    columns1 evals buf width row b hfit k (c + 1) (by omega)
      (addColumn evals buf width row b hfit c (by omega) sums)

/-- Blocks of rows from `row` up to `hi`, `k` of them, from node `x`. -/
def blocks (evals : @& ByteArray) (ω z0 k0 k1 z2x2 : Field) (width hi : ℕ) :
    (k row : ℕ) → Field → (buf : ByteArray) → Array Quad →
    row ≤ hi ∧ 4 * (hi * width) ≤ evals.size ∧ evals.size < USize.size ∧
      buf.size = 16 * blockRows → Array Quad
  | 0, _, _, _, sums, _ => sums
  | k + 1, row, x, buf, sums, h =>
    let b := min blockRows (hi - row)
    have hb : b ≤ blockRows := Nat.min_le_left _ _
    have hu := USize.le_size
    have hbt : b.toUSize.toNat = b := toUSize_toNat_of_lt b (blockRows + 1) (by
      omega) (by simp only [blockRows]; omega)
    let f := forward ω z0 k0 k1 z2x2 b 0 x 1 buf
    let buf := backward z0 b b.toUSize f.2.1⁻¹ f.1 (by
      rw [size_forward, h.2.2.2, hbt]; simp only [blockRows] at hb ⊢
      exact ⟨by omega, by omega, le_refl _⟩)
    have hbuf : buf.size = 16 * blockRows := by
      simp only [buf, size_backward, f, size_forward, h.2.2.2]
    have hfit : BlockFits evals buf width row b := by
      have hr : row + b ≤ hi := by have := Nat.min_le_right blockRows (hi - row); omega
      have := Nat.mul_le_mul_right width hr
      refine ⟨by omega, h.2.2.1, by omega, ?_⟩
      rw [hbuf]; simp only [blockRows]; omega
    let sums := columns4 evals buf width row b hfit (width / 4) 0 (by omega) sums
    let sums := columns1 evals buf width row b hfit (width % 4) (4 * (width / 4)) (by omega) sums
    blocks evals ω z0 k0 k1 z2x2 width hi k (row + b) f.2.2 buf sums (by
      have := Nat.min_le_right blockRows (hi - row)
      exact ⟨by omega, h.2.1, h.2.2.1, hbuf⟩)

/-- The column sums of rows `lo, …, hi - 1`. -/
def leaf (evals : @& ByteArray) (ω s : Field) (z : Ext4) (width lo hi : ℕ)
    (h : lo ≤ hi ∧ 4 * (hi * width) ≤ evals.size ∧ evals.size < USize.size) : Array Quad :=
  blocks evals ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) width hi
    ((hi - lo + blockRows - 1) / blockRows) lo (s * Montgomery.Native32.pow ω lo)
    (ByteArray.mk (Array.replicate (16 * blockRows) 0)) (Array.replicate width 0)
    ⟨h.1, h.2.1, h.2.2, by simp [ByteArray.size]⟩

/-- Add the lower half's sums, computed by the caller, to the upper half's task. -/
@[noinline] def join (upper : Task (Array Quad)) (low : Unit → Array Quad) : Array Quad :=
  let low := low ()
  Array.zipWith (· + ·) low upper.get

/-- The column sums of rows `lo, …, hi - 1` over `2 ^ depth` tasks; the caller takes the lowest
range. -/
def tree (evals : ByteArray) (ω s : Field) (z : Ext4) (width : ℕ) (lo hi : ℕ)
    (h : lo ≤ hi ∧ 4 * (hi * width) ≤ evals.size ∧ evals.size < USize.size) : ℕ → Array Quad
  | 0 => leaf evals ω s z width lo hi h
  | depth + 1 =>
    let mid := lo + (hi - lo) / 2
    have hm : mid ≤ hi := by omega
    have := Nat.mul_le_mul_right width hm
    join (Task.spawn fun _ ↦ tree evals ω s z width mid hi ⟨by omega, h.2⟩ depth)
      (fun _ ↦ tree evals ω s z width lo mid ⟨by omega, by omega, h.2.2⟩ depth)

end InterpolatePacked

open InterpolatePacked in
/-- `interpolateCoset` on a row-major `2^logN × width` matrix of Montgomery words, over up to
`2 ^ logTasks` tasks. -/
def interpolateCosetPacked (logN : ℕ) (ω s : Field) (width : ℕ) (evals : ByteArray) (z : Ext4)
    (logTasks : ℕ := 3) : Array Ext4 :=
  if h : evals.size = 4 * (2 ^ logN * width) ∧ evals.size < USize.size then
    let sums := tree evals ω s z width 0 (2 ^ logN) ⟨Nat.zero_le _, h.1.ge, h.2⟩
      (min logTasks (logN - 9))
    let factor := cosetFactor logN s z
    sums.map fun q ↦ factor * q.combine z
  else interpolateCoset logN ω s width (decodeWords evals) z

end KoalaBear.Fast
