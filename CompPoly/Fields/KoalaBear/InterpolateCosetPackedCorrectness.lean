/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

public import CompPoly.Fields.KoalaBear.InterpolateCosetPacked

/-!
# Correctness of coset interpolation over packed words

`interpolateCosetPacked_eq` proves `interpolateCosetPacked` equal to `interpolateCoset` on the
decoded words, for every point off the coset.
-/

@[expose] public section

namespace KoalaBear.Fast

open CompPoly CompPoly.Extension Montgomery.Native32 Polynomial
open CompPoly.CPolynomial.NTTFast.Packed

namespace Ext4

@[simp] theorem add_c0 (a b : Ext4) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Ext4) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Ext4) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem add_c3 (a b : Ext4) : (a + b).c3 = a.c3 + b.c3 := rfl
@[simp] theorem sub_c0 (a b : Ext4) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Ext4) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Ext4) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem sub_c3 (a b : Ext4) : (a - b).c3 = a.c3 - b.c3 := rfl
@[simp] theorem ofBase_c0 (x : Field) : (ofBase x).c0 = x := rfl
@[simp] theorem ofBase_c1 (x : Field) : (ofBase x).c1 = 0 := rfl
@[simp] theorem ofBase_c2 (x : Field) : (ofBase x).c2 = 0 := rfl
@[simp] theorem ofBase_c3 (x : Field) : (ofBase x).c3 = 0 := rfl
@[simp] theorem smul_c0 (x : Field) (a : Ext4) : (smul x a).c0 = x * a.c0 := rfl
@[simp] theorem smul_c1 (x : Field) (a : Ext4) : (smul x a).c1 = x * a.c1 := rfl
@[simp] theorem smul_c2 (x : Field) (a : Ext4) : (smul x a).c2 = x * a.c2 := rfl
@[simp] theorem smul_c3 (x : Field) (a : Ext4) : (smul x a).c3 = x * a.c3 := rfl

/-- The norm of `z - x` in terms of `t = z₀ - x`. -/
theorem norm_sub_ofBase (z : Ext4) (x : Field) :
    norm (z - ofBase x) =
      normAt (normK0 z) (normK1 z) (z.c2 + z.c2) (z.c0 - x) ((z.c0 - x) * (z.c0 - x)) := by
  apply toField_injective
  simp only [norm, g0, g1, normAt, normK0, normK1, triple, toField_add, toField_sub, toField_mul,
    toField_neg, sub_c0, sub_c1, sub_c2, sub_c3, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3,
    toField_zero]
  ring

/-- **The weight of a node.** `x / (z - x)` is `u b₀ + u t b₁ + u t² b₂ + u t³` for `t = z₀ - x`
and `u = x / N`, `N` the norm of `z - x`. -/
theorem smul_inv_sub_ofBase (z : Ext4) (x : Field) :
    smul x (z - ofBase x)⁻¹ =
      let t := z.c0 - x
      let u := x * (normAt (normK0 z) (normK1 z) (z.c2 + z.c2) t (t * t))⁻¹
      Quad.combine z ⟨u, u * t, u * (t * t), u * t * (t * t)⟩ := by
  rw [show (z - ofBase x)⁻¹ = inv (z - ofBase x) from rfl]
  unfold inv
  rw [norm_sub_ofBase]
  apply ext' <;> apply toField_injective <;>
    simp only [Quad.combine, adj0, adj1, adj2, g0, g1, six, normK0, normK1, triple, add_c0, add_c1,
      add_c2, add_c3, sub_c0, sub_c1, sub_c2, sub_c3, ofBase_c0, ofBase_c1, ofBase_c2, ofBase_c3,
      smul_c0, smul_c1, smul_c2, smul_c3, toField_add, toField_sub, toField_mul, toField_neg,
      toField_zero, toField_inv] <;>
    ring

end Ext4

namespace Quad

@[simp] theorem add_s0 (a b : Quad) : (a + b).s0 = a.s0 + b.s0 := rfl
@[simp] theorem add_s1 (a b : Quad) : (a + b).s1 = a.s1 + b.s1 := rfl
@[simp] theorem add_s2 (a b : Quad) : (a + b).s2 = a.s2 + b.s2 := rfl
@[simp] theorem add_s3 (a b : Quad) : (a + b).s3 = a.s3 + b.s3 := rfl
@[simp] theorem zero_s0 : (0 : Quad).s0 = 0 := rfl
@[simp] theorem zero_s1 : (0 : Quad).s1 = 0 := rfl
@[simp] theorem zero_s2 : (0 : Quad).s2 = 0 := rfl
@[simp] theorem zero_s3 : (0 : Quad).s3 = 0 := rfl

/-- A column sum in the spec field: `s₀ b₀ + s₁ b₁ + s₂ b₂ + s₃`. -/
theorem toSpec_combine (z : Ext4) (q : Quad) :
    Ext4.toSpec (q.combine z) =
      FastField.toField q.s0 • Ext4.toSpec (Ext4.adj0 z) +
        FastField.toField q.s1 • Ext4.toSpec (Ext4.adj1 z) +
        FastField.toField q.s2 • Ext4.toSpec (Ext4.adj2 z) + FastField.toField q.s3 • 1 := by
  simp only [combine, Ext4.toSpec_add, Ext4.toSpec_smul, Ext4.toSpec_ofBase,
    ← Ext.algebraMap_eq_ofBase, Algebra.algebraMap_eq_smul_one]

theorem toSpec_combine_add (z : Ext4) (a b : Quad) :
    Ext4.toSpec ((a + b).combine z) = Ext4.toSpec (a.combine z) + Ext4.toSpec (b.combine z) := by
  simp only [toSpec_combine, add_s0, add_s1, add_s2, add_s3, toField_add, add_smul]
  abel

@[simp] theorem toSpec_combine_zero (z : Ext4) : Ext4.toSpec ((0 : Quad).combine z) = 0 := by
  simp only [toSpec_combine, zero_s0, zero_s1, zero_s2, zero_s3, toField_zero, zero_smul,
    add_zero]

end Quad

namespace InterpolatePacked

/-! ### Words in byte arrays -/

/-- An unchecked read is the word at its index. -/
theorem readUOffset_eq (b : ByteArray) (i o : USize) (h) :
    Native.readUOffset b i o h = b.getUInt32LE! (4 * (i.toNat + o.toNat)) := by
  have hb : 4 * (i.toNat + o.toNat) + 3 < USize.size := h.1.trans h.2
  rw [Native.readUOffset, Native.ugetUInt32LE_eq, Native.wordOffset_toNat i o hb]

/-- Word `4 r + k` of a word array: coordinate `k` of row `r`. -/
def row (W : Array UInt32) (r k : ℕ) : UInt32 := W.getD (4 * r + k) 0

/-- Overwrite row `j` of a word array. -/
def setRow (W : Array UInt32) (j : ℕ) (v0 v1 v2 v3 : UInt32) : Array UInt32 :=
  W.extract 0 (4 * j) ++
    #[v0, v1, v2, v3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].extract 0 (4 : UInt8).toNat ++
      W.extract (4 * j + (4 : UInt8).toNat) W.size

theorem size_setRow (W : Array UInt32) (j : ℕ) (v0 v1 v2 v3 : UInt32) (hj : 4 * j + 4 ≤ W.size) :
    (setRow W j v0 v1 v2 v3).size = W.size := by
  simp only [setRow, Array.size_append, Array.size_extract, List.size_toArray, List.length_cons,
    List.length_nil]
  change min (4 * j) W.size - 0 + (min 4 16 - 0) + (min W.size W.size - (4 * j + 4)) = W.size
  omega

theorem getD_setRow (W : Array UInt32) (j : ℕ) (v0 v1 v2 v3 : UInt32) (hj : 4 * j + 4 ≤ W.size)
    (m : ℕ) :
    (setRow W j v0 v1 v2 v3).getD m 0 =
      if m < 4 * j then W.getD m 0
      else if m < 4 * j + 4 then #[v0, v1, v2, v3].getD (m - 4 * j) 0 else W.getD m 0 := by
  simp only [setRow, Array.getD_eq_getD_getElem?]
  change (W.extract 0 (4 * j) ++ #[v0, v1, v2, v3] ++ W.extract (4 * j + 4) W.size)[m]?.getD 0 = _
  have hA : (W.extract 0 (4 * j)).size = 4 * j := by rw [Array.size_extract]; omega
  have hB : (W.extract 0 (4 * j) ++ #[v0, v1, v2, v3]).size = 4 * j + 4 := by
    rw [Array.size_append, hA]; rfl
  split_ifs with h1 h2
  · rw [Array.getElem?_append_left (by rw [hB]; omega),
      Array.getElem?_append_left (by rw [hA]; omega), Array.getElem?_extract]
    simp only [Nat.zero_add, show m < min (4 * j) W.size - 0 by omega, ↓reduceIte]
  · rw [Array.getElem?_append_left (by rw [hB]; omega),
      Array.getElem?_append_right (by rw [hA]; omega), hA]
  · rw [Array.getElem?_append_right (by rw [hB]; omega), hB, Array.getElem?_extract]
    by_cases hm : m < W.size
    · simp only [show m - (4 * j + 4) < min W.size W.size - (4 * j + 4) by omega, ↓reduceIte]
      congr 2; omega
    · simp only [show ¬m - (4 * j + 4) < min W.size W.size - (4 * j + 4) by omega, ↓reduceIte,
        Array.getElem?_eq_none (show W.size ≤ m by omega)]

theorem row_setRow_ne (W : Array UInt32) (j : ℕ) (v0 v1 v2 v3 : UInt32) (hj : 4 * j + 4 ≤ W.size)
    (r k : ℕ) (hk : k < 4) (hr : r ≠ j) : row (setRow W j v0 v1 v2 v3) r k = row W r k := by
  simp only [row, getD_setRow W j v0 v1 v2 v3 hj]
  split_ifs <;> first | rfl | omega

theorem row_setRow (W : Array UInt32) (j : ℕ) (v0 v1 v2 v3 : UInt32) (hj : 4 * j + 4 ≤ W.size) :
    row (setRow W j v0 v1 v2 v3) j 0 = v0 ∧ row (setRow W j v0 v1 v2 v3) j 1 = v1 ∧
      row (setRow W j v0 v1 v2 v3) j 2 = v2 ∧ row (setRow W j v0 v1 v2 v3) j 3 = v3 := by
  simp only [row, getD_setRow W j v0 v1 v2 v3 hj, Nat.add_sub_cancel_left,
    show ¬4 * j + 0 < 4 * j by omega, show 4 * j + 0 < 4 * j + 4 by omega,
    show ¬4 * j + 1 < 4 * j by omega, show 4 * j + 1 < 4 * j + 4 by omega,
    show ¬4 * j + 2 < 4 * j by omega, show 4 * j + 2 < 4 * j + 4 by omega,
    show ¬4 * j + 3 < 4 * j by omega, show 4 * j + 3 < 4 * j + 4 by omega, ↓reduceIte]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Storing four words at row `j` of a packed array. -/
theorem storeRow (W : Array UInt32) (j : USize) (hj : 4 * j.toNat + 4 ≤ W.size)
    (hs : 4 * W.size < USize.size) (v0 v1 v2 v3 : UInt32) :
    Native.storeWords (PackedRepr.encode W) (16 * j) 4 v0 v1 v2 v3 0 0 0 0 0 0 0 0 0 0 0 0 =
      PackedRepr.encode (setRow W j.toNat v0 v1 v2 v3) := by
  have hsize : (2 : ℕ) ^ System.Platform.numBits = USize.size := rfl
  rw [Native.storeWords_replace_encodeWords W (16 * j) 4 (4 * j.toNat) (by decide) (by
      rw [USize.toNat_mul, Native.usize_numeral 16 (by decide), hsize,
        Nat.mod_eq_of_lt (by omega)]
      omega) (by change 4 * j.toNat + 4 ≤ W.size; omega)
      (by rw [PackedRepr.size_encode_uint32]; exact hs)]
  rfl

/-! ### The forward pass -/

/-- The nodes `x, x ω, x ω², …` as the passes compute them. -/
def nodeAt (ω x : Field) : ℕ → Field
  | 0 => x
  | r + 1 => nodeAt ω (x * ω) r

/-- The norm of `z - x`, with `z`'s constants. -/
def rowNorm (z0 k0 k1 z2x2 x : Field) : Field :=
  Ext4.normAt k0 k1 z2x2 (z0 - x) ((z0 - x) * (z0 - x))

/-- `acc` times the norms of the first `r` nodes. -/
def normPrefix (ω z0 k0 k1 z2x2 : Field) (x acc : Field) : ℕ → Field
  | 0 => acc
  | r + 1 => normPrefix ω z0 k0 k1 z2x2 (x * ω) (acc * rowNorm z0 k0 k1 z2x2 x) r

theorem usize_add_one_of (i : USize) (n : ℕ) (h : i.toNat + 1 ≤ n) (hn : n < USize.size) :
    (i + 1).toNat = i.toNat + 1 := by
  rw [usize_add_lt i 1 (by rw [USize.toNat_one]; omega), USize.toNat_one]

/-- The forward pass stores each row's node, `t²`, norm and norm prefix, and returns the product
of all norms and the next node. -/
theorem forward_spec (ω z0 k0 k1 z2x2 : Field) (n : ℕ) (i : USize) (x acc : Field)
    (W : Array UInt32) (hW : 4 * (i.toNat + n) ≤ W.size) (hs : 4 * W.size < USize.size) :
    ∃ W', forward ω z0 k0 k1 z2x2 n i x acc (PackedRepr.encode W) =
        (PackedRepr.encode W', normPrefix ω z0 k0 k1 z2x2 x acc n, nodeAt ω x n) ∧
      W'.size = W.size ∧
      (∀ r k, k < 4 → (r < i.toNat ∨ i.toNat + n ≤ r) → row W' r k = row W r k) ∧
      ∀ r < n, row W' (i.toNat + r) 0 = (nodeAt ω x r).val ∧
        row W' (i.toNat + r) 1 = ((z0 - nodeAt ω x r) * (z0 - nodeAt ω x r)).val ∧
        row W' (i.toNat + r) 2 = (rowNorm z0 k0 k1 z2x2 (nodeAt ω x r)).val ∧
        row W' (i.toNat + r) 3 = (normPrefix ω z0 k0 k1 z2x2 x acc r).val := by
  induction n generalizing i x acc W with
  | zero =>
    exact ⟨W, rfl, rfl, fun _ _ _ _ ↦ rfl, fun r hr ↦ absurd hr (Nat.not_lt_zero r)⟩
  | succ n ih =>
    have hi1 := usize_add_one_of i W.size (by omega) (by omega)
    have hj : 4 * i.toNat + 4 ≤ W.size := by omega
    rw [forward, storeRow W i hj hs]
    obtain ⟨W', heq, hsize, hout, hrows⟩ := ih (i + 1) (x * ω)
      (acc * rowNorm z0 k0 k1 z2x2 x) (setRow W i.toNat x.val ((z0 - x) * (z0 - x)).val
        (rowNorm z0 k0 k1 z2x2 x).val acc.val)
      (by rw [size_setRow W _ _ _ _ _ hj, hi1]; omega)
      (by rw [size_setRow W _ _ _ _ _ hj]; exact hs)
    have hW1 := row_setRow W i.toNat x.val ((z0 - x) * (z0 - x)).val
      (rowNorm z0 k0 k1 z2x2 x).val acc.val hj
    refine ⟨W', heq, by rw [hsize, size_setRow W _ _ _ _ _ hj], fun r k hk hr ↦ ?_,
      fun r hr ↦ ?_⟩
    · rw [hout r k hk (by omega), row_setRow_ne W _ _ _ _ _ hj r k hk (by omega)]
    · rcases r with _ | r
      · have hl : i.toNat < (i + 1).toNat ∨ (i + 1).toNat + n ≤ i.toNat := Or.inl (by omega)
        rw [Nat.add_zero, hout _ 0 (by omega) hl, hout _ 1 (by omega) hl, hout _ 2 (by omega) hl,
          hout _ 3 (by omega) hl]
        exact hW1
      · have := hrows r (by omega)
        rw [hi1, show i.toNat + 1 + r = i.toNat + (r + 1) by omega] at this
        exact this

/-! ### The backward pass -/

theorem readField_pack (W : Array UInt32) (i o : USize) (h) :
    readField (PackedRepr.encode W) i o h = wordField (W.getD (i.toNat + o.toNat) 0) := by
  rw [readField, readUOffset_eq, PackedRepr.getUInt32LE!_encode]

/-- Peeling one norm off the inverse of a prefix product. -/
theorem inv_mul_prefix (p m : Field) (hp : p ≠ 0) (hm : m ≠ 0) :
    (p * m)⁻¹ * p = m⁻¹ ∧ (p * m)⁻¹ * m = p⁻¹ := by
  have hp' : FastField.toField p ≠ 0 := fun h ↦ hp (toField_injective (by rw [h, toField_zero]))
  have hm' : FastField.toField m ≠ 0 := fun h ↦ hm (toField_injective (by rw [h, toField_zero]))
  constructor <;> apply toField_injective <;>
    simp only [toField_mul, toField_inv, mul_inv_rev] <;> field_simp

/-- The backward pass turns rows `i - n, …, i - 1` of node, `t²`, norm and prefix product into
the weights `u, u t, u t², u t³` for `u = x / N`, given that `inv` inverts the prefix product
before row `i`. -/
theorem backward_spec (z0 : Field) (X T2 Nn Pp : ℕ → Field) (n : ℕ) (i : USize) (inv : Field)
    (W : Array UInt32) (h) (hW : 4 * i.toNat ≤ W.size)
    (hrows : ∀ r < i.toNat, row W r 0 = (X r).val ∧ row W r 1 = (T2 r).val ∧
      row W r 2 = (Nn r).val ∧ row W r 3 = (Pp r).val)
    (hP : ∀ r < i.toNat, Pp (r + 1) = Pp r * Nn r) (hN : ∀ r < i.toNat, Nn r ≠ 0)
    (hPne : ∀ r < i.toNat, Pp r ≠ 0) (hinv : inv = (Pp i.toNat)⁻¹) :
    ∃ W', backward z0 n i inv (PackedRepr.encode W) h = PackedRepr.encode W' ∧ W'.size = W.size ∧
      (∀ r k, k < 4 → (r + n < i.toNat ∨ i.toNat ≤ r) → row W' r k = row W r k) ∧
      ∀ r < i.toNat, i.toNat ≤ r + n →
        row W' r 0 = (X r * (Nn r)⁻¹).val ∧
        row W' r 1 = (X r * (Nn r)⁻¹ * (z0 - X r)).val ∧
        row W' r 2 = (X r * (Nn r)⁻¹ * T2 r).val ∧
        row W' r 3 = (X r * (Nn r)⁻¹ * (z0 - X r) * T2 r).val := by
  induction n generalizing i inv W with
  | zero =>
    exact ⟨W, rfl, rfl, fun _ _ _ _ ↦ rfl, fun r hr hr' ↦ absurd hr' (by omega)⟩
  | succ n ih =>
    have hsize : (PackedRepr.encode W).size = 4 * W.size := PackedRepr.size_encode_uint32 W
    have hi : 1 ≤ i.toNat := by have := h.2.2; omega
    have hj : (i - 1).toNat = i.toNat - 1 := by
      rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; simp; omega)]; simp
    have hus : 4 * W.size < USize.size := by rw [← hsize]; exact h.2.1
    have h4 : (4 * (i - 1)).toNat = 4 * (i.toNat - 1) := by
      rw [usize_four_mul (i - 1) (PackedRepr.encode W).size (by rw [hsize, hj]; omega) h.2.1, hj]
    obtain ⟨hx, ht2, hn, hpre⟩ := hrows (i.toNat - 1) (by omega)
    have hrow : ∀ k, (4 * (i - 1)).toNat + (OfNat.ofNat k : USize).toNat = 4 * (i.toNat - 1) + k
        ∨ k ≥ 4 := by
      intro k
      by_cases hk : k < 4
      · left; rw [h4, Native.usize_numeral k (by omega)]
      · right; omega
    have hread : ∀ (k : ℕ) (hk : k < 4) (v : Field), row W (i.toNat - 1) k = v.val →
        ∀ hb, readField (PackedRepr.encode W) (4 * (i - 1)) (OfNat.ofNat k) hb = v := by
      intro k hk v hv hb
      rw [readField_pack, h4, Native.usize_numeral k (by omega)]
      change wordField (row W (i.toNat - 1) k) = v
      rw [hv, wordField_val]
    have hnp := inv_mul_prefix (Pp (i.toNat - 1)) (Nn (i.toNat - 1)) (hPne _ (by omega))
      (hN _ (by omega))
    have hinv' : inv = (Pp (i.toNat - 1) * Nn (i.toNat - 1))⁻¹ := by
      rw [hinv, ← hP _ (by omega), Nat.sub_add_cancel hi]
    rw [backward]
    simp only [hread 0 (by decide) _ hx, hread 1 (by decide) _ ht2, hread 2 (by decide) _ hn,
      hread 3 (by decide) _ hpre, hinv', hnp.1, hnp.2]
    have hj' : 4 * (i - 1).toNat + 4 ≤ W.size := by rw [hj]; omega
    simp only [storeRow W (i - 1) hj' hus, hj]
    have hj'' : 4 * (i.toNat - 1) + 4 ≤ W.size := by rw [← hj]; exact hj'
    have hW1 := row_setRow W (i.toNat - 1) (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹).val
      (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹ * (z0 - X (i.toNat - 1))).val
      (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹ * T2 (i.toNat - 1)).val
      (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹ * (z0 - X (i.toNat - 1)) * T2 (i.toNat - 1)).val hj''
    have hsz1 := size_setRow W (i.toNat - 1) (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹).val
      (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹ * (z0 - X (i.toNat - 1))).val
      (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹ * T2 (i.toNat - 1)).val
      (X (i.toNat - 1) * (Nn (i.toNat - 1))⁻¹ * (z0 - X (i.toNat - 1)) * T2 (i.toNat - 1)).val hj''
    obtain ⟨W', heq, hsz, hout, hrows'⟩ := ih (i - 1) (Pp (i.toNat - 1))⁻¹ _
      (by rw [PackedRepr.size_encode_uint32, hsz1, hj]
          exact ⟨by omega, by omega, by have := h.2.2; omega⟩)
      (by rw [hsz1, hj]; omega)
      (fun r hr ↦ by
        rw [hj] at hr
        rw [row_setRow_ne W _ _ _ _ _ hj'' r 0 (by omega) (by omega),
          row_setRow_ne W _ _ _ _ _ hj'' r 1 (by omega) (by omega),
          row_setRow_ne W _ _ _ _ _ hj'' r 2 (by omega) (by omega),
          row_setRow_ne W _ _ _ _ _ hj'' r 3 (by omega) (by omega)]
        exact hrows r (by omega))
      (fun r hr ↦ hP r (by rw [hj] at hr; omega)) (fun r hr ↦ hN r (by rw [hj] at hr; omega))
      (fun r hr ↦ hPne r (by rw [hj] at hr; omega)) (by rw [hj])
    refine ⟨W', heq, by rw [hsz, hsz1], fun r k hk hr ↦ ?_, fun r hr hr' ↦ ?_⟩
    · rw [hout r k hk (by rw [hj]; omega), row_setRow_ne W _ _ _ _ _ hj'' r k hk (by omega)]
    · by_cases hr1 : r = i.toNat - 1
      · subst hr1
        have hl : (i - 1).toNat ≤ i.toNat - 1 := by rw [hj]
        rw [hout _ 0 (by omega) (Or.inr hl), hout _ 1 (by omega) (Or.inr hl),
          hout _ 2 (by omega) (Or.inr hl), hout _ 3 (by omega) (Or.inr hl)]
        exact hW1
      · exact hrows' r (by rw [hj]; omega) (by rw [hj]; omega)

/-! ### Column sums -/

/-- Term `r` of a column sum: the residue of evaluation word `e + r · width` times coordinate `k`
of row `r`'s weights. -/
def dotTerm (evals buf : ByteArray) (e width w r k : ℕ) : KoalaBear.Field :=
  FastField.toField (ofWordMod (evals.getUInt32LE! (4 * (e + r * width))) : Field) *
    FastField.toField (wordField (buf.getUInt32LE! (4 * (w + 4 * r + k))))

theorem dot1_spec (evals buf : ByteArray) (width : USize) (n : ℕ) (e w : USize)
    (a0 a1 a2 a3 : Acc) (h) :
    FastField.toField (dot1 evals buf width n e w a0 a1 a2 a3 h).s0 =
        a0.value + ∑ r ∈ Finset.range n, dotTerm evals buf e.toNat width.toNat w.toNat r 0 ∧
      FastField.toField (dot1 evals buf width n e w a0 a1 a2 a3 h).s1 =
        a1.value + ∑ r ∈ Finset.range n, dotTerm evals buf e.toNat width.toNat w.toNat r 1 ∧
      FastField.toField (dot1 evals buf width n e w a0 a1 a2 a3 h).s2 =
        a2.value + ∑ r ∈ Finset.range n, dotTerm evals buf e.toNat width.toNat w.toNat r 2 ∧
      FastField.toField (dot1 evals buf width n e w a0 a1 a2 a3 h).s3 =
        a3.value + ∑ r ∈ Finset.range n, dotTerm evals buf e.toNat width.toNat w.toNat r 3 := by
  induction n generalizing e w a0 a1 a2 a3 with
  | zero =>
    simp only [dot1, LazyAcc.toField_result, Finset.range_zero, Finset.sum_empty, add_zero,
      and_self]
  | succ n ih =>
    have hw4 : (w + 4).toNat = w.toNat + 4 := by
      have := h.2.2.1; have := h.2.2.2
      rw [usize_add_lt _ _ (by rw [Native.usize_numeral 4 (by decide)]; omega),
        Native.usize_numeral 4 (by decide)]
    have hterm : ∀ k, ∀ r < n, dotTerm evals buf (e + width).toNat width.toNat (w + 4).toNat r k =
        dotTerm evals buf e.toNat width.toNat w.toNat (r + 1) k := by
      intro k r hr
      have h1 := h.1 1 (by omega)
      have := h.2.1
      rw [Nat.one_mul] at h1
      simp only [dotTerm, usize_add_lt e width (by omega), hw4]
      congr 4 <;> ring
    rw [dot1]
    simp only [readUOffset_eq, readField, Native.usize_numeral 0 (by decide),
      Native.usize_numeral 1 (by decide), Native.usize_numeral 2 (by decide),
      Native.usize_numeral 3 (by decide)]
    obtain ⟨i0, i1, i2, i3⟩ := ih (e + width) (w + 4) _ _ _ _ _
    rw [i0, i1, i2, i3]
    simp only [LazyAcc.value_add, Finset.sum_range_succ']
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [Finset.sum_congr rfl fun r hr ↦ hterm _ r (Finset.mem_range.mp hr)]
      simp only [dotTerm, Nat.zero_mul, Nat.add_zero, Nat.mul_zero]
      ring

/-- `dot1`'s range condition. -/
abbrev Dot1Fits (evals buf : ByteArray) (width : USize) (n : ℕ) (e w : USize) : Prop :=
  (∀ r < n, 4 * (e.toNat + r * width.toNat) + 3 < evals.size) ∧ evals.size < USize.size ∧
    4 * (w.toNat + 4 * n) ≤ buf.size ∧ buf.size < USize.size

theorem dot4_fits {evals buf : ByteArray} {width : USize} {n : ℕ} {e w : USize}
    (h : (∀ r < n, 4 * (e.toNat + r * width.toNat + 3) + 3 < evals.size) ∧
      evals.size < USize.size ∧ 4 * (w.toNat + 4 * n) ≤ buf.size ∧ buf.size < USize.size)
    (c : ℕ) (hc : c < 4) : Dot1Fits evals buf width n (e + OfNat.ofNat c) w := by
  refine ⟨fun r hr ↦ ?_, h.2⟩
  have := h.1 r hr
  have := h.2.1
  rw [usize_add_lt _ _ (by rw [Native.usize_numeral c (by omega)]; nlinarith),
    Native.usize_numeral c (by omega)]
  omega

theorem dot4_fits0 {evals buf : ByteArray} {width : USize} {n : ℕ} {e w : USize}
    (h : (∀ r < n, 4 * (e.toNat + r * width.toNat + 3) + 3 < evals.size) ∧
      evals.size < USize.size ∧ 4 * (w.toNat + 4 * n) ≤ buf.size ∧ buf.size < USize.size) :
    Dot1Fits evals buf width n e w :=
  ⟨fun r hr ↦ by have := h.1 r hr; omega, h.2⟩

/-- Four adjacent columns at once are four single columns. -/
theorem dot4_eq (evals buf : ByteArray) (width : USize) (n : ℕ) (e w : USize)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Acc) (h) :
    dot4 evals buf width n e w a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 h =
      (dot1 evals buf width n e w a0 a1 a2 a3 (dot4_fits0 h),
        dot1 evals buf width n (e + 1) w b0 b1 b2 b3 (dot4_fits h 1 (by decide)),
        dot1 evals buf width n (e + 2) w c0 c1 c2 c3 (dot4_fits h 2 (by decide)),
        dot1 evals buf width n (e + 3) w d0 d1 d2 d3 (dot4_fits h 3 (by decide))) := by
  induction n generalizing e w a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 with
  | zero => rfl
  | succ n ih =>
    have he := h.1 0 (by omega)
    have hes := h.2.1
    simp only [Nat.zero_mul, Nat.add_zero] at he
    have hc : ∀ c < 4, (e + OfNat.ofNat c).toNat = e.toNat + c := fun c hc ↦ by
      rw [usize_add_lt _ _ (by rw [Native.usize_numeral c (by omega)]; omega),
        Native.usize_numeral c (by omega)]
    simp only [dot4, dot1]
    simp only [readUOffset_eq, Native.usize_numeral 0 (by decide),
      Native.usize_numeral 1 (by decide), Native.usize_numeral 2 (by decide),
      Native.usize_numeral 3 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
      Nat.add_zero]
    rw [ih]
    simp only [USize.add_assoc, USize.add_comm width]

/-- Rows `0, …, b - 1` of `buf` hold weights whose column sums are `wt r`. -/
def WeightsAt (buf : ByteArray) (z : Ext4) (wt : ℕ → KoalaBear.Ext4) (b : ℕ) : Prop :=
  ∀ r < b, Ext4.toSpec (Quad.combine z ⟨wordField (buf.getUInt32LE! (4 * (4 * r))),
    wordField (buf.getUInt32LE! (4 * (4 * r + 1))), wordField (buf.getUInt32LE! (4 * (4 * r + 2))),
    wordField (buf.getUInt32LE! (4 * (4 * r + 3)))⟩) = wt r

/-- The block's sum of column `c`. -/
def colBlock (evals : ByteArray) (width row b c : ℕ) (wt : ℕ → KoalaBear.Ext4) :
    KoalaBear.Ext4 :=
  ∑ r ∈ Finset.range b,
    FastField.toField (ofWordMod (evals.getUInt32LE! (4 * ((row + r) * width + c))) : Field) • wt r

/-- A column's sums give the column's block sum. -/
theorem toSpec_combine_dot1 (evals buf : ByteArray) (z : Ext4) (wt : ℕ → KoalaBear.Ext4)
    (width row b c : ℕ) (hw : WeightsAt buf z wt b)
    (hi : b = 0 ∨ width.toUSize.toNat = width ∧ (row * width + c).toUSize.toNat = row * width + c)
    (h) :
    Ext4.toSpec ((dot1 evals buf width.toUSize b (row * width + c).toUSize 0 LazyAcc.zero
      LazyAcc.zero LazyAcc.zero LazyAcc.zero h).combine z) = colBlock evals width row b c wt := by
  obtain ⟨d0, d1, d2, d3⟩ := dot1_spec evals buf width.toUSize b (row * width + c).toUSize 0
    LazyAcc.zero LazyAcc.zero LazyAcc.zero LazyAcc.zero h
  rw [Quad.toSpec_combine, d0, d1, d2, d3]
  rcases hi with rfl | ⟨hwt, he⟩
  · simp only [Finset.range_zero, Finset.sum_empty, LazyAcc.value_zero, add_zero, zero_smul,
      colBlock]
  simp only [LazyAcc.value_zero, zero_add, colBlock, dotTerm, he, hwt, USize.toNat_zero]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun r hr ↦ by rw [← hw r (Finset.mem_range.mp hr)])
  simp only [Quad.toSpec_combine, Finset.sum_smul, smul_add, smul_smul, ← Finset.sum_add_distrib,
    Nat.add_zero]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [show row * width + c + r * width = (row + r) * width + c by ring]

theorem blockFits_index {evals buf : ByteArray} {width row b : ℕ}
    (h : BlockFits evals buf width row b) (c : ℕ) (hc : c < width) :
    b = 0 ∨ width.toUSize.toNat = width ∧ (row * width + c).toUSize.toNat = row * width + c := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · exact Or.inl hb
  · right
    have hd := dot_bound row b width c 0 0 hb (by omega)
    have := h.1; have := h.2.1
    simp only [Nat.zero_mul, Nat.add_zero] at hd
    have hw : width ≤ (row + b) * width := Nat.le_mul_of_pos_left _ (by omega)
    exact ⟨toUSize_toNat_of_lt _ ((row + b) * width + 1) (by omega) (by omega),
      toUSize_toNat_of_lt _ ((row + b) * width) hd (by omega)⟩

/-- The spec value of column `c` of a sums array. -/
def sumAt (z : Ext4) (sums : Array Quad) (c : ℕ) : KoalaBear.Ext4 :=
  Ext4.toSpec ((sums.getD c 0).combine z)

theorem sumAt_modify (z : Ext4) (sums : Array Quad) (c : ℕ) (hc : c < sums.size) (q : Quad)
    (c' : ℕ) :
    sumAt z (sums.modify c (· + q)) c' =
      sumAt z sums c' + if c = c' then Ext4.toSpec (q.combine z) else 0 := by
  simp only [sumAt, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  split
  · subst c'
    rw [Array.getElem?_eq_getElem hc, Option.map_some, Option.getD_some, Option.getD_some,
      Quad.toSpec_combine_add]
  · rw [add_zero]

theorem toUSize_add_numeral (a j : ℕ) : a.toUSize + (OfNat.ofNat j : USize) = (a + j).toUSize :=
  (USize.ofNat_add a j).symm

theorem addColumn_spec (evals buf : ByteArray) (z : Ext4) (wt : ℕ → KoalaBear.Ext4)
    (width row b : ℕ) (hfit : BlockFits evals buf width row b) (hw : WeightsAt buf z wt b)
    (c : ℕ) (hc : c + 1 ≤ width) (sums : Array Quad) :
    (addColumn evals buf width row b hfit c hc sums).size = sums.size ∧
      ∀ c', c < sums.size → sumAt z (addColumn evals buf width row b hfit c hc sums) c' =
        sumAt z sums c' + if c = c' then colBlock evals width row b c wt else 0 := by
  refine ⟨Array.size_modify, fun c' hcs ↦ ?_⟩
  rw [addColumn, sumAt_modify z sums c hcs,
    toSpec_combine_dot1 evals buf z wt width row b c hw (blockFits_index hfit c (by omega))]

theorem addColumns4_spec (evals buf : ByteArray) (z : Ext4) (wt : ℕ → KoalaBear.Ext4)
    (width row b : ℕ) (hfit : BlockFits evals buf width row b) (hw : WeightsAt buf z wt b)
    (c : ℕ) (hc : c + 4 ≤ width) (sums : Array Quad) (hcs : c + 4 ≤ sums.size) :
    (addColumns4 evals buf width row b hfit c hc sums).size = sums.size ∧
      ∀ c', sumAt z (addColumns4 evals buf width row b hfit c hc sums) c' =
        sumAt z sums c' + if c ≤ c' ∧ c' < c + 4 then colBlock evals width row b c' wt else 0 := by
  refine ⟨by simp only [addColumns4, Array.size_modify], fun c' ↦ ?_⟩
  have hcol : ∀ j, j < 4 → ∀ hj, Ext4.toSpec ((dot1 evals buf width.toUSize b
      ((row * width + c).toUSize + OfNat.ofNat j) 0 LazyAcc.zero LazyAcc.zero LazyAcc.zero
      LazyAcc.zero hj).combine z) = colBlock evals width row b (c + j) wt := by
    intro j hj hj'
    simp only [toUSize_add_numeral, Nat.add_assoc] at hj' ⊢
    exact toSpec_combine_dot1 evals buf z wt width row b (c + j) hw
      (blockFits_index hfit (c + j) (by omega)) hj'
  have hcol0 : ∀ hj, Ext4.toSpec ((dot1 evals buf width.toUSize b (row * width + c).toUSize 0
      LazyAcc.zero LazyAcc.zero LazyAcc.zero LazyAcc.zero hj).combine z) =
      colBlock evals width row b c wt := fun hj ↦
    toSpec_combine_dot1 evals buf z wt width row b c hw (blockFits_index hfit c (by omega)) hj
  simp only [addColumns4, dot4_eq]
  rw [sumAt_modify z _ _ (by simp only [Array.size_modify]; omega),
    sumAt_modify z _ _ (by simp only [Array.size_modify]; omega),
    sumAt_modify z _ _ (by simp only [Array.size_modify]; omega),
    sumAt_modify z _ _ (by omega), hcol0, hcol 1 (by decide), hcol 2 (by decide),
    hcol 3 (by decide)]
  by_cases h0 : c = c'
  · subst h0; simp [show c ≤ c ∧ c < c + 4 by omega]
  by_cases h1 : c + 1 = c'
  · subst h1; simp [show c ≤ c + 1 ∧ c + 1 < c + 4 by omega]
  by_cases h2 : c + 2 = c'
  · subst h2; simp [show c ≤ c + 2 ∧ c + 2 < c + 4 by omega]
  by_cases h3 : c + 3 = c'
  · subst h3; simp [show c ≤ c + 3 ∧ c + 3 < c + 4 by omega]
  simp only [h0, h1, h2, h3, ↓reduceIte, add_zero, show ¬(c ≤ c' ∧ c' < c + 4) by omega]

theorem columns1_spec (evals buf : ByteArray) (z : Ext4) (wt : ℕ → KoalaBear.Ext4)
    (width row b : ℕ) (hfit : BlockFits evals buf width row b) (hw : WeightsAt buf z wt b)
    (k c : ℕ) (hc : c + k ≤ width) (sums : Array Quad) (hs : sums.size = width) :
    (columns1 evals buf width row b hfit k c hc sums).size = width ∧
      ∀ c', sumAt z (columns1 evals buf width row b hfit k c hc sums) c' =
        sumAt z sums c' + if c ≤ c' ∧ c' < c + k then colBlock evals width row b c' wt else 0 := by
  induction k generalizing c sums with
  | zero =>
    refine ⟨hs, fun c' ↦ ?_⟩
    simp only [columns1]
    split_ifs
    · omega
    · rw [add_zero]
  | succ k ih =>
    obtain ⟨hs1, hv1⟩ := addColumn_spec evals buf z wt width row b hfit hw c (by omega) sums
    obtain ⟨hsz, hval⟩ := ih (c + 1) (by omega)
      (addColumn evals buf width row b hfit c (by omega) sums) (by rw [hs1, hs])
    refine ⟨hsz, fun c' ↦ ?_⟩
    rw [columns1, hval, hv1 c' (by omega)]
    by_cases h1 : c = c'
    · subst h1
      simp only [↓reduceIte, show ¬(c + 1 ≤ c ∧ c < c + 1 + k) by omega,
        show c ≤ c ∧ c < c + (k + 1) by omega, add_zero, and_self]
    · simp only [h1, ↓reduceIte, add_zero]
      congr 1
      split_ifs <;> first | rfl | omega

theorem columns4_spec (evals buf : ByteArray) (z : Ext4) (wt : ℕ → KoalaBear.Ext4)
    (width row b : ℕ) (hfit : BlockFits evals buf width row b) (hw : WeightsAt buf z wt b)
    (g c : ℕ) (hc : c + 4 * g ≤ width) (sums : Array Quad) (hs : sums.size = width) :
    (columns4 evals buf width row b hfit g c hc sums).size = width ∧
      ∀ c', sumAt z (columns4 evals buf width row b hfit g c hc sums) c' =
        sumAt z sums c' +
          if c ≤ c' ∧ c' < c + 4 * g then colBlock evals width row b c' wt else 0 := by
  induction g generalizing c sums with
  | zero =>
    refine ⟨hs, fun c' ↦ ?_⟩
    simp only [columns4]
    split_ifs
    · omega
    · rw [add_zero]
  | succ g ih =>
    obtain ⟨hs1, hv1⟩ := addColumns4_spec evals buf z wt width row b hfit hw c (by omega) sums
      (by omega)
    obtain ⟨hsz, hval⟩ := ih (c + 4) (by omega)
      (addColumns4 evals buf width row b hfit c (by omega) sums) (by rw [hs1, hs])
    refine ⟨hsz, fun c' ↦ ?_⟩
    rw [columns4, hval, hv1 c']
    rw [add_assoc]
    congr 1
    split_ifs <;> first | rfl | (exfalso; omega) | simp only [add_zero, zero_add]

/-! ### Blocks -/

theorem toField_nodeAt (ω x : Field) (r : ℕ) :
    FastField.toField (nodeAt ω x r) = FastField.toField x * FastField.toField ω ^ r := by
  induction r generalizing x with
  | zero => rw [nodeAt, pow_zero, mul_one]
  | succ r ih => rw [nodeAt, ih, toField_mul, pow_succ', mul_assoc]

theorem nodeAt_succ (ω x : Field) (r : ℕ) : nodeAt ω x (r + 1) = nodeAt ω x r * ω := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih => rw [nodeAt, ih, ← nodeAt]

theorem normPrefix_succ (ω z0 k0 k1 z2x2 x acc : Field) (r : ℕ) :
    normPrefix ω z0 k0 k1 z2x2 x acc (r + 1) =
      normPrefix ω z0 k0 k1 z2x2 x acc r * rowNorm z0 k0 k1 z2x2 (nodeAt ω x r) := by
  induction r generalizing x acc with
  | zero => rfl
  | succ r ih => rw [normPrefix, ih, ← normPrefix, nodeAt]

/-- Off the coset, the norm of `z - x` is a unit. -/
theorem rowNorm_ne_zero (z : Ext4) (x : Field)
    (hz : Ext4.toSpec z ≠ Ext.ofBase (FastField.toField x)) :
    rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) x ≠ 0 := by
  rw [rowNorm, ← Ext4.norm_sub_ofBase]
  intro h
  have ha : Ext4.toSpec (z - Ext4.ofBase x) ≠ 0 := by
    rw [Ext4.toSpec_sub, Ext4.toSpec_ofBase, sub_ne_zero]; exact hz
  apply Ext4.norm_ne_zero _ ha
  rw [← Ext4.toField_g0, ← Ext4.toField_g1]
  have := congrArg FastField.toField h
  rw [Ext4.toField_norm, toField_zero] at this
  rw [← this]

/-- The weight `x / (z - x)` in the spec field. -/
def specWeight (z : Ext4) (x : KoalaBear.Field) : KoalaBear.Ext4 :=
  Ext.ofBase x * (Ext4.toSpec z - Ext.ofBase x)⁻¹

theorem toSpec_weight (z : Ext4) (x : Field) :
    Ext4.toSpec (Ext4.smul x (z - Ext4.ofBase x)⁻¹) = specWeight z (FastField.toField x) := by
  rw [Ext4.toSpec_smul, Ext4.toSpec_inv, Ext4.toSpec_sub, Ext4.toSpec_ofBase, Algebra.smul_def,
    Ext.algebraMap_eq_ofBase, specWeight]

/-- Term `R` of column `c`: the residue of its word times the weight of node `s ω^R`. -/
def rowTerm (evals : ByteArray) (width : ℕ) (ω s : Field) (z : Ext4) (R c : ℕ) :
    KoalaBear.Ext4 :=
  FastField.toField (ofWordMod (evals.getUInt32LE! (4 * (R * width + c))) : Field) •
    specWeight z (FastField.toField s * FastField.toField ω ^ R)

theorem ne_zero_iff_toField (a : Field) : a ≠ 0 ↔ FastField.toField a ≠ 0 := by
  constructor
  · intro h h'; exact h (toField_injective (by rw [h', toField_zero]))
  · intro h h'; exact h (by rw [h', toField_zero])

/-- The weights a block's two passes leave in its buffer. -/
theorem weightsAt_passes (z : Ext4) (ω x : Field) (b : ℕ) (W2 : Array UInt32)
    (hrows : ∀ r < b,
      row W2 r 0 = (nodeAt ω x r * (rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
        (nodeAt ω x r))⁻¹).val ∧
      row W2 r 1 = (nodeAt ω x r * (rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
        (nodeAt ω x r))⁻¹ * (z.c0 - nodeAt ω x r)).val ∧
      row W2 r 2 = (nodeAt ω x r * (rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
        (nodeAt ω x r))⁻¹ * ((z.c0 - nodeAt ω x r) * (z.c0 - nodeAt ω x r))).val ∧
      row W2 r 3 = (nodeAt ω x r * (rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
        (nodeAt ω x r))⁻¹ * (z.c0 - nodeAt ω x r) *
          ((z.c0 - nodeAt ω x r) * (z.c0 - nodeAt ω x r))).val) :
    WeightsAt (PackedRepr.encode W2) z
      (fun r ↦ specWeight z (FastField.toField (nodeAt ω x r))) b := by
  intro r hr
  obtain ⟨h0, h1, h2, h3⟩ := hrows r hr
  simp only [PackedRepr.getUInt32LE!_encode]
  rw [show W2.getD (4 * r) 0 = row W2 r 0 from rfl,
    show W2.getD (4 * r + 1) 0 = row W2 r 1 from rfl,
    show W2.getD (4 * r + 2) 0 = row W2 r 2 from rfl,
    show W2.getD (4 * r + 3) 0 = row W2 r 3 from rfl, h0, h1, h2, h3, wordField_val, wordField_val,
    wordField_val, wordField_val, ← toSpec_weight, Ext4.smul_inv_sub_ofBase]
  rfl

theorem blocks_spec (evals : ByteArray) (ω s : Field) (z : Ext4) (width hi k row : ℕ) (x : Field)
    (W : Array UInt32) (sums : Array Quad) (h) (hW : W.size = 4 * blockRows)
    (hx : FastField.toField x = FastField.toField s * FastField.toField ω ^ row)
    (hs : sums.size = width)
    (hz : ∀ R, row ≤ R → R < hi →
      Ext4.toSpec z ≠ Ext.ofBase (FastField.toField s * FastField.toField ω ^ R)) :
    (blocks evals ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) width hi k row x
        (PackedRepr.encode W) sums h).size = width ∧
      ∀ c < width, sumAt z (blocks evals ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
          width hi k row x (PackedRepr.encode W) sums h) c =
        sumAt z sums c + ∑ R ∈ Finset.Ico row (min hi (row + k * blockRows)),
          rowTerm evals width ω s z R c := by
  induction k generalizing row x W sums with
  | zero =>
    refine ⟨hs, fun c _ ↦ ?_⟩
    rw [blocks, Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  | succ k ih =>
    obtain ⟨b, hb⟩ : ∃ b, b = min blockRows (hi - row) := ⟨_, rfl⟩
    have hbB : b ≤ blockRows := hb ▸ Nat.min_le_left _ _
    have hrb : row + b ≤ hi := by have := Nat.min_le_right blockRows (hi - row); have := h.1; omega
    have hus := USize.le_size
    have hbt : b.toUSize.toNat = b := toUSize_toNat_of_lt b (blockRows + 1) (by
      omega) (by simp only [blockRows]; omega)
    have hWs : 4 * W.size < USize.size := by rw [hW]; simp only [blockRows]; omega
    obtain ⟨W1, eq1, hs1, -, rows1⟩ := forward_spec ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z)
      (z.c2 + z.c2) b 0 x 1 W (by rw [USize.toNat_zero, hW]; omega) hWs
    have hX : ∀ r, FastField.toField (nodeAt ω x r) =
        FastField.toField s * FastField.toField ω ^ (row + r) := by
      intro r; rw [toField_nodeAt, hx, pow_add, mul_assoc]
    have hN : ∀ r < b, rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
        (nodeAt ω x r) ≠ 0 := fun r hr ↦
      rowNorm_ne_zero z _ (by rw [hX]; exact hz _ (by omega) (by omega))
    have hPne : ∀ r ≤ b,
        normPrefix ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) x 1 r ≠ 0 := by
      intro r hr
      induction r with
      | zero => rw [normPrefix, ne_zero_iff_toField, toField_one]; exact one_ne_zero
      | succ r ihr =>
        rw [normPrefix_succ, ne_zero_iff_toField, toField_mul]
        exact mul_ne_zero ((ne_zero_iff_toField _).mp (ihr (by omega)))
          ((ne_zero_iff_toField _).mp (hN r (by omega)))
    obtain ⟨W2, eq2, hs2, -, rows2⟩ := backward_spec z.c0 (nodeAt ω x)
      (fun r ↦ (z.c0 - nodeAt ω x r) * (z.c0 - nodeAt ω x r))
      (fun r ↦ rowNorm z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) (nodeAt ω x r))
      (normPrefix ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) x 1) b b.toUSize
      (normPrefix ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) x 1 b)⁻¹ W1
      (by rw [PackedRepr.size_encode_uint32, hs1, hW, hbt]; simp only [blockRows] at hbB ⊢
          exact ⟨by omega, by omega, le_refl _⟩)
      (by rw [hs1, hW, hbt]; simp only [blockRows] at hbB ⊢; omega)
      (fun r hr ↦ by
        rw [hbt] at hr
        have := rows1 r hr
        simp only [USize.toNat_zero, Nat.zero_add] at this
        exact this)
      (fun r _ ↦ normPrefix_succ _ _ _ _ _ _ _ r) (fun r hr ↦ hN r (by omega))
      (fun r hr ↦ hPne r (by omega)) (by rw [hbt])
    have hw := weightsAt_passes z ω x b W2 (fun r hr ↦ by
      have := rows2 r (by omega) (by omega)
      exact this)
    have hfit : BlockFits evals (PackedRepr.encode W2) width row b := by
      have := Nat.mul_le_mul_right width hrb
      refine ⟨by omega, h.2.2.1, ?_, ?_⟩ <;> rw [PackedRepr.size_encode_uint32, hs2, hs1, hW] <;>
        simp only [blockRows] at hbB ⊢ <;> omega
    have hcol : ∀ c, colBlock evals width row b c
        (fun r ↦ specWeight z (FastField.toField (nodeAt ω x r))) =
        ∑ R ∈ Finset.Ico row (row + b), rowTerm evals width ω s z R c := by
      intro c
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, colBlock]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [rowTerm, hX]
    have key : ∀ (S : Array Quad) (hS : S.size = width)
        (_ : ∀ c < width, sumAt z S c = sumAt z sums c + colBlock evals width row b c
          (fun r ↦ specWeight z (FastField.toField (nodeAt ω x r)))) (h''),
        (blocks evals ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2) width hi k (row + b)
          (nodeAt ω x b) (PackedRepr.encode W2) S h'').size = width ∧
        ∀ c < width, sumAt z (blocks evals ω z.c0 (Ext4.normK0 z) (Ext4.normK1 z) (z.c2 + z.c2)
            width hi k (row + b) (nodeAt ω x b) (PackedRepr.encode W2) S h'') c =
          sumAt z sums c + ∑ R ∈ Finset.Ico row (min hi (row + (k + 1) * blockRows)),
            rowTerm evals width ω s z R c := by
      intro S hS hv h''
      obtain ⟨hsz, hval⟩ := ih (row + b) (nodeAt ω x b) W2 S h'' (by rw [hs2, hs1, hW])
        (by rw [hX]) hS (fun R h1 h2 ↦ hz R (by omega) h2)
      refine ⟨hsz, fun c hc ↦ ?_⟩
      rw [hval c hc, hv c hc, add_assoc, hcol,
        Finset.sum_Ico_consecutive _ (by omega) (by omega)]
      congr 3
      simp only [blockRows] at hb ⊢
      omega
    rw [blocks]
    simp only [← hb, eq1, eq2]
    have h4 := columns4_spec evals _ z _ width row b hfit hw (width / 4) 0 (by omega) sums hs
    have h1 := columns1_spec evals _ z _ width row b hfit hw (width % 4) (4 * (width / 4))
      (by omega) _ h4.1
    refine key _ h1.1 (fun c hc ↦ ?_) _
    rw [h1.2 c, h4.2 c]
    split_ifs <;> first | omega | simp only [add_zero]

/-! ### Leaves and tasks -/

theorem sumAt_replicate_zero (z : Ext4) (width c : ℕ) :
    sumAt z (Array.replicate width 0) c = 0 := by
  simp only [sumAt, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp only [Option.getD_some, Option.getD_none, Quad.toSpec_combine_zero]

theorem leaf_spec (evals : ByteArray) (ω s : Field) (z : Ext4) (width lo hi : ℕ) (h)
    (hz : ∀ R, lo ≤ R → R < hi →
      Ext4.toSpec z ≠ Ext.ofBase (FastField.toField s * FastField.toField ω ^ R)) :
    (leaf evals ω s z width lo hi h).size = width ∧
      ∀ c < width, sumAt z (leaf evals ω s z width lo hi h) c =
        ∑ R ∈ Finset.Ico lo hi, rowTerm evals width ω s z R c := by
  have hpack : ByteArray.mk (Array.replicate (16 * blockRows) 0) =
      PackedRepr.encode (Array.replicate (4 * blockRows) (0 : UInt32)) := by
    rw [← Native.zeroBuffer_eq_encodeWords, ← Nat.mul_assoc]
  have hmin : min hi (lo + (hi - lo + blockRows - 1) / blockRows * blockRows) = hi := by
    simp only [blockRows]; have := h.1; omega
  unfold leaf
  simp only [hpack]
  obtain ⟨hsz, hval⟩ := blocks_spec evals ω s z width hi ((hi - lo + blockRows - 1) / blockRows) lo
    (s * Montgomery.Native32.pow ω lo) (Array.replicate (4 * blockRows) 0)
    (Array.replicate width 0)
    ⟨h.1, h.2.1, h.2.2, by rw [PackedRepr.size_encode_uint32, Array.size_replicate]; ring⟩
    (Array.size_replicate) (by rw [toField_mul, toField_pow]) Array.size_replicate hz
  refine ⟨hsz, fun c hc ↦ ?_⟩
  rw [hval c hc, sumAt_replicate_zero, zero_add, hmin]

theorem sumAt_join (z : Ext4) (a b : Array Quad) (c : ℕ) (ha : c < a.size) (hb : c < b.size) :
    sumAt z (Array.zipWith (· + ·) a b) c = sumAt z a c + sumAt z b c := by
  simp only [sumAt, Array.getD_eq_getD_getElem?, Array.getElem?_zipWith,
    Array.getElem?_eq_getElem ha, Array.getElem?_eq_getElem hb,
    Option.getD_some, Quad.toSpec_combine_add]

theorem tree_spec (evals : ByteArray) (ω s : Field) (z : Ext4) (width depth lo hi : ℕ) (h)
    (hz : ∀ R, lo ≤ R → R < hi →
      Ext4.toSpec z ≠ Ext.ofBase (FastField.toField s * FastField.toField ω ^ R)) :
    (tree evals ω s z width lo hi h depth).size = width ∧
      ∀ c < width, sumAt z (tree evals ω s z width lo hi h depth) c =
        ∑ R ∈ Finset.Ico lo hi, rowTerm evals width ω s z R c := by
  induction depth generalizing lo hi with
  | zero => exact leaf_spec evals ω s z width lo hi h hz
  | succ depth ih =>
    have hm : lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 ≤ hi := by have := h.1; omega
    obtain ⟨hs1, hv1⟩ := ih lo (lo + (hi - lo) / 2) ⟨hm.1, by
      have := Nat.mul_le_mul_right width hm.2; omega, h.2.2⟩ (fun R h1 h2 ↦ hz R h1 (by omega))
    obtain ⟨hs2, hv2⟩ := ih (lo + (hi - lo) / 2) hi ⟨hm.2, h.2⟩ (fun R h1 h2 ↦ hz R (by omega) h2)
    simp only [tree, join, Task.spawn]
    refine ⟨by rw [Array.size_zipWith, hs1, hs2, Nat.min_self], fun c hc ↦ ?_⟩
    rw [sumAt_join z _ _ c (by rw [hs1]; exact hc) (by rw [hs2]; exact hc), hv1 c hc, hv2 c hc,
      Finset.sum_Ico_consecutive _ hm.1 hm.2]

end InterpolatePacked

open InterpolatePacked

theorem getD_decodeWords (b : ByteArray) (k : ℕ) (hk : k < b.size / 4) :
    (decodeWords b).getD k 0 = ofWordMod (b.getUInt32LE! (4 * k)) := by
  rw [decodeWords, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hk, ↓reduceDIte, Option.getD_some]

/-- **Correctness of `interpolateCosetPacked`.** For a point off the coset, it computes
`interpolateCoset` on the matrix's words, read as residues. -/
theorem interpolateCosetPacked_eq (logN : ℕ) (ω s : Field) (width : ℕ) (evals : ByteArray)
    (z : Ext4) (logTasks : ℕ)
    (hz : ∀ i < 2 ^ logN, Ext4.toSpec z ≠ Ext.ofBase (specNode ω s i)) :
    interpolateCosetPacked logN ω s width evals z logTasks =
      interpolateCoset logN ω s width (decodeWords evals) z := by
  unfold interpolateCosetPacked
  split
  · rename_i h
    obtain ⟨hsz, hval⟩ := tree_spec evals ω s z width (min logTasks (logN - 9)) 0 (2 ^ logN)
      ⟨Nat.zero_le _, h.1.ge, h.2⟩ (fun R _ hR ↦ hz R hR)
    apply Array.ext
    · rw [Array.size_map, hsz, size_interpolateCoset]
    · intro j hj1 hj2
      have hj : j < width := by rw [Array.size_map, hsz] at hj1; exact hj1
      apply Ext4.toSpec_injective
      rw [Array.getElem_map, Ext4.toSpec_mul,
        toSpec_getElem_interpolateCoset logN ω s width _ z hz j hj]
      congr 1
      have hs : Ext4.toSpec (Quad.combine z (tree evals ω s z width 0 (2 ^ logN)
          ⟨Nat.zero_le _, h.1.ge, h.2⟩ (min logTasks (logN - 9)))[j]) =
          sumAt z (tree evals ω s z width 0 (2 ^ logN) ⟨Nat.zero_le _, h.1.ge, h.2⟩
            (min logTasks (logN - 9))) j := by
        rw [sumAt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem, Option.getD_some]
      rw [hs, hval j hj, Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun R hR ↦ ?_
      have hR' := (Finset.mem_Ico.mp hR).2
      have hk : R * width + j < evals.size / 4 := by
        rw [h.1, Nat.mul_div_cancel_left _ (by decide)]
        have := Nat.mul_le_mul_right width (show R + 1 ≤ 2 ^ logN from hR')
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      rw [rowTerm, getD_decodeWords evals _ hk]
      rfl
  · rfl

theorem size_columns1 (evals buf : ByteArray) (width row b : ℕ) (hfit) (k c : ℕ) (hc)
    (sums : Array Quad) : (columns1 evals buf width row b hfit k c hc sums).size = sums.size := by
  induction k generalizing c sums with
  | zero => rfl
  | succ k ih => rw [columns1, ih, addColumn, Array.size_modify]

theorem size_columns4 (evals buf : ByteArray) (width row b : ℕ) (hfit) (g c : ℕ) (hc)
    (sums : Array Quad) : (columns4 evals buf width row b hfit g c hc sums).size = sums.size := by
  induction g generalizing c sums with
  | zero => rfl
  | succ g ih => simp only [columns4, ih, addColumns4, Array.size_modify]

theorem size_blocks (evals : ByteArray) (ω z0 k0 k1 z2x2 : Field) (width hi k row : ℕ)
    (x : Field) (buf : ByteArray) (sums : Array Quad) (h) :
    (blocks evals ω z0 k0 k1 z2x2 width hi k row x buf sums h).size = sums.size := by
  induction k generalizing row x buf sums with
  | zero => rfl
  | succ k ih => simp only [blocks, ih, size_columns1, size_columns4]

theorem size_tree (evals : ByteArray) (ω s : Field) (z : Ext4) (width lo hi : ℕ) (h)
    (depth : ℕ) : (tree evals ω s z width lo hi h depth).size = width := by
  induction depth generalizing lo hi with
  | zero => simp only [tree, leaf, size_blocks, Array.size_replicate]
  | succ depth ih => simp only [tree, join, Task.spawn, Array.size_zipWith, ih, Nat.min_self]

theorem size_interpolateCosetPacked (logN : ℕ) (ω s : Field) (width : ℕ) (evals : ByteArray)
    (z : Ext4) (logTasks : ℕ) :
    (interpolateCosetPacked logN ω s width evals z logTasks).size = width := by
  unfold interpolateCosetPacked
  split
  · rw [Array.size_map, size_tree]
  · exact size_interpolateCoset _ _ _ _ _ _

/-- If column `j` of the words holds the values of `pⱼ`, of degree below `n`, on the coset
`s · ⟨ω⟩`, and `z` lies outside the coset, then output `j` is `pⱼ(z)`. -/
theorem toSpec_interpolateCosetPacked (D : CPolynomial.NTT.Domain KoalaBear.Field) (ω s : Field)
    (hω : FastField.toField ω = D.omega) (hs : FastField.toField s ≠ 0) (width : ℕ)
    (evals : ByteArray) (z : Ext4) (logTasks : ℕ)
    (hz : Ext4.toSpec z ^ D.n ≠
      algebraMap KoalaBear.Field KoalaBear.Ext4 (FastField.toField s) ^ D.n)
    (p : Fin width → KoalaBear.Field[X]) (hp : ∀ j, (p j).degree < D.n)
    (hevals : ∀ (i : D.Idx) (j : Fin width),
      FastField.toField ((decodeWords evals).getD (i * width + j) 0) =
        (p j).eval (FastField.toField s * D.node i))
    (j : Fin width) :
    Ext4.toSpec ((interpolateCosetPacked D.logN ω s width evals z logTasks)[j.val]'(by
      rw [size_interpolateCosetPacked]; exact j.isLt)) =
      Polynomial.aeval (Ext4.toSpec z) (p j) := by
  simp only [interpolateCosetPacked_eq D.logN ω s width evals z logTasks
    (toSpec_ne_specNode D ω s hω z hz)]
  exact toSpec_interpolateCoset D ω s hω hs width _ z hz p hp hevals j

end KoalaBear.Fast
