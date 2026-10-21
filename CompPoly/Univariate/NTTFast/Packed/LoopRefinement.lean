/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.KernelRefinement
public import CompPoly.Univariate.NTTFast.Packed.BatchCorrectness
public import CompPoly.Univariate.NTTFast.Packed.KernelSpecialization

/-! # Packed scalar loop refinement -/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode)

/-- The packed scalar radix-four tail agrees with the ordinary field-array loop. -/
theorem Native.inner_encode (th tl : Array (FastField p)) (q j i0 i1 i2 i3 : Nat)
    (a : Array (FastField p))
    (ha : (encode a).size < USize.size)
    (hth : (encode th).size < USize.size) (htl : (encode tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size)
    (hi : i0 + (q - j) ≤ a.size ∧ i1 + (q - j) ≤ a.size ∧
      i2 + (q - j) ≤ a.size ∧ i3 + (q - j) ≤ a.size) :
    Native.inner p (encode th) (encode tl) q j i0 i1 i2 i3 (encode a) =
      encode (Plan.butterflyDIFRadix4Inner th tl q j i0 i1 i2 i3 a) := by
  rw [Native.inner, Plan.butterflyDIFRadix4Inner]
  split
  · rename_i hj
    simp (config := { maxDischargeDepth := 8 })
      (disch := (simp_all only [Array.size_setIfInBounds, size_encode_fields] <;> omega)) only
      [Native.read_encode, add_val, sub_val, mul_val, Native.write_encode]
    exact Native.inner_encode th tl q (j + 1) (i0 + 1) (i1 + 1) (i2 + 1) (i3 + 1) _
      (by simpa only [size_encode_fields, Array.size_setIfInBounds] using ha)
      hth htl hthi htli (by simp only [Array.size_setIfInBounds]; omega)
  · rfl
termination_by q - j
decreasing_by omega


/-- The hoisted batch loop depends only on the buffer's value. -/
theorem Native.inner16Loop_congr {th tl : ByteArray} {n : Nat} {j j1 i0 i1 i2 i3 : USize}
    {b b' : ByteArray} (h) (e : b = b') :
    Native.inner16Loop p th tl n j j1 i0 i1 i2 i3 b h =
      Native.inner16Loop p th tl n j j1 i0 i1 i2 i3 b' (e ▸ h) := by
  subst e
  rfl

/-- The hoisted batch loop executes `16 * n` cells. -/
theorem Native.inner16Loop_encode (th tl : Array (FastField p)) (q : Nat) :
    ∀ (n : Nat) (j j1 i0 i1 i2 i3 : USize) (a : Array (FastField p)) (h),
    j1.toNat = j.toNat + q → i3.toNat + 16 * n ≤ a.size → i0.toNat + 16 * n ≤ i1.toNat →
    i1.toNat + 16 * n ≤ i2.toNat → i2.toNat + 16 * n ≤ i3.toNat →
    Native.inner16Loop p (encode th) (encode tl) n j j1 i0 i1 i2 i3 (encode a) h =
      encode (quadCells th tl q j.toNat i0.toNat i1.toNat i2.toNat i3.toNat a (16 * n)) := by
  intro n
  induction n with
  | zero => intro j j1 i0 i1 i2 i3 a h _ _ _ _ _; simp only [Native.inner16Loop, quadCells]
  | succ n ih =>
    intro j j1 i0 i1 i2 i3 a h hj1 hs h01 h12 h23
    have hb := h.2.2.2.2.2.2.2.1
    have ht := h.2.2.2.2.2.2.2.2.1
    rw [Native.inner16Loop, Native.inner16Loop_congr _ ((Native.step16_encode th tl
      j j1 i0 i1 i2 i3 a _).trans (by
        rw [step16Field_eq_expression, Expressions.step16Field_eq_quadCells th tl q j j1 i0 i1 i2
          i3 a hj1 (by omega) (by omega) (by omega) (by omega)]))]
    rw [ih _ _ _ _ _ _ _ _ (by
        rw [usize_add16 j _ (by omega) ht, usize_add16 j1 _ (by omega) ht, hj1]
        omega)
      (by rw [usize_add16 i3 _ (by omega) hb, size_quadCells]; omega)
      (by rw [usize_add16 i0 _ (by omega) hb, usize_add16 i1 _ (by omega) hb]; omega)
      (by rw [usize_add16 i1 _ (by omega) hb, usize_add16 i2 _ (by omega) hb]; omega)
      (by rw [usize_add16 i2 _ (by omega) hb, usize_add16 i3 _ (by omega) hb]; omega)]
    rw [usize_add16 j _ (by omega) ht, usize_add16 i0 _ (by omega) hb,
      usize_add16 i1 _ (by omega) hb, usize_add16 i2 _ (by omega) hb,
      usize_add16 i3 _ (by omega) hb, ← quadCells_add, Nat.mul_succ, Nat.add_comm (16 * n)]

/-- Batched dispatch and the scalar tail together execute the ordinary inner loop. -/
theorem Native.inner16_encode (th tl : Array (FastField p)) (q j i0 i1 i2 i3 : Nat)
    (a : Array (FastField p))
    (ha : (encode a).size < USize.size)
    (hth : (encode th).size < USize.size) (htl : (encode tl).size < USize.size)
    (hthi : 2 * q ≤ th.size) (htli : q ≤ tl.size)
    (hs : i3 + (q - j) ≤ a.size) (h01 : i0 + (q - j) ≤ i1)
    (h12 : i1 + (q - j) ≤ i2) (h23 : i2 + (q - j) ≤ i3) :
    Native.inner16 p (encode th) (encode tl) q j i0 i1 i2 i3 (encode a) =
      encode (Plan.butterflyDIFRadix4Inner th tl q j i0 i1 i2 i3 a) := by
  have hn : 16 * ((q - j) / 16) ≤ q - j := Nat.mul_div_le _ _
  rw [Native.inner16]
  split
  · rename_i h
    rw [Native.inner16Loop_encode th tl q _ _ _ _ _ _ _ a _ (by simp only [USize.toNat_ofNatLT])
      (by simp only [USize.toNat_ofNatLT]; omega) (by simp only [USize.toNat_ofNatLT]; omega)
      (by simp only [USize.toNat_ofNatLT]; omega) (by simp only [USize.toNat_ofNatLT]; omega)]
    simp only [USize.toNat_ofNatLT]
    rw [Native.inner_encode th tl q _ _ _ _ _ _
      (by simpa only [size_encode_fields, size_quadCells] using ha) hth htl hthi htli
      (by simp only [size_quadCells]; omega)]
    rw [butterflyDIFRadix4Inner_eq_quadCells, butterflyDIFRadix4Inner_eq_quadCells,
      ← quadCells_add]
    have he : 16 * ((q - j) / 16) + (q - (j + 16 * ((q - j) / 16))) = q - j := by omega
    rw [he]
  · exact Native.inner_encode th tl q j i0 i1 i2 i3 a ha hth htl hthi htli (by omega)

end CompPoly.CPolynomial.NTTFast.Packed
