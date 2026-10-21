/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregor Mitscha-Baude
-/
module

import all CompPoly.Univariate.NTTFast.Plan
import all CompPoly.Univariate.NTTFast.Packed.Native
public import CompPoly.Univariate.NTTFast.Packed.FieldStorage
public import CompPoly.Univariate.NTTFast.Packed.ButterflyLemmas
public import CompPoly.Univariate.NTTFast.Packed.Rows
public import CompPoly.Univariate.NTTFast.Packed.Arrays

/-! # Refinement of the packed radix-two loop

`Native.pairs` runs `Plan.butterflyDIFInner` on packed words: sixteen-butterfly batches with
`pair16`, then the scalar `pairInner`.
-/

@[expose] public section
namespace CompPoly.CPolynomial.NTTFast.Packed
open Montgomery.Native32 (Mont32Field FastField)

variable {p : ℕ} [Mont32Field p]

open CompPoly.PackedRepr (encode)

local notation "F" => FastField p

/-- One step of the inner DIF loop. -/
theorem butterflyDIFInner_succ [Field R] (tw : Array R) (limit j i0 i1 : Nat) (a : Array R)
    (h : j < limit) :
    Plan.butterflyDIFInner tw limit j i0 i1 a =
      Plan.butterflyDIFInner tw limit (j + 1) (i0 + 1) (i1 + 1)
        ((a.set! i0 (a.getD i0 0 + a.getD i1 0)).set! i1
          (tw.getD j 0 * (a.getD i0 0 - a.getD i1 0))) := by
  rw [Plan.butterflyDIFInner]
  simp only [h, ↓reduceIte]

/-- An inner DIF loop runs its first `k` butterflies, then the rest. -/
theorem butterflyDIFInner_split [Field R] (tw : Array R) (limit : Nat) :
    ∀ (k j i0 i1 : Nat) (a : Array R), j + k ≤ limit →
      Plan.butterflyDIFInner tw limit j i0 i1 a =
        Plan.butterflyDIFInner tw limit (j + k) (i0 + k) (i1 + k)
          (Plan.butterflyDIFInner tw (j + k) j i0 i1 a) := by
  intro k
  induction k with
  | zero =>
    intro j i0 i1 a _
    have hz : Plan.butterflyDIFInner tw j j i0 i1 a = a := by
      rw [Plan.butterflyDIFInner]
      simp only [Nat.lt_irrefl, ↓reduceIte]
    simp only [Nat.add_zero, hz]
  | succ k ih =>
    intro j i0 i1 a hk
    rw [butterflyDIFInner_succ tw limit j i0 i1 a (by omega),
      butterflyDIFInner_succ tw (j + (k + 1)) j i0 i1 a (by omega),
      ih (j + 1) (i0 + 1) (i1 + 1) _ (by omega)]
    simp only [show ∀ x, x + 1 + k = x + (k + 1) from fun x ↦ by omega]

/-- The field-array semantics of sixteen radix-two butterflies. -/
def pair16Field (w : Array F) (j i0 i1 : Nat) (a : Array F) : Array F :=
  splice (splice a i0 (lit16 fun t ↦ a.getD (i0 + t) 0 + a.getD (i1 + t) 0)) i1
    (lit16 fun t ↦ w.getD (j + t) 0 * (a.getD (i0 + t) 0 - a.getD (i1 + t) 0))

/-- The radix-two word kernel is its field-array semantics. -/
theorem Native.pair16_encode (w a : Array F) (j i0 i1 : USize) (h) :
    Native.pair16 p (encode w) j i0 i1 (encode a) h =
      encode (pair16Field w j.toNat i0.toNat i1.toNat a) := by
  obtain ⟨h0, h1, -, hs, -⟩ := h
  rw [size_encode_fields] at h0 h1
  unfold Native.pair16
  simp only [Native.readUOffset_encode, add_val, sub_val, mul_val]
  rw [Native.write16U_encode _ _ hs (by omega), Native.write16U_encode _ _ (by
    rw [size_encode_fields, size_splice16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    rwa [size_encode_fields] at hs) (by
      rw [size_splice16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]; omega)]
  simp only [USize.reduceToNat, Nat.add_zero]
  rfl

/-- Sixteen disjoint radix-two butterflies are sixteen steps of the inner DIF loop. -/
theorem pair16Field_eq (w a : Array F) (j i0 i1 : Nat) (h01 : i0 + 16 ≤ i1)
    (hs : i1 + 16 ≤ a.size) :
    pair16Field w j i0 i1 a = Plan.butterflyDIFInner w (j + 16) j i0 i1 a := by
  have hs1 : i0 + (lit16 fun t ↦ a.getD (i0 + t) 0 + a.getD (i1 + t) 0).size ≤ a.size := by
    rw [size_lit16]; omega
  have hsz : (splice a i0 (lit16 fun t ↦ a.getD (i0 + t) 0 + a.getD (i1 + t) 0)).size =
      a.size := size_splice _ _ _ hs1
  have he : j + 16 - j = 16 := by omega
  apply array_eq_of_getD _ _ 0 (by
    rw [pair16Field, size_splice _ _ _ (by rw [size_lit16, hsz]; omega), hsz,
      Plan.size_butterflyDIFInner])
  intro k
  unfold pair16Field
  rw [getD_splice _ _ _ (by rw [size_lit16, hsz]; omega), getD_splice _ _ _ hs1, size_lit16,
    size_lit16]
  by_cases hk1 : i1 ≤ k ∧ k < i1 + 16
  · simp only [show ¬k < i1 by omega, show k < i1 + 16 by omega, ↓reduceIte]
    rw [getD_lit16 _ _ (by omega),
      getD_butterflyDIFInner_right _ _ _ _ _ _ (by omega) (by omega) _ (by rw [he]; omega),
      show i1 + (k - i1) = k by omega]
  · by_cases hk0 : i0 ≤ k ∧ k < i0 + 16
    · simp only [show k < i1 by omega, show ¬k < i0 by omega, show k < i0 + 16 by omega,
        ↓reduceIte]
      rw [getD_lit16 _ _ (by omega),
        getD_butterflyDIFInner_left _ _ _ _ _ _ (by omega) (by omega) _ (by rw [he]; omega),
        show i0 + (k - i0) = k by omega]
    · rw [getD_butterflyDIFInner_outside _ _ _ _ _ _ (by omega) (by omega) _ (by rw [he]; omega)
        (by rw [he]; omega)]
      by_cases hlt : k < i1
      · by_cases hlt0 : k < i0
        · simp only [hlt, hlt0, ↓reduceIte]
        · simp only [hlt, hlt0, show ¬k < i0 + 16 by omega, ↓reduceIte]
      · simp only [hlt, show ¬k < i1 + 16 by omega, show ¬k < i0 by omega,
          show ¬k < i0 + 16 by omega, ↓reduceIte]

/-- The hoisted batch loop depends only on the buffer's value. -/
theorem Native.pair16Loop_congr {w : ByteArray} {n : Nat} {j i0 i1 : USize} {b b' : ByteArray}
    (h) (e : b = b') :
    Native.pair16Loop p w n j i0 i1 b h = Native.pair16Loop p w n j i0 i1 b' (e ▸ h) := by
  subst e
  rfl

/-- The batch loop runs `16 * n` butterflies of the inner DIF loop. -/
theorem Native.pair16Loop_encode (w : Array F) :
    ∀ (n : Nat) (j i0 i1 : USize) (a : Array F) (h), i0.toNat + 16 * n ≤ i1.toNat →
      i1.toNat + 16 * n ≤ a.size →
      Native.pair16Loop p (encode w) n j i0 i1 (encode a) h =
        encode (Plan.butterflyDIFInner w (j.toNat + 16 * n) j.toNat i0.toNat i1.toNat a) := by
  intro n
  induction n with
  | zero =>
    intro j i0 i1 a h _ _
    rw [Native.pair16Loop, Nat.mul_zero, Nat.add_zero, Plan.butterflyDIFInner]
    simp only [Nat.lt_irrefl, ↓reduceIte]
  | succ n ih =>
    intro j i0 i1 a h h01 hs
    have hb := h.2.2.2.1
    have hw := h.2.2.2.2
    rw [Native.pair16Loop, Native.pair16Loop_congr _ ((Native.pair16_encode w a j i0 i1 _).trans
      (by rw [pair16Field_eq w a _ _ _ (by omega) (by omega)]))]
    rw [ih _ _ _ _ _ (by rw [usize_add16 i0 _ (by omega) hb, usize_add16 i1 _ (by omega) hb]; omega)
      (by rw [usize_add16 i1 _ (by omega) hb, Plan.size_butterflyDIFInner]; omega),
      usize_add16 j _ (by omega) hw, usize_add16 i0 _ (by omega) hb,
      usize_add16 i1 _ (by omega) hb,
      butterflyDIFInner_split w (j.toNat + 16 * (n + 1)) 16 j.toNat i0.toNat i1.toNat a (by omega),
      show j.toNat + 16 + 16 * n = j.toNat + 16 * (n + 1) by omega]

/-- The scalar radix-two loop agrees with the ordinary inner DIF loop. -/
theorem Native.pairInner_encode (w a : Array F) (q j i0 i1 : Nat)
    (ha : (encode a).size < USize.size) (hw : (encode w).size < USize.size) (hwi : q ≤ w.size)
    (hi : i0 + (q - j) ≤ a.size ∧ i1 + (q - j) ≤ a.size) :
    Native.pairInner p (encode w) q j i0 i1 (encode a) =
      encode (Plan.butterflyDIFInner w q j i0 i1 a) := by
  rw [Native.pairInner, Plan.butterflyDIFInner]
  split
  · rename_i hj
    simp (config := { maxDischargeDepth := 8 })
      (disch := (simp_all only [Array.size_setIfInBounds, size_encode_fields] <;> omega)) only
      [Native.read_encode, add_val, sub_val, mul_val, Native.write_encode,
        Array.set!_eq_setIfInBounds]
    exact Native.pairInner_encode w _ q (j + 1) (i0 + 1) (i1 + 1)
      (by simpa only [size_encode_fields, Array.size_setIfInBounds] using ha) hw hwi
      (by simp only [Array.size_setIfInBounds]; omega)
  · rfl
termination_by q - j
decreasing_by omega

/-- The packed radix-two loop agrees with the ordinary inner DIF loop. -/
theorem Native.pairs_encode (w a : Array F) (q j i0 i1 : Nat)
    (ha : (encode a).size < USize.size) (hw : (encode w).size < USize.size) (hwi : q ≤ w.size)
    (hj : j ≤ q) (hs : i1 + (q - j) ≤ a.size) (h01 : i0 + (q - j) ≤ i1) :
    Native.pairs p (encode w) q j i0 i1 (encode a) =
      encode (Plan.butterflyDIFInner w q j i0 i1 a) := by
  have hn : 16 * ((q - j) / 16) ≤ q - j := Nat.mul_div_le _ _
  rw [Native.pairs]
  split
  · rw [Native.pair16Loop_encode w _ _ _ _ a _ (by simp only [USize.toNat_ofNatLT]; omega)
      (by simp only [USize.toNat_ofNatLT]; omega)]
    simp only [USize.toNat_ofNatLT]
    rw [Native.pairInner_encode w _ q _ _ _ (by
        rwa [size_encode_fields, Plan.size_butterflyDIFInner, ← size_encode_fields]) hw hwi
        (by rw [Plan.size_butterflyDIFInner]; omega),
      ← butterflyDIFInner_split w q _ j i0 i1 a (by omega)]
  · exact Native.pairInner_encode w a q j i0 i1 ha hw hwi (by omega)

end CompPoly.CPolynomial.NTTFast.Packed
